//! Runs a prebuilt test command with a deadline and captures hang diagnostics.

use std::{
    collections::{HashMap, HashSet},
    env,
    ffi::OsString,
    fs::{self, File},
    io::{self, BufRead, BufReader, Write},
    path::{Path, PathBuf},
    process::{Child, Command, ExitCode, ExitStatus, Stdio},
    sync::{Arc, Mutex},
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

#[cfg(unix)]
use std::os::unix::process::CommandExt;

struct Options {
    timeout: Duration,
    output_dir: Option<PathBuf>,
    conformance_timing: bool,
    command: Vec<OsString>,
}

#[derive(Clone)]
struct ProcessRow {
    pid: u32,
    ppid: u32,
    elapsed: String,
    state: String,
    command: String,
}

fn usage() -> &'static str {
    "usage: diagnose_hang [--timeout SECONDS] [--output-dir PATH] \
        [--conformance-timing] -- COMMAND [ARG ...]"
}

fn parse_options() -> Result<Options, String> {
    let mut args = env::args_os().skip(1).peekable();
    let mut timeout = Duration::from_secs(20);
    let mut output_dir = None;
    let mut conformance_timing = false;
    let mut command = Vec::new();

    while let Some(argument) = args.next() {
        match argument.to_str() {
            Some("--timeout") => {
                let value = args
                    .next()
                    .ok_or_else(|| "--timeout requires a value".to_string())?;
                let seconds = value
                    .to_str()
                    .ok_or_else(|| "--timeout must be valid UTF-8".to_string())?
                    .parse::<f64>()
                    .map_err(|_| "--timeout must be a number".to_string())?;
                if !seconds.is_finite() || seconds <= 0.0 {
                    return Err("--timeout must be greater than zero".to_string());
                }
                timeout = Duration::from_secs_f64(seconds);
            }
            Some("--output-dir") => {
                output_dir =
                    Some(PathBuf::from(args.next().ok_or_else(|| {
                        "--output-dir requires a value".to_string()
                    })?));
            }
            Some("--conformance-timing") => conformance_timing = true,
            Some("--") => {
                command.extend(args);
                break;
            }
            Some("--help" | "-h") => return Err(usage().to_string()),
            _ => {
                command.push(argument);
                command.extend(args);
                break;
            }
        }
    }

    if command.is_empty() {
        return Err(format!("missing command\n{}", usage()));
    }

    Ok(Options {
        timeout,
        output_dir,
        conformance_timing,
        command,
    })
}

fn default_output_dir() -> io::Result<PathBuf> {
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(io::Error::other)?
        .as_secs();
    Ok(PathBuf::from("target/hang-diagnostics").join(timestamp.to_string()))
}

fn process_rows() -> io::Result<Vec<ProcessRow>> {
    let output = Command::new("ps")
        .args(["-axo", "pid=,ppid=,etime=,state=,command="])
        .output()?;
    let text = String::from_utf8_lossy(&output.stdout);
    let mut rows = Vec::new();

    for line in text.lines() {
        let fields: Vec<_> = line.split_whitespace().collect();
        if fields.len() < 5 {
            continue;
        }
        let (Ok(pid), Ok(ppid)) = (fields[0].parse(), fields[1].parse()) else {
            continue;
        };
        rows.push(ProcessRow {
            pid,
            ppid,
            elapsed: fields[2].to_string(),
            state: fields[3].to_string(),
            command: fields[4..].join(" "),
        });
    }
    Ok(rows)
}

fn process_tree(root_pid: u32) -> io::Result<Vec<ProcessRow>> {
    let rows = process_rows()?;
    let mut selected = HashSet::from([root_pid]);
    loop {
        let previous_len = selected.len();
        for row in &rows {
            if selected.contains(&row.ppid) {
                selected.insert(row.pid);
            }
        }
        if selected.len() == previous_len {
            break;
        }
    }
    Ok(rows
        .into_iter()
        .filter(|row| selected.contains(&row.pid))
        .collect())
}

fn write_processes(rows: &[ProcessRow], destination: &Path) -> io::Result<()> {
    let mut output = File::create(destination)?;
    writeln!(output, "pid\tppid\telapsed\tstate\tcommand")?;
    for row in rows {
        writeln!(
            output,
            "{}\t{}\t{}\t{}\t{}",
            row.pid, row.ppid, row.elapsed, row.state, row.command
        )?;
    }
    Ok(())
}

fn sample_processes(rows: &[ProcessRow], output_dir: &Path) {
    if !cfg!(target_os = "macos") {
        return;
    }
    let parent_pids: HashSet<_> = rows.iter().map(|row| row.ppid).collect();
    let by_pid: HashMap<_, _> = rows.iter().map(|row| (row.pid, row)).collect();
    let mut pids: Vec<_> = by_pid.keys().copied().collect();
    pids.sort_by_key(|pid| parent_pids.contains(pid));

    for pid in pids {
        let destination = output_dir.join(format!("sample-{pid}.txt"));
        let _ = Command::new("sample")
            .arg(pid.to_string())
            .arg("1")
            .arg("-file")
            .arg(destination)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
    }
}

#[cfg(unix)]
fn signal_group(child: &Child, signal: &str) {
    let _ = Command::new("kill")
        .arg(signal)
        .arg(format!("-{}", child.id()))
        .status();
}

#[cfg(not(unix))]
fn signal_group(child: &Child, _signal: &str) {
    let _ = Command::new("taskkill")
        .args(["/T", "/F", "/PID", &child.id().to_string()])
        .status();
}

fn wait_for(child: &mut Child, duration: Duration) -> io::Result<Option<ExitStatus>> {
    let deadline = Instant::now() + duration;
    loop {
        if let Some(status) = child.try_wait()? {
            return Ok(Some(status));
        }
        if Instant::now() >= deadline {
            return Ok(None);
        }
        thread::sleep(Duration::from_millis(20));
    }
}

fn terminate_group(child: &mut Child) -> io::Result<ExitStatus> {
    for (signal, grace) in [("-INT", 2), ("-TERM", 1)] {
        signal_group(child, signal);
        if let Some(status) = wait_for(child, Duration::from_secs(grace))? {
            return Ok(status);
        }
    }
    signal_group(child, "-KILL");
    child.wait()
}

fn spawn_output_thread<R>(
    reader: R,
    log: Arc<Mutex<File>>,
    stderr: bool,
) -> thread::JoinHandle<io::Result<()>>
where
    R: io::Read + Send + 'static,
{
    thread::spawn(move || {
        for line in BufReader::new(reader).lines() {
            let line = line?;
            if stderr {
                eprintln!("{line}");
            } else {
                println!("{line}");
            }
            writeln!(log.lock().expect("output log mutex poisoned"), "{line}")?;
        }
        Ok(())
    })
}

fn write_metadata(
    output_dir: &Path,
    options: &Options,
    elapsed: Duration,
    timed_out: bool,
    status: ExitStatus,
) -> io::Result<()> {
    let command = options
        .command
        .iter()
        .map(|part| part.to_string_lossy())
        .collect::<Vec<_>>()
        .join(" ");
    fs::write(
        output_dir.join("metadata.txt"),
        format!(
            "command={command}\nelapsed_seconds={:.3}\ntimeout_seconds={:.3}\ntimed_out={timed_out}\nexit_code={:?}\n",
            elapsed.as_secs_f64(),
            options.timeout.as_secs_f64(),
            status.code(),
        ),
    )
}

fn run(options: Options) -> io::Result<u8> {
    let output_dir = options
        .output_dir
        .clone()
        .map_or_else(default_output_dir, Ok)?;
    fs::create_dir_all(&output_dir)?;

    println!("diagnostics: {}", output_dir.display());
    println!("deadline: {:.3}s", options.timeout.as_secs_f64());
    println!(
        "command: {}",
        options
            .command
            .iter()
            .map(|part| part.to_string_lossy())
            .collect::<Vec<_>>()
            .join(" ")
    );

    let mut command = Command::new(&options.command[0]);
    command
        .args(&options.command[1..])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if options.conformance_timing {
        command.env("OXC_CONFORMANCE_TIMING", "1");
    }
    #[cfg(unix)]
    command.process_group(0);

    let started = Instant::now();
    let mut child = command.spawn()?;
    let log = Arc::new(Mutex::new(File::create(output_dir.join("output.log"))?));
    let stdout_thread = spawn_output_thread(
        child.stdout.take().expect("piped stdout missing"),
        Arc::clone(&log),
        false,
    );
    let stderr_thread = spawn_output_thread(
        child.stderr.take().expect("piped stderr missing"),
        log,
        true,
    );

    let (timed_out, status) = match wait_for(&mut child, options.timeout)? {
        Some(status) => (false, status),
        None => {
            let rows = process_tree(child.id()).unwrap_or_default();
            write_processes(&rows, &output_dir.join("processes.tsv"))?;
            eprintln!("deadline exceeded; sampling {} process(es)", rows.len());
            sample_processes(&rows, &output_dir);
            (true, terminate_group(&mut child)?)
        }
    };

    stdout_thread.join().expect("stdout thread panicked")?;
    stderr_thread.join().expect("stderr thread panicked")?;
    let elapsed = started.elapsed();
    write_metadata(&output_dir, &options, elapsed, timed_out, status)?;

    if timed_out {
        eprintln!("hang diagnostics captured in {}", output_dir.display());
        Ok(124)
    } else {
        let code = status.code().unwrap_or(1).clamp(0, 255) as u8;
        println!(
            "completed in {:.3}s with exit code {code}",
            elapsed.as_secs_f64()
        );
        Ok(code)
    }
}

fn main() -> ExitCode {
    let options = match parse_options() {
        Ok(options) => options,
        Err(message) => {
            eprintln!("{message}");
            return ExitCode::from(2);
        }
    };
    match run(options) {
        Ok(code) => ExitCode::from(code),
        Err(error) => {
            eprintln!("diagnose_hang: {error}");
            ExitCode::FAILURE
        }
    }
}
