function* g1() {
  yield 1
  yield "foo"
}

function* g2() {
  return "bar"
}

function* g3() {
  yield "foo"
}

async function* g4() {
  if (Math.random() > 0.5) {
    return "bar"
  }
  yield "foo"
}

async function* g5() {
  yield "foo"
  await new Promise(resolve => setTimeout(resolve, 1000))
  yield 1
  await new Promise(resolve => setTimeout(resolve, 1000))
  yield 3
  return "bar"
}


async function* g6() {
  yield "foo"
  await new Promise(resolve => setTimeout(resolve, 1000))
  yield 1
  try {
    yield 2
  } catch (e) {
    console.error(e)
    return "err"
  }
  yield 3
  return "bar"
}