// @filename: a.ts
// somebody forgot that `alert` doesn't return anything
const response = alert('Are you sure?');
console.log(alert('Are you sure?'));

// it's not obvious whether the chained promise will contain the response (fixable)
promise.then(value => window.postMessage(value));

// it looks like we are returning the result of `console.error` (fixable)
function doSomething() {
  if (!somethingToDo) {
    return console.error('Nothing to do!');
  }

  console.log('Doing a thing...');
}

// @filename: b.ts
// just a regular void function in a statement position
alert('Hello, world!');

// this function returns a boolean value so it's ok
const response = confirm('Are you sure?');
console.log(confirm('Are you sure?'));

// now it's obvious that `postMessage` doesn't return any response
promise.then(value => {
  window.postMessage(value);
});

// now it's explicit that we want to log the error and return early
function doSomething() {
  if (!somethingToDo) {
    console.error('Nothing to do!');
    return;
  }

  console.log('Doing a thing...');
}

// using logical expressions for their side effects is fine
cond && console.log('true');
cond || console.error('false');
cond ? console.log('true') : console.error('false');

// @filename: c.ts
promise.then(value => window.postMessage(value));

// @filename: d.ts
// now it's obvious that we don't expect any response
promise.then(value => void window.postMessage(value));

// now it's explicit that we don't want to return anything
function doSomething() {
  if (!somethingToDo) {
    return void console.error('Nothing to do!');
  }

  console.log('Doing a thing...');
}

// we are sure that we want to always log `undefined`
console.log(void alert('Hello, world!'));

// @filename: e.ts
function foo(): void {
  return console.log();
}

function onError(callback: () => void): void {
  callback();
}

onError(() => console.log('oops'));