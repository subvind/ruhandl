const { InteractionScript } = require('./language.js');

// Create a new runtime
const runtime = new InteractionScript();

// Example program
const program = `
  // Define a simple function
  function double(x) {
    return x + x;
  }

  // Use Church numerals
  const three = n => f => x => f(f(f(x)));
  double(three)
`;

// Evaluate the program
runtime.evaluate(program).then(result => {
  console.log('Result:', result);
  console.log('Statistics:', result.statistics);
});