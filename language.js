const { Parser } = require('acorn');
const { ParallelEvaluator, Tags } = require('./evaluator.js'); // Previous artifact

// AST node types for our language
const NodeTypes = {
  LAMBDA: 'Lambda',
  APPLICATION: 'Application',
  VARIABLE: 'Variable',
  LET: 'Let',
  IF: 'If',
  NUMBER: 'Number',
  BOOLEAN: 'Boolean',
  BINARY_OP: 'BinaryOp',
  FUNCTION: 'Function'
};

class Compiler {
  constructor() {
    this.evaluator = new ParallelEvaluator();
    this.scope = new Map();
    this.nextVarId = 0;
  }

  // Main compilation entry point
  compile(sourceCode) {
    const ast = Parser.parse(sourceCode, {
      ecmaVersion: 2020,
      sourceType: 'module'
    });
    return this.compileNode(ast);
  }

  // Compile AST nodes to interaction combinators
  compileNode(node) {
    switch(node.type) {
      case 'Program':
        return this.compileProgram(node);
      case 'FunctionDeclaration':
        return this.compileFunctionDeclaration(node);
      case 'ArrowFunctionExpression':
        return this.compileLambda(node);
      case 'CallExpression':
        return this.compileApplication(node);
      case 'Identifier':
        return this.compileVariable(node);
      case 'VariableDeclaration':
        return this.compileVariableDeclaration(node);
      case 'IfStatement':
        return this.compileIf(node);
      case 'NumericLiteral':
        return this.compileNumber(node);
      case 'BooleanLiteral':
        return this.compileBoolean(node);
      case 'BinaryExpression':
        return this.compileBinaryOp(node);
      default:
        throw new Error(`Unsupported node type: ${node.type}`);
    }
  }

  compileProgram(node) {
    let lastResult = null;
    for (const statement of node.body) {
      lastResult = this.compileNode(statement);
    }
    return lastResult;
  }

  compileLambda(node) {
    const paramName = node.params[0].name;
    const varId = this.nextVarId++;
    this.scope.set(paramName, varId);
    
    const bodyLoc = this.compileNode(node.body);
    const lamLoc = this.evaluator.net.createLam(varId, bodyLoc);
    
    this.scope.delete(paramName);
    return lamLoc;
  }

  compileApplication(node) {
    const funcLoc = this.compileNode(node.callee);
    const argLoc = this.compileNode(node.arguments[0]);
    return this.evaluator.net.createApp(argLoc, funcLoc);
  }

  compileVariable(node) {
    const varId = this.scope.get(node.name);
    if (varId === undefined) {
      throw new Error(`Undefined variable: ${node.name}`);
    }
    return this.evaluator.net.createVar(varId);
  }

  // Church encoding for numbers
  compileNumber(node) {
    return this.evaluator.createChurchNumeral(node.value);
  }

  // Church encoding for booleans
  compileBoolean(node) {
    if (node.value) {
      // Church true: λx.λy.x
      const trueLoc = this.evaluator.net.createLam(0, 0);
      const innerLam = this.evaluator.net.createLam(0, 0);
      this.evaluator.net.move(trueLoc + 2, [Tags.VAR, innerLam]);
      this.evaluator.net.move(innerLam + 2, [Tags.VAR, trueLoc + 1]);
      return trueLoc;
    } else {
      // Church false: λx.λy.y
      const falseLoc = this.evaluator.net.createLam(0, 0);
      const innerLam = this.evaluator.net.createLam(0, 0);
      this.evaluator.net.move(falseLoc + 2, [Tags.VAR, innerLam]);
      this.evaluator.net.move(innerLam + 2, [Tags.VAR, innerLam + 1]);
      return falseLoc;
    }
  }

  compileBinaryOp(node) {
    const leftLoc = this.compileNode(node.left);
    const rightLoc = this.compileNode(node.right);
    
    switch(node.operator) {
      case '+':
        return this.compileAddition(leftLoc, rightLoc);
      case '*':
        return this.compileMultiplication(leftLoc, rightLoc);
      // Add more operators as needed
      default:
        throw new Error(`Unsupported operator: ${node.operator}`);
    }
  }

  // Church numeral addition
  compileAddition(aLoc, bLoc) {
    // (a + b) = λf.λx.a f (b f x)
    const outerLam = this.evaluator.net.createLam(0, 0); // λf.
    const innerLam = this.evaluator.net.createLam(0, 0); // λx.
    
    const app1 = this.evaluator.net.createApp(0, 0); // a f
    const app2 = this.evaluator.net.createApp(0, 0); // b f
    const app3 = this.evaluator.net.createApp(0, 0); // (b f x)
    
    // Wire everything up
    this.evaluator.net.move(outerLam + 2n, [Tags.VAR, innerLam]);
    this.evaluator.net.move(innerLam + 2n, [Tags.VAR, app1]);
    this.evaluator.net.move(app1 + 1n, [Tags.VAR, aLoc]);
    this.evaluator.net.move(app1 + 2n, [Tags.VAR, app2]);
    this.evaluator.net.move(app2 + 1n, [Tags.VAR, bLoc]);
    this.evaluator.net.move(app2 + 2n, [Tags.VAR, app3]);
    this.evaluator.net.move(app3 + 1n, [Tags.VAR, outerLam + 1n]);
    this.evaluator.net.move(app3 + 2n, [Tags.VAR, innerLam + 1n]);
    
    return outerLam;
  }

  // Church numeral multiplication
  compileMultiplication(aLoc, bLoc) {
    // (a * b) = λf.a (b f)
    const lamF = this.evaluator.net.createLam(0, 0); // λf.
    const app1 = this.evaluator.net.createApp(0, 0); // a (b f)
    const app2 = this.evaluator.net.createApp(0, 0); // b f
    
    this.evaluator.net.move(lamF + 2, [Tags.VAR, app1]);
    this.evaluator.net.move(app1 + 1, [Tags.VAR, aLoc]);
    this.evaluator.net.move(app1 + 2, [Tags.VAR, app2]);
    this.evaluator.net.move(app2 + 1, [Tags.VAR, bLoc]);
    this.evaluator.net.move(app2 + 2, [Tags.VAR, lamF + 1]);
    
    return lamF;
  }

  compileFunctionDeclaration(node) {
    const funcName = node.id.name;
    const paramName = node.params[0]?.name;
    
    // Create variable ID for the function
    const funcId = this.nextVarId++;
    this.scope.set(funcName, funcId);
    
    // Compile as lambda
    const paramId = this.nextVarId++;
    this.scope.set(paramName, paramId);
    
    const bodyLoc = this.compileNode(node.body.body[0].argument);
    const lamLoc = this.evaluator.net.createLam(paramId, bodyLoc);
    
    this.scope.delete(paramName);
    return lamLoc;
  }

  compileVariableDeclaration(node) {
    const declaration = node.declarations[0];
    const varName = declaration.id.name;
    const varId = this.nextVarId++;
    
    // Compile initializer
    const initLoc = this.compileNode(declaration.init);
    
    // Store in scope
    this.scope.set(varName, varId);
    
    // Create binding
    const bindingLoc = this.evaluator.net.createLam(varId, initLoc);
    return bindingLoc;
  }

  compileIf(node) {
    // Compile condition, then, and else expressions
    const condLoc = this.compileNode(node.test);
    const thenLoc = this.compileNode(node.consequent);
    const elseLoc = node.alternate ? 
      this.compileNode(node.alternate) :
      this.compileBoolean({ value: false }); // Default else
    
    // Create if-then-else using Church encoding
    // (if c t e) = c t e
    const app1 = this.evaluator.net.createApp(elseLoc, condLoc);
    const app2 = this.evaluator.net.createApp(thenLoc, app1);
    
    return app2;
  }
}

// InteractionScript runtime
class InteractionScript {
  constructor() {
    this.compiler = new Compiler();
  }

  // Evaluate source code
  async evaluate(sourceCode) {
    // Compile the source code to interaction combinators
    const rootLoc = this.compiler.compile(sourceCode);
    
    // Evaluate the network
    const stats = await this.compiler.evaluator.evaluate();
    
    // Convert result back to JavaScript value
    return this.extractResult(rootLoc, stats);
  }

  // Extract JavaScript values from Church encodings
  extractResult(loc, stats) {
    const net = this.compiler.evaluator.net;
    const [tag, target] = net.get(loc);
    
    // Try to detect if it's a Church numeral
    if (this.isChurchNumeral(loc)) {
      return this.churchToNumber(loc);
    }
    
    // Try to detect if it's a Church boolean
    if (this.isChurchBoolean(loc)) {
      return this.churchToBoolean(loc);
    }
    
    return {
      value: 'function',
      statistics: stats
    };
  }

  // Convert Church numeral back to JavaScript number
  churchToNumber(loc) {
    // Apply the Church numeral to a counter function
    let count = 0;
    const countFunc = () => { count++; };
    this.applyChurchNumeral(loc, countFunc);
    return count;
  }

  // Detect if a location contains a Church numeral
  isChurchNumeral(loc) {
    const net = this.compiler.evaluator.net;
    const [tag, target] = net.get(loc);
    return tag === Tags.LAM && this.hasChurchNumeralShape(loc);
  }

  // Helper to check Church numeral shape
  hasChurchNumeralShape(loc) {
    // Implementation to detect λf.λx.f^n x pattern
    // This is a simplified check - you'd want more thorough validation
    const net = this.compiler.evaluator.net;
    return true; // Simplified for brevity
  }

  // Test program
  static example() {
    const script = `
      // Define a function that adds two numbers
      function add(x, y) {
        return x + y;
      }

      // Use the function
      let result = add(3, 4);
      
      // Create a higher-order function
      const twice = f => x => f(f(x));
      
      // Use Church numerals
      const four = n => f => x => f(f(f(f(x))));
      const three = n => f => x => f(f(f(x)));
      
      // Multiply them
      four(three)
    `;

    const runtime = new InteractionScript();
    return runtime.evaluate(script);
  }
}

module.exports = { InteractionScript, Compiler };
