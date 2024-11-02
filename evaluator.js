const { Worker, isMainThread, parentPort, workerData } = require('worker_threads');
const os = require('os');

// Constants for term tags
const Tags = {
  VAR: 0n, // Positive variable
  SUB: 1n, // Negative variable
  NUL: 2n, // Positive eraser
  ERA: 3n, // Negative eraser
  LAM: 4n, // Positive constructor (lambda)
  APP: 5n, // Negative constructor (application)
  SUP: 6n, // Positive duplicator
  DUP: 7n, // Negative duplicator
};

class Net {
  constructor() {
    // Using BigInt64Array for 64-bit integers
    this.terms = new SharedArrayBuffer(1024 * 1024 * 8); // 8MB initial size
    this.termsView = new BigInt64Array(this.terms);
    this.nextLoc = 0;
    this.redexQueue = [];
    this.statistics = {
      betaReductions: 0,
      duplications: 0,
      erasures: 0,
      annihilations: 0
    };
  }

  // Allocates space for a new node with given number of ports
  alloc(ports) {
    const loc = this.nextLoc;
    this.nextLoc += ports;
    return BigInt(loc);
  }

  toBigInt(value) {
    return typeof value === 'bigint' ? value : BigInt(value);
  }

  // Fixed atomic swap operation for BigInt
  swap(loc, newValue) {
    let packedValue;
    if (typeof newValue === 'bigint') {
      packedValue = newValue;
    } else if (Array.isArray(newValue)) {
      packedValue = this.packTerm(newValue);
    } else {
      throw new Error('Invalid value type for swap');
    }
    
    const oldValue = Atomics.compareExchange(
      this.termsView,
      Number(loc),
      this.termsView[Number(loc)],
      packedValue
    );
    return this.unpackTerm(oldValue);
  }

  // Sets a value at location
  set(loc, term) {
    const packed = this.packTerm(term);
    this.termsView[Number(loc)] = packed;
  }

  // Gets a term at location
  get(loc) {
    return this.unpackTerm(this.termsView[Number(loc)]);
  }

  // Visualization methods
  visualize() {
    let dot = 'digraph G {\n';
    const visited = new Set();

    const visualizeNode = (loc) => {
      if (visited.has(loc)) return;
      visited.add(loc);

      const [tag, target] = this.get(loc);
      const nodeLabel = this.getTagName(tag);
      
      dot += `  node${loc} [label="${nodeLabel}"];\n`;
      
      // Add edges for ports
      if (tag !== Tags.VAR && tag !== Tags.SUB) {
        for (let i = 1; i <= this.getPortCount(tag); i++) {
          const portLoc = loc + i;
          const [portTag, portTarget] = this.get(portLoc);
          dot += `  node${loc} -> node${portTarget} [label="port${i}"];\n`;
          visualizeNode(portTarget);
        }
      }
    };

    // Start visualization from root
    visualizeNode(0);
    dot += '}\n';
    return dot;
  }

  // Construction methods
  createLam(variable, body) {
    const lamLoc = this.alloc(3);
    this.set(lamLoc, [Tags.LAM, lamLoc]);
    this.set(lamLoc + 1n, [Tags.SUB, variable]);
    this.set(lamLoc + 2n, [Tags.VAR, body]);
    return lamLoc;
  }

  createApp(arg, ret) {
    const appLoc = this.alloc(3);
    this.set(appLoc, [Tags.APP, appLoc]);
    this.set(appLoc + 1n, [Tags.VAR, arg]);
    this.set(appLoc + 2n, [Tags.SUB, ret]);
    return appLoc;
  }

  createDup(port1, port2) {
    const dupLoc = this.alloc(3);
    this.set(dupLoc, [Tags.DUP, dupLoc]);
    this.set(dupLoc + 1, [Tags.SUB, port1]);
    this.set(dupLoc + 2, [Tags.SUB, port2]);
    return dupLoc;
  }

  createSup(port1, port2) {
    const supLoc = this.alloc(3);
    this.set(supLoc, [Tags.SUP, supLoc]);
    this.set(supLoc + 1, [Tags.VAR, port1]);
    this.set(supLoc + 2, [Tags.VAR, port2]);
    return supLoc;
  }

  // Core evaluation methods (enhanced)
  move(negLoc, posTerm) {
    const maxRecursionDepth = 1000; // Prevent infinite recursion
    return this._moveWithDepth(negLoc, posTerm, 0, maxRecursionDepth);
  }

  _moveWithDepth(negLoc, posTerm, depth, maxDepth) {
    if (depth >= maxDepth) {
      throw new Error('Maximum recursion depth exceeded in move operation');
    }

    const packed = this.packTerm(posTerm);
    const neg = this.swap(this.toBigInt(negLoc), packed);
    
    if (neg[0] !== Tags.SUB) {
      return this._linkWithDepth(neg, posTerm, depth + 1, maxDepth);
    }
  }

  link(neg, pos) {
    const maxRecursionDepth = 1000;
    return this._linkWithDepth(neg, pos, 0, maxRecursionDepth);
  }

  _linkWithDepth(neg, pos, depth, maxDepth) {
    if (depth >= maxDepth) {
      throw new Error('Maximum recursion depth exceeded in link operation');
    }

    const [negTag, negTarget] = neg;
    const [posTag, posTarget] = pos;

    if (posTag === Tags.VAR) {
      const negVar = this.swap(posTarget, this.packTerm(neg));
      if (negVar[0] !== Tags.SUB) {
        return this._moveWithDepth(posTarget, negVar, depth + 1, maxDepth);
      }
    } else {
      this.pushRedex(neg, pos);
    }
  }

  applam(negLoc, posLoc) {
    const argLoc = this.toBigInt(negLoc) + 1n;
    const retLoc = this.toBigInt(negLoc) + 2n;
    const varLoc = this.toBigInt(posLoc) + 1n;
    const bodLoc = this.toBigInt(posLoc) + 2n;

    const argVal = this.swap(argLoc, 0n);
    const bodVal = this.swap(bodLoc, 0n);

    this.move(varLoc, argVal);
    this.move(retLoc, bodVal);
    this.statistics.betaReductions++;
  }


  duplam(negLoc, posLoc) {
    const dp1Loc = negLoc + 1;
    const dp2Loc = negLoc + 2;
    const varLoc = posLoc + 1;
    const bodLoc = posLoc + 2;

    const bodVal = this.unpackTerm(this.swap(bodLoc, 0n));

    const co1Loc = this.alloc(3);
    const co2Loc = this.alloc(3);
    const du1Loc = this.alloc(3);
    const du2Loc = this.alloc(3);

    this.set(co1Loc + 1, [Tags.SUB, co1Loc + 1]);
    this.set(co1Loc + 2, [Tags.VAR, du2Loc + 1]);
    this.set(co2Loc + 1, [Tags.SUB, co2Loc + 1]);
    this.set(co2Loc + 2, [Tags.VAR, du2Loc + 2]);
    this.set(du1Loc + 1, [Tags.VAR, co1Loc + 1]);
    this.set(du1Loc + 2, [Tags.VAR, co2Loc + 1]);
    this.set(du2_loc + 1, [Tags.SUB, du2Loc + 1]);
    this.set(du2_loc + 2, [Tags.SUB, du2Loc + 2]);

    this.move(dp1Loc, [Tags.LAM, co1Loc]);
    this.move(dp2Loc, [Tags.LAM, co2Loc]);
    this.move(varLoc, [Tags.SUP, du1Loc]);
    this.link([Tags.DUP, du2Loc], bodVal);
    this.statistics.duplications++;
  }

  // New interaction rules
  eraLam(negLoc, posLoc) {
    const varLoc = posLoc + 1;
    const bodLoc = posLoc + 2;

    this.move(varLoc, [Tags.NUL, 0n]);
    const bodVal = this.unpackTerm(this.swap(bodLoc, 0n));
    this.erase(bodVal);
    this.statistics.erasures++;
  }

  eraSup(negLoc, posLoc) {
    const tm1Loc = posLoc + 1;
    const tm2Loc = posLoc + 2;

    const tm1Val = this.unpackTerm(this.swap(tm1Loc, 0n));
    const tm2Val = this.unpackTerm(this.swap(tm2Loc, 0n));
    
    this.erase(tm1Val);
    this.erase(tm2Val);
    this.statistics.erasures++;
  }

  annihilate(negLoc, posLoc) {
    // Handle annihilation of opposing eraser nodes
    this.statistics.annihilations++;
  }

  // Utility methods

  // Enhanced packing/unpacking methods
  packTerm([tag, target]) {
    // Handle null/undefined values
    if (tag == null || target == null) {
      throw new Error('Invalid term: tag or target is null/undefined');
    }

    // Ensure values are within valid ranges
    const tagBig = this.toBigInt(tag);
    const targetBig = this.toBigInt(target);

    // Validate tag range (8 bits)
    if (tagBig < 0n || tagBig > 255n) {
      throw new Error(`Invalid tag value: ${tagBig}`);
    }

    // Validate target range (56 bits)
    const maxTarget = (1n << 56n) - 1n;
    if (targetBig < 0n || targetBig > maxTarget) {
      throw new Error(`Invalid target value: ${targetBig}`);
    }

    return (tagBig << 56n) | (targetBig & ((1n << 56n) - 1n));
  }

  unpackTerm(packed) {
    if (typeof packed !== 'bigint') {
      throw new Error(`Invalid packed term: ${packed}`);
    }

    const tag = packed >> 56n;
    const target = packed & ((1n << 56n) - 1n);

    // Validate unpacked values
    if (tag < 0n || tag > 255n) {
      throw new Error(`Invalid unpacked tag: ${tag}`);
    }

    return [tag, target];
  }

  getTagName(tag) {
    return Object.entries(Tags).find(([_, v]) => v === tag)?.[0] || 'UNKNOWN';
  }

  getPortCount(tag) {
    const tagBig = this.toBigInt(tag);
    switch(tagBig) {
      case Tags.VAR:
      case Tags.SUB:
      case Tags.NUL:
      case Tags.ERA:
        return 0n;
      case Tags.LAM:
      case Tags.APP:
      case Tags.SUP:
      case Tags.DUP:
        return 2n;
      default:
        return 0n;
    }
  }

  erase(term) {
    const [tag, loc] = term;
    if (tag === Tags.VAR || tag === Tags.SUB) {
      return;
    }
    
    for (let i = 1; i <= this.getPortCount(tag); i++) {
      const portVal = this.unpackTerm(this.swap(loc + i, 0n));
      this.erase(portVal);
    }
  }

  pushRedex(neg, pos) {
    if (!Array.isArray(neg) || !Array.isArray(pos)) {
      throw new Error('Invalid redex: neg and pos must be arrays');
    }
    if (neg.length !== 2 || pos.length !== 2) {
      throw new Error('Invalid redex: neg and pos must have length 2');
    }
    this.redexQueue.push([neg, pos]);
  }

  evaluate() {
    while (this.redexQueue.length > 0) {
      const [neg, pos] = this.redexQueue.pop();
      const [negTag, negLoc] = neg;
      const [posTag, posLoc] = pos;

      switch(true) {
        case negTag === Tags.APP && posTag === Tags.LAM:
          this.applam(negLoc, posLoc);
          break;
        case negTag === Tags.DUP && posTag === Tags.LAM:
          this.duplam(negLoc, posLoc);
          break;
        case negTag === Tags.ERA && posTag === Tags.LAM:
          this.eraLam(negLoc, posLoc);
          break;
        case negTag === Tags.ERA && posTag === Tags.SUP:
          this.eraSup(negLoc, posLoc);
          break;
        case (negTag === Tags.ERA && posTag === Tags.NUL) ||
             (negTag === Tags.DUP && posTag === Tags.SUP):
          this.annihilate(negLoc, posLoc);
          break;
      }
    }
  }

  getStatistics() {
    return { ...this.statistics };
  }

  createVar(varId) {
    const varLoc = this.alloc(1);
    this.set(varLoc, [Tags.VAR, varId]);
    return varLoc;
  }

  createSub(varId) {
    const subLoc = this.alloc(1);
    this.set(subLoc, [Tags.SUB, varId]);
    return subLoc;
  }

  // Helper method to count applications of a function
  applyAndCount(loc, callback) {
    let count = 0;
    const countLoc = this.alloc(1);
    
    // Create a special node that increments counter when reduced
    this.set(countLoc, [Tags.APP, () => {
      count++;
      if (callback) callback();
      return countLoc;
    }]);

    // Apply the church numeral to our counting function
    const resultLoc = this.createApp(countLoc, loc);
    this.evaluate();
    
    return count;
  }

  // Extended Church encoding support
  isChurchBoolean(loc) {
    const [tag, target] = this.get(loc);
    if (tag !== Tags.LAM) return false;
    
    // Check for λx.λy.x or λx.λy.y pattern
    const [innerTag, innerTarget] = this.get(target + 2);
    return (
      innerTag === Tags.LAM &&
      this.get(innerTarget + 2)[0] === Tags.VAR
    );
  }

  churchToBoolean(loc) {
    // Apply church boolean to two distinct values and see which one it returns
    const trueLoc = this.alloc(1);
    const falseLoc = this.alloc(1);
    
    const testLoc = this.createApp(
      this.createApp(loc, trueLoc),
      falseLoc
    );
    
    this.evaluate();
    const [_, result] = this.get(testLoc);
    return result === trueLoc;
  }
}

if (isMainThread) {
  class ParallelEvaluator {
    constructor(numWorkers = os.cpus().length) {
      this.net = new Net();
      this.workers = [];
      this.numWorkers = numWorkers;
    }

    startWorkers() {
      for (let i = 0; i < this.numWorkers; i++) {
        const worker = new Worker(__filename, {
          workerData: {
            workerId: i,
            terms: this.net.terms
          }
        });

        worker.on('message', (message) => {
          if (message.type === 'done') {
            console.log(`Worker ${i} finished processing`);
          }
          if (message.type === 'statistics') {
            console.log(`Worker ${i} statistics:`, message.data);
          }
        });

        this.workers.push(worker);
      }
    }

    async evaluate() {
      this.startWorkers();
      
      await Promise.all(this.workers.map(worker => {
        return new Promise((resolve) => {
          worker.on('exit', resolve);
        });
      }));

      return this.net.getStatistics();
    }

    // Example: create Church numeral
    createChurchNumeral(n) {
      let current = this.net.createLam(0, 0); // λf.
      let innerLam = this.net.createLam(0, 0); // λx.
      
      let last = innerLam;
      for (let i = 0; i < n; i++) {
        const app = this.net.createApp(0, 0);
        this.net.move(last + 2, [Tags.VAR, app]);
        last = app;
      }
      
      this.net.move(innerLam + 2, [Tags.VAR, last]);
      this.net.move(current + 2, [Tags.VAR, innerLam]);
      
      return current;
    }

    // Generate DOT visualization
    visualize() {
      return this.net.visualize();
    }
  }

  module.exports = { ParallelEvaluator, Net, Tags };
} else {
  // Worker thread code
  const net = new Net();
  net.terms = workerData.terms;
  
  net.evaluate();
  
  parentPort.postMessage({ 
    type: 'statistics', 
    data: net.getStatistics() 
  });
  
  parentPort.postMessage({ type: 'done' });
}
