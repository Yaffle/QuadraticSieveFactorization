/*jshint esversion:6*/
import isPrime from './isPrime.js';

function modInverse(a, m) {
  a = BigInt(a);
  m = BigInt(m);
  if (a < 0n || a >= m || m <= 0n) {
    throw new RangeError();
  }
  // We use the extended Euclidean algorithm:
  let oldR = a;
  let r = m;
  let oldS = 1n;
  let s = 0n;
  while (r !== 0n) {
    const q = (oldR - oldR % r) / r; // floor(oldR / r)
    const newR = oldR - q * r;
    oldR = r;
    r = newR;
    const newS = oldS - q * s;
    oldS = s;
    s = newS;
  }
  if (oldR !== 1n) {
    return 0n;
  }
  return oldS < 0n ? oldS + m : oldS;
}

function modInverseSmall(a, m) {
  a = Number(a);
  m = Number(m);
  const maxSMI = (~(-1 << 30));
  if (a < 0 || a >= m || m <= 0 || m > maxSMI) {
    throw new RangeError();
  }
  // We use the extended Euclidean algorithm:
  let oldR = a & maxSMI;
  let r = m & maxSMI;
  let oldS = 1;
  let s = 0;
  while (r !== 0) {
    const q = Math.floor(oldR / r);
    const newR = oldR % r;
    oldR = r;
    r = newR;
    const newS = oldS - q * s;
    oldS = s;
    s = newS;
  }
  if (oldR !== 1) {
    return 0;
  }
  return oldS < 0 ? oldS + m : oldS;
}

function squareRootModuloOddPrimeBig(n, p, e = 1) {
  n = BigInt(n);
  p = BigInt(p);
  e = Number(e);
  const m = e === 1 ? p : (e === 2 ? p * p : 0n); // p**BigInt(e)
  n %= m;
  if (!(n > 0n && p > 0n && e >= 1 && n % p !== 0n)) { // + p is a prime number
    throw new RangeError();
  }
  if ((p + 1n) % 4n === 0n) {
    if (e !== 1) {
      const x = squareRootModuloOddPrimeBig(n, p, e - 1);
      if (x === -1n) {
        return -1n;
      }
      let x1 = (x + (n - (x * x) % m) * modInverse(x + x, m)) % m;
      if (x1 < 0n) {
        x1 += m;
      }
      if (x1 > m - x1) {
        x1 = m - x1;
      }
      return x1;
    }
    // from https://en.wikipedia.org/wiki/Quadratic_residue#Prime_or_prime_power_modulus :
    let r = modPow(n, (p + 1n) / 4n, p);
    if ((r * r) % p === n) {
      if (r > p - r) {
        r = p - r;
      }
      return r;
    }
    return -1n;
  }
  throw new RangeError('implemented only for primes of the form 4k+3');
}

function getSquareRootsModuloTwo(n, e = 1) {
  if (e >= 3) {
    if (n % 8 === 1) { // from Cohen H.
      const m = Math.pow(2, e);
      const candidate = getSquareRootsModuloTwo(n, e - 1)[0];
      const candidate2 = m / 4 - candidate;
      const r = (candidate * candidate) % m !== n ? candidate2 : candidate;
      return [r, m / 2 - r, m / 2 + r, m - r];
    }
    return [];
  }
  if (e >= 2) {
    if (n % 4 === 1) {
      return [1, 3];
    }
    return [];
  }
  if (e >= 1) {
    return [1];
  }
  return [];
}

function squareRootModuloOddPrime(n, p, e = 1) { // slow for non-small p
  n = Number(n);
  p = Number(p);
  e = Number(e);
  const m = Math.pow(p, e);
  n = n % m;
  if (!(n > 0 && p > 0 && e >= 1 && n % p !== 0 && m < Math.floor(Math.sqrt(Number.MAX_SAFE_INTEGER)))) { // + p is a prime number
    throw new RangeError();
  }
  if (p % 2 === 0) {
    throw new RangeError();
  }
  // r**2 == n (mod p)
  if (e > 1) {
    const x = squareRootModuloOddPrime(n, p, e - 1);
    if (x === -1) {
      return [];
    }
    // x**2 = n mod p**(e - 1)
    // x1 = x + a * p**(e-1)
    // x1**2 = x**2 + (a * p**(e-1))**2 + 2*x*a*p**(e-1) = n mod p**e
    // a*p**(e-1) = (n - x**2) * (2*x)**-1 mod p**e
    let x1 = x + ((n - x * x) % m * modInverseSmall(2 * x, m)) % m;
    if (x1 >= m) {
      x1 -= m;
    }
    if (x1 < 0) {
      x1 += m;
    }
    if (x1 > m - x1) {
      x1 = m - x1;
    }
    return x1;
  }
  if ((p + 1) % 4 === 0) {
    // from https://en.wikipedia.org/wiki/Quadratic_residue#Prime_or_prime_power_modulus :
    let r = modPowSmall(n, (p + 1) / 4, p);
    if ((r * r) % p === n) {
      if (r > p - r) {
        r = p - r;
      }
      return r;
    }
  }
  let rrmnmodp = 1 - n; // r**2 % p - n
  for (let tworm1 = -1; tworm1 < p; tworm1 += 2) {
    rrmnmodp += tworm1;
    if (rrmnmodp >= p) {
      rrmnmodp -= p;
    }
    if (rrmnmodp === 0) {
      const r = Math.floor((tworm1 + 1) / 2);
      return r;
    }
  }
  return -1;
}

function bitLength(x) {
  return BigInt(x.toString(16).length * 4);
}

function sqrt(x) {
  if (x < BigInt((Number.MAX_SAFE_INTEGER + 1) / 2)) {
    return BigInt(Math.floor(Math.sqrt(Number(x) + 0.5)));
  }
  const q = (bitLength(x) / 4n);
  const initialGuess = ((sqrt(x >> (q * 2n)) + 1n) << q);
  let a = initialGuess;
  let b = a + 1n;
  while (a < b) {
    b = a;
    a = (b + x / b) / 2n;
  }
  return b;
}

function getSmoothFactorization(a, base) {
  let value = BigInt(a);
  if (value === 0n) {
    return [];
  }
  const result = [];
  if (value < 0n) {
    result.push(-1);
    value = -value;
  }
  let i = 0;

  let fastValue = FastModBigInt(value);
  let isBig = value > BigInt(Number.MAX_SAFE_INTEGER);
  while (i < base.length && isBig) {
    const p = base[i];
    while (FastMod(fastValue, p) === 0) {
      value /= BigInt(p);
      fastValue = FastModBigInt(value);
      isBig = value > BigInt(Number.MAX_SAFE_INTEGER);
      result.push(p);
    }
    i += 1;
  }

  let n = Number(value);
  while (i < base.length) {
    const p = base[i];
    while (n - Math.floor(n / p) * p === 0) {
      n /= p;
      result.push(p);
    }
    if (n !== 1 && n < p * p) {
      // n should be prime (?)
      const index = indexOf(base, n);
      if (index === -1) {
        return null;
      }
      result.push(n);
      return result;
    }
    i += 1;
  }
  return n === 1 ? result : null;
}

// (X**2 - Y) % N === 0, where Y is a smooth number
function CongruenceOfsquareOfXminusYmoduloN(X, Y, N, factorization) {
  this.X = X;
  this.Y = Y;
  this.N = N;
  this.factorization = factorization;
}
CongruenceOfsquareOfXminusYmoduloN.prototype.toString = function () {
  const X = this.X;
  const Y = this.Y;
  const N = this.N;
  return 'X**2 ≡ Y (mod N), Y = F'.replaceAll('X', X).replaceAll('Y', Y).replaceAll('N', N).replaceAll('F', this.factorization.join(' * '));
};

function isQuadraticResidueModuloPrime(a, p) {
  a = BigInt(a);
  p = Number(p);
  if (p === 2) {
    // "Modulo 2, every integer is a quadratic residue." - https://en.wikipedia.org/wiki/Quadratic_residue#Prime_modulus
    return true;
  }
  // https://en.wikipedia.org/wiki/Euler%27s_criterion
  const amodp = Number(BigInt(a) % BigInt(p));
  if (amodp === 0) {
    return true;
  }
  console.assert(p % 2 === 1);
  const value = modPowSmall(amodp, (p - 1) / 2, p);
  console.assert(value === 1 || value === p - 1);
  return value === 1;
}

function isQuadraticResidueModuloPrimeBig(a, p) {
  a = BigInt(a);
  p = BigInt(p);
  if (p === 2n) {
    // "Modulo 2, every integer is a quadratic residue." - https://en.wikipedia.org/wiki/Quadratic_residue#Prime_modulus
    return true;
  }
  // https://en.wikipedia.org/wiki/Euler%27s_criterion
  const amodp = a % p;
  if (amodp === 0n) {
    return true;
  }
  console.assert(p % 2n === 1n);
  const value = modPow(amodp, (p - 1n) / 2n, p);
  console.assert(value === 1n || value === p - 1n);
  return value === 1n;
}

function log(N) {
  const e = Math.max(Number(bitLength(N)) - 4 * 12, 0);
  const lnn = Math.log(Number(N >> BigInt(e))) + Math.log(2) * e;
  return lnn;
}

function L(N) {  // exp(sqrt(log(n)*log(log(n))))
  const lnn = log(N);
  return Math.exp(Math.sqrt(lnn * Math.log(lnn)));
}

function product(array) {
  const n = array.length;
  const m = Math.floor(n / 2);
  return n === 0 ? 1n : (n === 1 ? BigInt(array[0]) : product(array.slice(0, m)) * product(array.slice(m)));
}

function modPowSmall(base, exponent, modulus) {
  base = Number(base);
  exponent = Number(exponent);
  modulus = Number(modulus);
  if (Math.max(Math.pow(modulus, 2), Math.pow(base, 2)) > Number.MAX_SAFE_INTEGER) {
    throw new RangeError();
  }
  let accumulator = 1;
  while (exponent !== 0) {
    if (exponent % 2 === 0) {
      exponent /= 2;
      base = (base * base) % modulus;
    } else {
      exponent -= 1;
      accumulator = (accumulator * base) % modulus;
    }
  }
  return accumulator;
}

function modPow(base, exponent, modulus) {
  base = BigInt(base);
  exponent = BigInt(exponent);
  modulus = BigInt(modulus);
  let accumulator = 1n;
  while (exponent !== 0n) {
    if (exponent % 2n === 0n) {
      exponent /= 2n;
      base = (base * base) % modulus;
    } else {
      exponent -= 1n;
      accumulator = (accumulator * base) % modulus;
    }
  }
  return accumulator;
}

function primes(MAX) {
  // Note: it is slow in Chrome to create array this way when MAX >= 2**25
  const sieve = new Array(MAX + 1).fill(true);
  const result = [];
  result.push(2);
  for (let i = 3; i <= MAX; i += 2) {
    if (sieve[i]) {
      result.push(i);
      for (let j = i * i; j <= MAX; j += 2 * i) {
        sieve[j] = false;
      }
    }
  }
  return result;
}

const BitSetWordSize = 31; // see https://v8.dev/blog/pointer-compression

function packedArray(n) {
  // see https://v8.dev/blog/elements-kinds
  const array = [];
  for (let i = 0; i < n; i += 1) {
    array.push(0);
  }
  return array;
}
function BitSet(size) {
  const n = Math.ceil(size / (4 * BitSetWordSize)) * 4;
  this.data = packedArray(n);
  this.size = size;
}
BitSet.prototype.nextSetBit = function (index) {
  if (index >= this.size) {
    return -1;
  }
  const data = this.data;
  let q = Math.floor(index / BitSetWordSize);
  let r = index % BitSetWordSize;
  let x = data[q] >> r;
  while (x === 0) {
    q += 1;
    if (q === data.length) {
      return -1;
    }
    x = data[q];
    r = 0;
  }
  // https://stackoverflow.com/questions/61442006/whats-the-most-efficient-way-of-getting-position-of-least-significant-bit-of-a
  r += 31 - Math.clz32(x & -x);
  return q * BitSetWordSize + r;
};
BitSet.prototype.toggle = function (index) {
  if (index >= this.size) {
    throw new RangeError();
  }
  const q = Math.floor(index / BitSetWordSize);
  const r = index % BitSetWordSize;
  this.data[q] ^= (r === BitSetWordSize - 1 ? ((-1) << r) : (1 << r));
};
BitSet.prototype.xor = function (other) {
  const a = this.data;
  const b = other.data;
  const n = a.length;
  if (n !== b.length || n % 4 !== 0) {
    throw new RangeError();
  }
  for (let i = 0; i < n; i += 4) {
    a[i + 0] ^= b[i + 0];
    a[i + 1] ^= b[i + 1];
    a[i + 2] ^= b[i + 2];
    a[i + 3] ^= b[i + 3];
  }
};
BitSet.prototype.toString = function () {
  return this.data.map(x => (x >>> 0).toString(2).padStart(BitSetWordSize, '0').split('').reverse().join('')).join('').slice(0, this.size);
};


// pass factorizations with associated values to the next call
// returns linear combinations of vectors which result in zero vector by modulo 2
// (basis of the kernel of the matrix)
function solve(matrixSize) {
  // We build the augmented matrix in row-echelon form with permuted rows, which can grow up to matrixSize rows:
  // The augmented matrix is stored in the lower triangle!
  const M = new Array(matrixSize).fill(null); // We will fill the matrix so pivot elements will be placed on the diagonal
  const associatedValues = new Array(matrixSize).fill(undefined);
  let nextSolution = null;
  let state = 1;
  const iterator = {
    next: function solve(tmp) {
      while (true) {
        if (state === 1) {
          state = 0;
          return {value: nextSolution, done: false};
        }
        state = 1;
        const [rawRow, associatedValue] = tmp;
        let row = new BitSet(matrixSize);
        const reverseColumns = true; // makes it much faster when the data is more dense from the beginning (?)
        for (let j = 0; j < rawRow.length; j += 1) {
          const unitaryColumn = rawRow[j];
          const c = reverseColumns ? matrixSize - 1 - unitaryColumn : unitaryColumn;
          row.toggle(c);
        }
        // add row to the matrix maintaining it to be in row-echelon form:
        for (let pivotColumn = row.nextSetBit(0); pivotColumn !== -1 && row != null; pivotColumn = row == null ? -1 : row.nextSetBit(pivotColumn + 1)) {
          const pivotRow = M[pivotColumn];
          if (pivotRow != null) {
            // row-reduction:
            row.xor(pivotRow);
            console.assert(row.nextSetBit(pivotColumn) > pivotColumn || row.nextSetBit(pivotColumn) === -1);
            row.toggle(pivotColumn);
          } else {
            //row.toggle(matrixSize + pivotColumn);
            associatedValues[pivotColumn] = associatedValue;
            M[pivotColumn] = row;
            row = null;
          }
        }
        if (row != null) {
          // row has a solution
          // extract solution from the augmented part of the matrix:
          const solution = [];
          for (let i = row.nextSetBit(0); i !== -1; i = row.nextSetBit(i + 1)) {
            solution.push(associatedValues[i]);
          }
          solution.push(associatedValue);
          nextSolution = solution;
        } else {
          nextSolution = null;
        }
      }
      //console.log(M.filter(x => x != null).map(x => x.toString()).join('\n').replaceAll('0', ' '))
    }
  };
  iterator[globalThis.Symbol.iterator] = function () {
    return this;
  };
  return iterator;
}

//!copy-paste

function fmod(a, b) {
  return (a - Math.floor(a / b) * b);
}
function FastModBigInt(a) {
  const array = [];
  while (a !== 0n) {
    const x = Number(BigInt.asUintN(52, a));
    array.push(x);
    a >>= 52n;
  }
  return array;
}
function FastMod(array, integer) {
  const n = array.length - 1;
  let result = fmod(array[n], integer);
  if (n > 0) {
    let x = fmod(2**52, integer);
    for (let i = n - 1; i >= 0; i -= 1) {
      result = fmod(result * x + array[i], integer);
    }
  }
  return result | 0;
}


function exp2(x) {
  return Math.pow(2, Math.floor(x)) * Math.exp(Math.LN2 * (x - Math.floor(x)));
}

const useMultiplePolynomials = true;

// A*x**2 + 2*B*x + C, A = q**2, qInv = q**-1 mod N
function QuadraticPolynomial(A, B, C, q, qInv, N) {
  this.A = A;
  this.B = B;
  this.C = C;
  this.q = q;
  this.qInv = qInv;
  this.N = N;
  const logA = log(A);
  const u = -Math.exp(log(B) - logA);
  const v = Math.exp(log(N) / 2 - logA);
  this.x1 = u - v;
  this.x2 = u + v;
  this.log2a = logA / Math.LN2;
}

QuadraticPolynomial.prototype.calculateNewPolynomial = function (M, primes, N) {
  let q = this.q;
  if (q === 1n) {
    q = BigInt(sqrt(BigInt(sqrt(2n * N)) / BigInt(M)));//TODO: !?
    const B = BigInt(primes[primes.length - 1]);
    if (q <= B) {
      q = B + 2n;
    }
    q += 3n - q % 4n;
  } else {
    q += 4n;
  }
  while (!isPrime(q) || !isQuadraticResidueModuloPrimeBig(N, q)) {
    q += 4n;
  }
  const qInv = modInverse(q % N, N);
  if (qInv === 0n) {
    //TODO: what to do here - ?
    return new QuadraticPolynomial(0n, 0n, 0n, q, 0n, 0n).calculateNewPolynomial(M, primes, N);
  }
  const A = q * q;
  const B = squareRootModuloOddPrimeBig(N, q, 2);
  const AC = (B * B - N);
  if (AC % A !== 0n) {
    throw new Error();
  }
  const C = AC / A;
  return new QuadraticPolynomial(A, B, C, q, qInv, N);
};
QuadraticPolynomial.prototype.X = function (x) {
  return (this.A * BigInt(x) + this.B) * this.qInv;
};
QuadraticPolynomial.prototype.Y = function (x) {
  return this.A * (x * x <= Number.MAX_SAFE_INTEGER ? BigInt(x * x) : (a => a * a)(BigInt(x))) + this.B * BigInt(2 * x) + this.C;
};
QuadraticPolynomial.prototype.log2AbsY = function (x) {
  //const v1 = Math.log2(Math.abs(Number(this.Y(x))));
  const v2 =  Math.log2(Math.abs((x - this.x1) * (x - this.x2))) + this.log2a;
  return v2;
};


function thresholdApproximationInterval(polynomial, x, threshold, sieveSize) {
  let w = sieveSize > 2048 ? (sieveSize > 2**18 ? 1024 : 256) : 1;
  while (w >= 2 && Math.abs(polynomial.log2AbsY(x + w) - threshold) > 0.5) {
    w /= 2;
  }
  return x + w;
}

// https://ru.wikipedia.org/wiki/Алгоритм_Диксона
// https://www.youtube.com/watch?v=TvbQVj2tvgc

function congruencesUsingQuadraticSieve(primes, N, sieveSize0) {
  let sieveSize1 = Number(sieveSize0 || 0);
  if (sieveSize1 === 0) {
    sieveSize1 = Math.pow(2, 18);
    sieveSize1 = Math.min(sieveSize1, Math.ceil(Math.pow(primes[primes.length - 1], 1.15)));
    sieveSize1 = Math.max(sieveSize1, primes[primes.length - 1] + 1);
  }
  sieveSize1 += sieveSize1 % 2;
  const sieveSize = sieveSize1;

  if (typeof N !== 'bigint') {
    throw new RangeError();
  }
  const SIEVE = new Array(sieveSize).fill(-0);

  const twoB = 2 * Math.log2(primes.length === 0 ? Math.sqrt(2) : Number(primes[primes.length - 1]));
  const largePrimes = new Map(); // faster (?)

  // see https://www.youtube.com/watch?v=TvbQVj2tvgc
  const wheels = [];
  for (let i = 0; i < primes.length; i += 1) {
    const p = primes[i];
    for (let beta = 1, pInBeta = p; pInBeta <= sieveSize; beta += 1, pInBeta *= p) {
      const nmodpInBeta = Number(N % BigInt(pInBeta));
      if (nmodpInBeta % p === 0) {
        console.warn('N has a factor in prime base', N, p);
      } else {
        if (p === 2) {
          const roots = getSquareRootsModuloTwo(nmodpInBeta, beta);
          for (let j = 0; j < Math.ceil(roots.length / 2); j += 1) {
            wheels.push({root: roots[j], proot: 0, proot2: 0, log2p: Math.log2(p) * (pInBeta === 2 ? 0.5 : 1), step: pInBeta});
          }
        } else {
          const root = squareRootModuloOddPrime(nmodpInBeta, p, beta);
          if (root === -1) {
            throw new TypeError();
          }
          wheels.push({root: root, proot: 0, proot2: 0, log2p: Math.log2(p), step: pInBeta});
        }
      }
    }
  }

  const lpStrategy = function (p, polynomial, x) {
    // https://ru.wikipedia.org/wiki/Алгоритм_Диксона#Стратегия_LP
    const lp = largePrimes.get(p);
    if (lp == undefined) {
      // storing polynomial + x has smaller memory usage
      largePrimes.set(p, {polynomial: polynomial, x: x});
    } else {
      const s = BigInt(p);
      const sInverse = modInverse(s, N);
      if (sInverse === 0n) {
        return new CongruenceOfsquareOfXminusYmoduloN(s, 0n, N, null);//?
      } else {
        const X = polynomial.X(x);
        const Y = polynomial.Y(x);
        const lpX = lp.polynomial.X(lp.x);
        const lpY = lp.polynomial.Y(lp.x);
        const X1 = (sInverse * lpX * X) % N;
        if (Y % s === 0n && lpY % s === 0n) {
          const a = lpY / s;
          const b = Y / s;
          const Y1 = a * b;
          const fa = getSmoothFactorization(a, primes);
          const fb = getSmoothFactorization(b, primes);
          if (fa != null && fb != null) {
            const factorization = fa.concat(fb).sort((a, b) => a - b);
            return new CongruenceOfsquareOfXminusYmoduloN(X1, Y1, N, factorization);
          }
        }
      }
    }
    return null;
  };

  let polynomial = null;
  if (!useMultiplePolynomials) {
    // - Number(baseOffset % BigInt(pInBeta))
    const baseOffset = BigInt(sqrt(N)) + 1n;
    polynomial = new QuadraticPolynomial(1n, baseOffset, baseOffset * baseOffset - N, 1n, 1n, N);
    for (let i = 0; i < wheels.length; i += 1) {
      const wheel = wheels[i];
      const pInBeta = wheel.step;
      const offset = Number(baseOffset % BigInt(pInBeta));
      wheel.proot = +wheel.root - offset;
      wheel.proot2 = -wheel.root - offset;
    }
  } else {
    polynomial = new QuadraticPolynomial(1n, 0n, -N, 1n, 1n, N);
  }

  const updateWheels = function (polynomial) {
    //recalculate roots based on the formulat:
    //proot = ((-B + root) * modInv(A, pInBeta)) % pInBeta;
    //+some optimizations to minimize bigint usage and modInverseSmall calls
    const AA = FastModBigInt(polynomial.A);
    const BB = FastModBigInt(polynomial.B);
    for (let i = wheels.length - 1; i >= 0; i -= 1) {
      const w = wheels[i];
      const pInBeta = w.step;
      //const a = Number(polynomial.A % BigInt(pInBeta));
      //const b = Number(polynomial.B % BigInt(pInBeta));
      const a = FastMod(AA, pInBeta);
      const b = FastMod(BB, pInBeta);
      const invA = modInverseSmall(a, pInBeta);
      if (invA === 0) {
        throw new Error('unsupported A');
      }
      const proot1 = fmod((-b + w.root) * invA, pInBeta) | 0;
      w.proot = proot1;
      const proot2 = fmod((-b - w.root) * invA, pInBeta) | 0;
      w.proot2 = proot2;
    }
    if (false) {
      for (let k = 0; k < wheels.length; k += 1) {
        for (let v = 0; v <= 1; v += 1) {
          const x = BigInt(v === 0 ? wheels[k].proot : wheels[k].proot2);
          const X = (polynomial.A * x + polynomial.B);
          const Y = X * X - N;
          if (Y % BigInt(wheels[k].step) !== 0n) {
            throw new Error();
          }
        }
      }
    }
  };
  
  const updateSieveSegment = function (offset, segmentStart, segmentEnd) {
    for (let j = segmentStart; j < segmentEnd; j += 1) {
      SIEVE[j] = -0;
    }
    for (let j = 0; j < wheels.length; j += 1) {
      const w = wheels[j];
      const log2p = w.log2p;
      const step = w.step;
      let kpplusr = w.proot;
      while (kpplusr < segmentEnd) {
        SIEVE[kpplusr] += log2p;
        kpplusr += step;
      }
      w.proot = kpplusr;
      let kpplusr2 = w.proot2;
      while (kpplusr2 < segmentEnd) {
        SIEVE[kpplusr2] += log2p;
        kpplusr2 += step;
      }
      w.proot2 = kpplusr2;
    }
  };

  const updateSieve = function (offset) {
    for (let j = 0; j < wheels.length; j += 1) {
      const w = wheels[j];
      const step = w.step;
      const x = (w.proot - offset) % step;
      w.proot = x + (x < 0 ? step : 0);
      const x2 = (w.proot2 - offset) % step;
      w.proot2 = x2 + (x2 < 0 ? step : 0);
    }

    // updateSieveSegment(offset, 0, sieveSize);
    const segmentSize = Math.ceil(sieveSize / Math.ceil(sieveSize / 2**18));
    for (let segmentStart = 0; segmentStart < sieveSize; segmentStart += segmentSize) {
      const segmentEnd = Math.min(segmentStart + segmentSize, sieveSize);
      updateSieveSegment(offset, segmentStart, segmentEnd);
    }
  };

  const smoothEntries = [];
  const smoothEntries2 = [];
  const findSmoothEntries = function (offset, polynomial) {
    smoothEntries.length = 0;
    smoothEntries2.length = 0;
    let j = 0;
    let thresholdApproximation = 0.5;
    while (j < sieveSize) {
      const k = j;
      // it is slow to compute the threshold on every iteration, so trying to optimize:

      //TODO: the threshold calculation is much more simple in the Youtube videos (?)
      thresholdApproximation = polynomial.log2AbsY(j + offset) - twoB;
      j = thresholdApproximationInterval(polynomial, j + offset, thresholdApproximation + twoB, sieveSize) - offset;
      j = j > sieveSize ? sieveSize : j;

      for (let i = k; i < j; i += 1) {
        if (thresholdApproximation < SIEVE[i]) {
          smoothEntries.push(i + offset);
          smoothEntries2.push(SIEVE[i]);
        }
      }
    }
  };

  let i1 = -1;
  let k = 0;
  const iterator = {
    next: function congruencesUsingQuadraticSieve() {
      while (2 * k * sieveSize <= Math.pow(primes[primes.length - 1], 2)) {
        if (i1 === sieveSize) {
          k += 1;
          i1 = -1;
        }
        const offset = useMultiplePolynomials ? -sieveSize / 2 : (k % 2 === 0 ? 1 : -1) * Math.floor((k + 1) / 2) * sieveSize;
        if (i1 === -1) {

          if (useMultiplePolynomials) {
            polynomial = polynomial.calculateNewPolynomial(sieveSize / 2, primes, N);
            updateWheels(polynomial);
          }

          updateSieve(offset);
          
          findSmoothEntries(offset, polynomial);
          
        }


          //Note: separate loop over "smooth entries" is better for performance, seems
          for (let i = i1 + 1; i < smoothEntries.length; i += 1) {
            const x = smoothEntries[i];
            const value = smoothEntries2[i];
            const threshold = polynomial.log2AbsY(x);
            if (threshold - value < 1) {
              const X = polynomial.X(x);
              const Y = polynomial.Y(x);
              const factorization = getSmoothFactorization(Y, primes);
              if (factorization != null) {
                i1 = i;
                return {value: new CongruenceOfsquareOfXminusYmoduloN(X, Y, N, factorization), done: false};
              } else {
                console.count('?');
                /*let p = 1n;
                for (let n = 0; n < wheels.length; n += 1) {
                  const w = wheels[n];
                  for (let v = 0; v <= 1; v += 1) {
                    if ((x - (v === 0 ? wheels[n].proot : wheels[n].proot2)) % w.step === 0) {
                      console.log(w);
                      p *= BigInt(w.step);
                    }
                  }
                }*/
              }
            } else {
              if (threshold - value < twoB) {
                const p = Math.round(exp2(threshold - value));
                const c = lpStrategy(p, polynomial, x);
                if (c != null) {
                  i1 = i;
                  return {value: c, done: false};
                }
              }
            }
          }
        i1 = sieveSize;
      }
      return {value: undefined, done: true};
    }
  };
  iterator[globalThis.Symbol.iterator] = function () {
    return this;
  };
  return iterator;
}

function gcd(a, b) {
  while (b !== 0n) {
    const r = a % b;
    a = b;
    b = r;
  }
  return a;
}

function abs(x) {
  return x < 0n ? -x : x;
}

function indexOf(sortedArray, x) {
  let min = 0;
  let max = sortedArray.length - 1;
  while (min < max) {
    const mid = Math.ceil((min + max) / 2);
    if (sortedArray[mid] > x) {
      max = mid - 1;
    } else {
      min = mid;
    }
  }
  if (sortedArray[min] === x) {
    return min;
  }
  return -1;
}

function QuadraticSieveFactorization(N) { // N - is not a prime
  N = BigInt(N);
  for (let k = 1n;; k += 1n) {
    const kN = k * N;
    // https://trizenx.blogspot.com/2018/10/continued-fraction-factorization-method.html#:~:text=optimal%20value :
    const B = Math.min(Math.floor(Math.sqrt(L(kN) / 1.5)), (1 << 25) - 1);
    const primeBase = primes(B).filter(p => isQuadraticResidueModuloPrime(kN, p));
    for (let i = 0; i < primeBase.length; i += 1) {
      if (Number(N % BigInt(primeBase[i])) === 0) {
        return BigInt(primeBase[i]);
      }
    }
    const congruences = congruencesUsingQuadraticSieve(primeBase, kN); // congruences X_k^2 = Y_k mod N, where Y_k is smooth over the prime base
    const solutions = solve(1 + primeBase.length); // find products of Y_k = Y, so that Y is a perfect square
    solutions.next();
    let c = null;
    let c1 = 0;
    const start = Date.now();
    let last = start;
    while ((c = congruences.next().value) != undefined) {
      c1 += 1;
      const now = Date.now();
      if (now - last > 5000) {
        console.debug('congruences found: ', c1, '/', primeBase.length, 'expected time: ', (now - start) / c1 * primeBase.length);
        last = now;
      }
      const solution = c.Y === 0n ? [c] : solutions.next([c.factorization.map(p => (p === -1 ? 0 : 1 + indexOf(primeBase, p))), c]).value;
      if (solution != null) {
        const X = product(solution.map(c => c.X));
        const Y = product(solution.map(c => c.Y)); // = sqrt(X**2 % N)
        const x = X;
        const y = BigInt(sqrt(Y));
        console.assert(y * y === BigInt(Y));
        const g = gcd(abs(x + y), N);
        if (g !== 1n && g !== N) {
          return g;
        }
      }
    }
  }
}

QuadraticSieveFactorization.testables = {
  isPrime: isPrime,
  congruencesUsingQuadraticSieve: congruencesUsingQuadraticSieve,
  squareRootModuloOddPrime: squareRootModuloOddPrime,
  squareRootModuloOddPrimeBig: squareRootModuloOddPrimeBig,
  isQuadraticResidueModuloPrime: isQuadraticResidueModuloPrime,
  isQuadraticResidueModuloPrimeBig: isQuadraticResidueModuloPrimeBig,
  solve: solve,
  QuadraticPolynomial: QuadraticPolynomial,
  thresholdApproximationInterval: thresholdApproximationInterval
};

export default QuadraticSieveFactorization;
