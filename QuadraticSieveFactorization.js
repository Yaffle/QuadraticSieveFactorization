/*jshint esversion:11, bitwise:false*/

import solve from './solve.js';
import sqrtMod from './sqrtMod.js';

function modInverse(a, m) {
  if (typeof a !== 'bigint' || typeof m !== 'bigint') {
    throw new TypeError();
  }
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
  if (typeof a !== 'number' || typeof m !== 'number') {
    throw new TypeError();
  }
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

function ChineseRemainderTheorem(r1, r2, m1, m2) {
  if (typeof r1 !== 'bigint' || typeof r2 !== 'bigint' || typeof m1 !== 'bigint' || typeof m2 !== 'bigint') {
    throw new TypeError();
  }
  // https://en.wikipedia.org/wiki/Chinese_remainder_theorem#Case_of_two_moduli
  // x = r1 (mod m1)
  // x = r2 (mod m2)
  const c = modInverse(m1 % m2, m2);
  return r1 + (((r2 - r1) * c) % m2) * m1;
}

function squareRootsModuloOddPrimesProduct(n, primes, e = 1) {
  // Chinese Remainder Theorem idea from https://en.wikipedia.org/wiki/Quadratic_residue#Complexity_of_finding_square_roots
  let result = [];
  result.push(0n);
  let P = 1n;
  for (let i = 0; i < primes.length; i += 1) {
    const p = BigInt(Math.pow(primes[i], e));
    if (Number(p) > Number.MAX_SAFE_INTEGER) {
      throw new RangeError();
    }
    const x2 = BigInt(squareRootModuloOddPrime(Number(n % p), primes[i], e));
    const result2 = [];
    for (let j = 0; j < result.length; j += 1) {
      const x1 = result[j];
      result2.push(ChineseRemainderTheorem(x1, x2, P, p));
      result2.push(ChineseRemainderTheorem(x1, -x2, P, p));
    }
    P *= p;
    result = result2;
  }
  return result;
}

function squareRootsModuloTwo(n, e = 1) {
  if (e >= 3) {
    if (n % 8 === 1) { // from Cohen H.
      const m = Math.pow(2, e);
      const candidate = +squareRootsModuloTwo(n, e - 1)[0];
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
  if (typeof n !== 'number' || typeof p !== 'number' || typeof e !== 'number') {
    throw new TypeError();
  }
  const m = Math.pow(p, e);
  if (!(n > 0 && n < m && p > 0 && e >= 1 && +n % +p !== 0 && m < Math.floor(Math.sqrt(Number.MAX_SAFE_INTEGER * 4)))) { // + p is a prime number
    throw new RangeError();
  }
  if (p % 2 === 0) {
    throw new RangeError();
  }
  // r**2 == n (mod p)
  if (e > 1) {
    const x = squareRootModuloOddPrime(n % Math.pow(p, e - 1), p, e - 1);
    // x**2 = n mod p**(e - 1)
    // x1 = x + a * p**(e-1)
    // x1**2 = x**2 + (a * p**(e-1))**2 + 2*x*a*p**(e-1) = n mod p**e
    // a*p**(e-1) = (n - x**2) * (2*x)**-1 mod p**e
    let inv = modInverseSmall(2 * x, m) % m;
    let v = (n - x * x) % m;
    inv = inv > m / 2 ? inv - m : inv; // use sign bit
    v = v > m / 2 ? v - m : v; // use sign bit
    let x1 = x + (v * inv) % m;
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
  if (true) {
    const r = sqrtMod(n, p);
    return Math.min(r, p - r);
  }
  let rrmnmodp = 1 - n; // r**2 % p - n
  for (let tworm1 = -1; true; tworm1 += 2) {
    rrmnmodp += tworm1;
    if (rrmnmodp >= p) {
      rrmnmodp -= p;
    }
    if (rrmnmodp === 0) {
      const r = Math.floor((tworm1 + 1) / 2);
      return r;
    }
  }
  throw new RangeError();
}

function bitLength(x) {
  return BigInt(x.toString(16).length * 4);
}

function sqrt(x) {
  if (x < BigInt((Number.MAX_SAFE_INTEGER + 1) / 2)) {
    return BigInt(Math.floor(Math.sqrt(Number(BigInt(x)) + 0.5)));
  }
  const q = (bitLength(x) >> 2n);
  const initialGuess = ((sqrt(x >> (q * 2n)) + 1n) << q);
  let a = initialGuess;
  let b = a + 1n;
  while (a < b) {
    b = a;
    a = (b + x / b) >> 1n;
  }
  return b;
}

function getSmoothFactorization(a, base) {
  let value = BigInt(a);
  if (value === 0n) {
    return [0];
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
    const p = +base[i];
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
function CongruenceOfsquareOfXminusYmoduloN(X, Y, N) {
  this.X = X;
  this.Y = Y;
  this.N = N;
}
CongruenceOfsquareOfXminusYmoduloN.prototype.toString = function () {
  return 'X**2 ≡ Y (mod N)'.replaceAll('X', this.X)
                           .replaceAll('N', this.N)
                           .replaceAll('Y', this.Y.join(' * '));
};

function isQuadraticResidueModuloPrime(a, p) {
  if (typeof a !== 'bigint' || typeof p !== 'number') {
    throw new TypeError();
  }
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

function log(N) {
  const e = Math.max(Number(bitLength(N)) - 4 * 12, 0);
  const lnn = Math.log(Number(N >> BigInt(e))) + Math.log(2) * e;
  return lnn;
}

function L(N) {  // exp(sqrt(log(n)*log(log(n))))
  const lnn = log(N);
  return Math.exp(Math.sqrt(lnn * Math.log(lnn)));
}

function modPowSmall(base, exponent, modulus) {
  if (typeof base !== 'number' || typeof exponent !== 'number' || typeof modulus !== 'number') {
    throw new TypeError();
  }
  if (Math.max(Math.pow(modulus, 2), Math.pow(base, 2)) > Number.MAX_SAFE_INTEGER) {
    throw new RangeError();
  }
  let accumulator = 1;
  while (exponent !== 0) {
    if (exponent % 2 === 0) {
      exponent /= 2;
      base = (+base * +base) % modulus;
    } else {
      exponent -= 1;
      accumulator = (accumulator * base) % modulus;
    }
  }
  return accumulator;
}

function modPow(base, exponent, modulus) {
  if (typeof base !== 'bigint' || typeof exponent !== 'bigint' || typeof modulus !== 'bigint') {
    throw new TypeError();
  }
  let e = exponent;
  let b = base;
  let accumulator = 1n;
  while (e !== 0n) {
    if (BigInt.asUintN(1, e) === 1n) {
      e -= 1n;
      accumulator = (accumulator * b) % modulus;
    }
    e >>= 1n;
    b = (b * b) % modulus;
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
      if (i <= Math.floor(MAX / i)) {
        for (let j = i * i; j <= MAX; j += 2 * i) {
          sieve[j] = false;
        }
      }
    }
  }
  return result;
}

//!copy-paste

function FastModBigInt(a) {
  const array = [];
  while (a !== 0n) {
    const x = Number(BigInt.asUintN(51, a));
    array.push(x);
    a >>= 51n;
  }
  return array;
}
function FastMod(array, integer) {
  const n = array.length - 1;
  let result = array[n];
  const v = integer;
  const inv = (1 + 2**-52) / v;
  result -= Math.floor(result * inv) * v;
  if (n > 0) {
    const x = 2**51 - Math.floor(2**51 * inv) * v;
    let i = n;
    do {
      i -= 1;
      result = result * x + array[i];
      result -= Math.floor(result * inv) * v;
    } while (i !== 0);
  }
  return result;
}

//squareRootModuloOddPrime(4865648, 9749, 2)  // huge size of p**e

function exp2(x) {
  return Math.round(Math.pow(2, Math.floor(x)) * Math.exp(Math.LN2 * (x - Math.floor(x))));
}

const useMultiplePolynomials = true;

// (A * x + B)**2 - N = A * (A * x**2 + 2 * B * x + C), A * C = B**2 - N
function QuadraticPolynomial(A, B, N, AFactors) {
  if (typeof A !== 'bigint' || typeof B !== 'bigint' || typeof N !== 'bigint') {
    throw new TypeError();
  }
  const AC = (B * B - N);
  if (AC % A !== 0n) {
    throw new TypeError();
  }
  const C = AC / A;
  this.A = A;
  this.B = B;
  this.C = C;
  this.AFactors = AFactors;
  const logA = log(A);
  const u = -Math.exp(log(B) - logA);
  const v = Math.exp(log(N) / 2 - logA);
  this.x1 = u - v;
  this.x2 = u + v;
  this.log2a = logA / Math.LN2;
}
QuadraticPolynomial.generator = function (M, primes, N) {
  // see https://www.cs.virginia.edu/crab/QFS_Simple.pdf for multiple primes optimization
  const getCombinations = function (elements, k) {
    if (elements.length === 0) {
      return [];
    }
    if (k === 0) {
      return [[]];
    }
    if (k === 1) {
      return elements.map(e => [e]);
    }
    return getCombinations(elements.slice(1), k - 1).map(c => [elements[0]].concat(c)).concat(getCombinations(elements.slice(1), k));
  };
  const nthRootApprox = function (A, n) {
    if (typeof A !== 'bigint') {
      throw new TypeError();
    }
    const e = bitLength(A);
    return Math.round(e <= 1023n ? Math.pow(Number(A), 1 / n) : Math.pow(Number(A >> (e - 1023n)), 1 / n) * Math.pow(2, Number(e - 1023n) / n));
  };
  const S = BigInt(sqrt(2n * N)) / BigInt(M);
  const e = log(S) / Math.log(2);
  if (primes.length < 42) {
    throw new TypeError();//TODO:
  }
  const max1 = Math.log2(primes[primes.length - 1]);
  const k = Math.max(2, Math.ceil(e / Math.min(14.5, max1) / 2) * 2); // number of small primes
  //console.debug(k);
  const p = nthRootApprox(S, k);
  let s = 0;
  const nextPrime = function () {
    let p3 = 0;
    do {
      p3 = p - p % 2 + 1 + (s % 2 === 0 ? s : (-1 - s));
      s += 1;
    } while (indexOf(primes, p3) === -1);
    return p3;
  };
  let combinations = [];
  const polynomials = [];
  const elements = [];
  QuadraticSieveFactorization.polynomialsCounter = 0;
  return {
    next: function generator() {
      while (polynomials.length === 0) {
        // There must be at least two different primes from previous selections. - from https://www.rieselprime.de/ziki/Self-initializing_quadratic_sieve
        while (combinations.length === 0) {
          const p3 = nextPrime();
          const p4 = nextPrime();
          console.assert(k % 2 === 0);
          combinations = getCombinations(elements, k / 2 - 1).map(c => [[p3, p4]].concat(c));
          elements.push([p3, p4]);
          //console.log(elements.length, combinations.length, p**k / Number(S));
        }
        const qPrimes = combinations.pop().reduce((array, pair) => array.concat(pair), []);
        const q = BigInt(qPrimes.reduce((p, a) => p * BigInt(a), 1n));
        const qInv = modInverse(q % N, N);
        if (qInv === 0n) {
          //TODO: what to do here - ?
          return this.next();
        }
        const A = q;
        const Bs = squareRootsModuloOddPrimesProduct(N, qPrimes, 1);
        for (let i = 0; i < Bs.length; i += 1) {
          Bs[i] = Bs[i] < 0n ? A - Bs[i] : Bs[i];
        }
        Bs.sort((a, b) => Number(BigInt(a) - BigInt(b)));
        for (let i = 0; i < Bs.length / 2; i += 1) {
          const B = Bs[i];
          polynomials.push(new QuadraticPolynomial(A, B, N, qPrimes));
        }
      }
      QuadraticSieveFactorization.polynomialsCounter += 1;
      return polynomials.shift();
    }
  };
};
QuadraticPolynomial.prototype.X = function (x) {
  return (this.A * BigInt(x) + this.B);
};
QuadraticPolynomial.prototype.Y = function (x, s, primes) {
  if (typeof x !== 'number') {
    throw new TypeError();
  }
  const Y = this.A * (x * x >= 2**53 ? BigInt(x) * BigInt(x) : BigInt(x * x)) + this.B * BigInt(2 * x) + this.C;
  if (Y % s !== 0n) {
    return null;
  }
  const YFactors = getSmoothFactorization(Y / s, primes);
  if (YFactors == null) {
    return null;
  }
  if (YFactors.length === 1 && YFactors[0] === 0) {
    return YFactors;
  }
  return this.AFactors.concat(YFactors);
};
QuadraticPolynomial.prototype.log2AbsY = function (x) {
  if (typeof x !== 'number') {
    throw new TypeError();
  }
  //const v1 = Math.log2(Math.abs(Number(this.Y(x))));
  const v2 =  Math.log2(Math.abs((x - this.x1) * (x - this.x2))) + this.log2a;
  return v2;
};

function thresholdApproximationInterval(polynomial, x, threshold, sieveSize) {
  let w = sieveSize > 2048 ? (sieveSize > 2**18 ? 1024 : 256) : 1;
  while (w >= 2 && Math.abs(polynomial.log2AbsY(x + w) - threshold) > 0.5) {
    w = Math.floor(w / 2);
  }
  return x + w;
}

// https://ru.wikipedia.org/wiki/Алгоритм_Диксона
// https://www.youtube.com/watch?v=TvbQVj2tvgc
// https://www.rieselprime.de/ziki/Self-initializing_quadratic_sieve

function packedDoubleArray(n) {
  const array = [];
  for (let i = 0; i < n; i += 1) {
    array.push(-0);
  }
  return array.slice(0);
}

function packedIntArray(n) {
  const array = [];
  for (let i = 0; i < n; i += 1) {
    array.push(0);
  }
  return array.slice(0);
}

function congruencesUsingQuadraticSieve(primes, N, sieveSize0) {
  if (typeof N !== 'bigint') {
    throw new TypeError();
  }
  let sieveSize1 = Number(sieveSize0 || 0);
  if (sieveSize1 === 0) {
    sieveSize1 = 3 * 2**14;
    sieveSize1 = Math.min(sieveSize1, Math.ceil(Math.pow(+primes[primes.length - 1], 1.15)));
    sieveSize1 = Math.max(sieveSize1, primes[primes.length - 1] + 1);
    if (sieveSize1 > 2**21) {
      sieveSize1 = Math.max(2**21, Math.floor(sieveSize1 / 3));
    } else if (sieveSize1 > 2.75 * 2**17) {
      sieveSize1 = Math.max(2.75 * 2**17, Math.floor(sieveSize1 / 2));
    }
  }
  //console.debug('sieveSize1', Math.log2(sieveSize1));

  const q = Math.ceil(sieveSize1 / (2.75 * 2**17));
  const segmentSize = Math.ceil(Math.ceil(sieveSize1 / q) / 2) * 2;
  const sieveSize = segmentSize * q;
  const SIEVE_SEGMENT = packedDoubleArray(segmentSize);

  const log2B = Math.log2(primes.length === 0 ? Math.sqrt(2) : +primes[primes.length - 1]);
  const twoB = log2B + Math.min(8.5, log2B);
  const largePrimes = new Map(); // faster (?)

  // see https://www.youtube.com/watch?v=TvbQVj2tvgc
  const wheels0 = [];
  for (let i = 0; i < primes.length; i += 1) {
    const p = +primes[i];
    for (let beta = 1, pInBeta = p; pInBeta <= sieveSize || beta === 1; beta += 1, pInBeta *= p) {
      const nmodpInBeta = Number(N % BigInt(pInBeta));
      if (nmodpInBeta % p === 0) {
        //console.warn('N has a factor in prime base', N, p);
      } else {
        if (p === 2) {
          const roots = squareRootsModuloTwo(nmodpInBeta, beta);
          for (let j = 0; j < Math.ceil(roots.length / 2); j += 1) {
            wheels0.push({step: pInBeta, p: p, root: roots[j] | 0});
          }
        } else {
          const root = squareRootModuloOddPrime(nmodpInBeta, p, beta);
          wheels0.push({step: pInBeta, p: p, root: root | 0});
        }
      }
    }
  }
  wheels0.sort((a, b) => +a.step - +b.step);

  const wheelLogs = packedDoubleArray(wheels0.length);
  const wheelRoots = packedIntArray(wheels0.length);
  const wheelData = packedIntArray(wheels0.length * 3);

  for (let i = 0; i < wheels0.length; i += 1) {
    const w = wheels0[i];
    const wheel = i * 3;
    wheelData[wheel] = w.step | 0;
    wheelData[wheel + 1] = 0;
    wheelData[wheel + 2] = 0;
    wheelLogs[i] = Math.log2(w.p) * (w.step === 2 ? 0.5 : 1);
    wheelRoots[i] = w.root | 0;
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
        return new CongruenceOfsquareOfXminusYmoduloN(s, [0], N);//?
      } else {
        const X = polynomial.X(x);
        const Y = polynomial.Y(x, s, primes);
        const lpX = lp.polynomial.X(lp.x);
        const lpY = lp.polynomial.Y(lp.x, s, primes);
        const X1 = (sInverse * lpX * X) % N;
        if (Y != null && lpY != null) {
          const Y1 = Y.concat(lpY);
          return new CongruenceOfsquareOfXminusYmoduloN(X1, Y1, N);
        }
      }
    }
    return null;
  };

  const polynomialGenerator = useMultiplePolynomials ? QuadraticPolynomial.generator(sieveSize / 2, primes, N) : null;
  let polynomial = null;
  let baseOffsets = null;
  if (!useMultiplePolynomials) {
    const baseOffset = BigInt(sqrt(N)) + 1n;
    polynomial = new QuadraticPolynomial(1n, baseOffset, N, []);
    baseOffsets = packedIntArray(wheels0.length);
    // - Number(baseOffset % BigInt(pInBeta))
    for (let i = 0; i < wheels0.length; i += 1) {
      baseOffsets[i] = Number(baseOffset % BigInt(wheels0[i].step)) | 0;
    }
  }

  let invCacheKey = 0n;
  const invCache = packedIntArray(wheels0.length);

  function checkWheels(offset) {
    for (let k = 0; k < wheelData.length / 3; k += 1) {
      for (let v = 0; v <= 1; v += 1) {
        const wheel = k * 3;
        const root = (v === 0 ? wheelData[wheel + 1] : wheelData[wheel + 2]);
        if (root !== sieveSize) {
          const x = BigInt(+root + offset);
          const X = (polynomial.A * x + polynomial.B);
          const Y = X * X - N;
          if (Y % polynomial.A !== 0n || (Y / polynomial.A) % BigInt(wheelData[wheel]) !== 0n) {
            throw new Error();
          }
        }
      }
    }
  }

  const updateWheels = function (polynomial, offset) {
    //recalculate roots based on the formula:
    //proot = ((-B + root) * modInv(A, p)) % p;
    //+some optimizations to minimize bigint usage and modInverseSmall calls
    const AA = FastModBigInt(polynomial.A);
    const BB = FastModBigInt(polynomial.B);
    const useCache = BigInt(polynomial.A) === BigInt(invCacheKey);
    for (let i = 0; (i + i + i) < wheelData.length; i += 1) {
      const wheel = (i + i + i);
      const p = wheelData[wheel] | 0;
      const root = wheelRoots[i] | 0;
      if (!useCache) {
        //const a = Number(polynomial.A % BigInt(p));
        const a = FastMod(AA, p);
        invCache[i] = modInverseSmall(a, p) | 0;
      }
      const invA = invCache[i] | 0;
      //const b = Number(polynomial.B % BigInt(p));
      const pInv = (1 + 2**-52) / p;
      const b = +FastMod(BB, p);
      if (invA === 0) {
        // single root:
        // x = (2B)^-1*(-C) (mod p)
        // skip as the performance is not better
        wheelData[wheel + 1] = sieveSize;
        wheelData[wheel + 2] = sieveSize;
      } else {
        const x1 = (p - b + (p + root)) * invA - offset;
        const x2 = (p - b + (p - root)) * invA - offset;
        const r1 = (x1 - Math.floor(x1 * pInv) * p) | 0; // x1 mod p
        const r2 = (x2 - Math.floor(x2 * pInv) * p) | 0; // x2 mod p
        wheelData[wheel + 1] = r2 + ((r1 - r2) & ((r1 - r2) >> 31));
        wheelData[wheel + 2] = r1 - ((r1 - r2) & ((r1 - r2) >> 31));
      }
    }
    invCacheKey = polynomial.A;
    //checkWheels(offset);
  };

  const gcd = function (a, b) {
    while (b !== 0) {
      const r = +a % +b;
      a = b;
      b = r;
    }
    return a;
  };
  const lcm = function (a, b) {
    return Math.floor(a / gcd(a, b)) * b;
  };
  const getSmallWheels = function () {
    let p = 1;
    let i = 0;
    while (i < wheels0.length && lcm(p, wheels0[i].step) <= segmentSize / 5) {
      p = lcm(p, wheels0[i].step);
      i += 1;
    }
    return i;
  };
  const smallWheels = getSmallWheels();


  const singleBlockSieve = function (limit, subsegmentEnd, s) {
    if (typeof limit !== 'number' || typeof subsegmentEnd !== 'number' || typeof s !== 'number') {
      throw new TypeError();
    }
    if (subsegmentEnd > SIEVE_SEGMENT.length || limit * 3 > wheelData.length || limit > wheelLogs.length || smallWheels < 0) {
      throw new RangeError();
    }
    for (let j = smallWheels; j < limit; j += 1) {
      const log2p = +wheelLogs[j];
      const wheel = (j + j + j);
      const step = wheelData[wheel] | 0;
      let kpplusr = wheelData[wheel + 1] | 0;
      let kpplusr2 = wheelData[wheel + 2] | 0;
      if (kpplusr > kpplusr2 || kpplusr < 0) {
        throw new RangeError();
      }
      while (kpplusr2 < subsegmentEnd) {
        SIEVE_SEGMENT[kpplusr] += log2p;
        kpplusr += step;
        SIEVE_SEGMENT[kpplusr2] += log2p;
        kpplusr2 += step;
      }
      if (kpplusr < subsegmentEnd) {
        SIEVE_SEGMENT[kpplusr] += log2p;
        kpplusr += step;
        const tmp = kpplusr;
        kpplusr = kpplusr2;
        kpplusr2 = tmp;
      }
      wheelData[wheel + 1] = kpplusr - s;
      wheelData[wheel + 2] = kpplusr2 - s;
    }
  };

  const copyCycle = function (array, cycleLength, limit) {
    if (typeof limit !== 'number' || typeof cycleLength !== 'number') {
      throw new TypeError();
    }
    if (limit > array.length || cycleLength > array.length) {
      throw new RangeError();
    }
    let i = 0;
    while (i + 3 < cycleLength) {
      const a = array[i + 0];
      const b = array[i + 1];
      const c = array[i + 2];
      const d = array[i + 3];
      let j = cycleLength + i;
      while (j + 3 < limit) {
        array[j + 0] = a;
        array[j + 1] = b;
        array[j + 2] = c;
        array[j + 3] = d;
        j += cycleLength;
      }
      if (j + 0 < limit) {
        array[j + 0] = a;
      }
      if (j + 1 < limit) {
        array[j + 1] = b;
      }
      if (j + 2 < limit) {
        array[j + 2] = c;
      }
      i += 4;
    }
    while (i < cycleLength) {
      const a = array[i];
      let j = cycleLength + i;
      while (j < limit) {
        array[j] = a;
        j += cycleLength;
      }
      i += 1;
    }
  };

  const updateSieveSegment = function (segmentStart) {
    if (typeof segmentStart !== 'number') {
      throw new TypeError();
    }
    let cycleLength = 1;
    SIEVE_SEGMENT[0] = -0;
    for (let j = 0; j < smallWheels; j += 1) {
      const wheel = (j + j + j);
      const newCycleLength = +lcm(cycleLength, wheelData[wheel]);
      copyCycle(SIEVE_SEGMENT, cycleLength, newCycleLength);
      cycleLength = newCycleLength;
      const step = wheelData[wheel] | 0;
      const log2p = +wheelLogs[j];
      for (let k = ((wheelData[wheel + 1] | 0) + newCycleLength - segmentStart % newCycleLength) % step; k < newCycleLength; k += step) {
        SIEVE_SEGMENT[k] += log2p;
      }
      for (let k = ((wheelData[wheel + 2] | 0) + newCycleLength - segmentStart % newCycleLength) % step; k < newCycleLength; k += step) {
        SIEVE_SEGMENT[k] += log2p;
      }
    }
    copyCycle(SIEVE_SEGMENT, cycleLength, segmentSize);
    //for (let j = 0; j < segmentSize; j += 1) {
    //  SIEVE_SEGMENT[j] = -0;
    //}
    // "Block Sieving Algorithms" by Georg Wambach and Hannes Wettig May 1995
    const V = 64;
    const S = 2**12 - Math.floor(V * 5 / 2);
    let subsegmentEnd = 0;
    while (subsegmentEnd + S <= segmentSize) {
      subsegmentEnd += S;
      singleBlockSieve(smallWheels + V, subsegmentEnd, 0);
    }
    singleBlockSieve(Math.floor(wheelData.length / 3), segmentSize, segmentSize);
  };

  const smoothEntries = [];
  const smoothEntries2 = [];
  const findSmoothEntries = function (offset, polynomial) {
    let i = 0;
    let thresholdApproximation = 0.5;
    while (i < segmentSize) {
      // it is slow to compute the threshold on every iteration, so trying to optimize:

      //TODO: the threshold calculation is much more simple in the Youtube videos (?)
      thresholdApproximation = polynomial.log2AbsY(i + offset) - twoB;
      const j = Math.min(segmentSize, thresholdApproximationInterval(polynomial, i + offset, thresholdApproximation + twoB, sieveSize) - offset);

      while (i < j) {
        if (i < j - 1) {
          const tmp = SIEVE_SEGMENT[j - 1];
          SIEVE_SEGMENT[j - 1] = 1/0;
          while (thresholdApproximation >= SIEVE_SEGMENT[i]) {
            i += 1;
          }
          SIEVE_SEGMENT[j - 1] = tmp;
        }
        if (thresholdApproximation < SIEVE_SEGMENT[i]) {
          smoothEntries.push(i + offset);
          smoothEntries2.push(SIEVE_SEGMENT[i]);
        }
        i += 1;
      }
    }
  };

  function checkFactorization(x) {
    let p = 0;
    for (let n = 0; n < wheelData.length / 3; n += 1) {
      for (let v = 0; v <= 1; v += 1) {
        const wheel = n * 3;
        const step = wheelData[wheel];
        if ((x - (v === 0 ? (wheelData[wheel + 1] | 0) : (wheelData[wheel + 2] | 0)) - (n < smallWheels ? 0 : segmentSize)) % step === 0) {
          if (polynomial.AFactors.indexOf(step) === -1) {
            console.log(step);
            p += +wheelLogs[n];
          }
        }
      }
    }
    return p;
  }

  function applyOffset(offset) {
    for (let j = 0; j < wheelData.length / 3; j += 1) {
      const wheel = j * 3;
      const step = wheelData[wheel];
      let r1 = (0 + (wheelRoots[j] | 0) - baseOffsets[j] - offset) % step;
      r1 += (r1 < 0 ? step : 0);
      let r2 = (0 - (wheelRoots[j] | 0) - baseOffsets[j] - offset) % step;
      r2 += (r2 < 0 ? step : 0);
      wheelData[wheel + 1] = Math.min(r1, r2);
      wheelData[wheel + 2] = Math.max(r1, r2);
    }
  }

  QuadraticSieveFactorization.lpCounter = 0;
  let i1 = -1;
  let k = 0;
  const iterator = {
    next: function congruencesUsingQuadraticSieve() {
      while ((useMultiplePolynomials ? 2 : 1/16) * k * sieveSize <= Math.pow(primes[primes.length - 1], 2)) {
        if (i1 === sieveSize) {
          k += 1;
          i1 = -1;
        }
        const offset = useMultiplePolynomials ? -sieveSize / 2 : (k % 2 === 0 ? 1 : -1) * Math.floor((k + 1) / 2) * sieveSize;
        if (i1 === -1) {

          if (useMultiplePolynomials) {
            polynomial = polynomialGenerator.next();
            updateWheels(polynomial, offset);
          } else {
            applyOffset(offset);
          }

          smoothEntries.length = 0;
          smoothEntries2.length = 0;

          for (let segmentStart = 0; segmentStart < sieveSize; segmentStart += segmentSize) {
            updateSieveSegment(segmentStart);
            findSmoothEntries(offset + segmentStart, polynomial);
          }
          
        }


          //Note: separate loop over "smooth entries" is better for performance, seems
          for (let i = i1 + 1; i < smoothEntries.length; i += 1) {
            const x = smoothEntries[i];
            const value = +smoothEntries2[i];
            const threshold = +polynomial.log2AbsY(x);
            if (threshold - value < 1) {
              const X = polynomial.X(x);
              const Y = polynomial.Y(x, 1n, primes);
              if (Y != null) {
                i1 = i;
                return {value: new CongruenceOfsquareOfXminusYmoduloN(X, Y, N), done: false};
              } else {
                console.count('?');
                //console.log(threshold, value, checkFactorization(x - offset));
              }
            } else {
              if (threshold - value < twoB) {
                const p = exp2(threshold - value);
                const c = lpStrategy(p, polynomial, x);
                if (c != null) {
                  i1 = i;
                  QuadraticSieveFactorization.lpCounter += 1;
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
    const r = BigInt(a) % BigInt(b);
    a = b;
    b = r;
  }
  return a;
}

function abs(x) {
  if (typeof x !== 'bigint') {
    throw new TypeError();
  }
  return x < 0n ? -x : x;
}

function indexOf(sortedArray, x) {
  if (typeof x !== 'number' || (x | 0) !== x) {
    throw new TypeError();
  }
  let min = 0;
  let max = sortedArray.length - 1;
  while (min < max) {
    const mid = Math.ceil((min + max) / 2);
    if ((sortedArray[mid] | 0) > (x | 0)) {
      max = mid - 1;
    } else {
      min = mid;
    }
  }
  if ((sortedArray[min] | 0) === (x | 0)) {
    return min;
  }
  return -1;
}

function computeY(primeBase, solution, N) {
  const Y = new Array(primeBase.length + 1).fill(0);
  for (let i = 0; i < solution.length; i += 1) {
    const v = solution[i].v;
    for (let j = 0; j < v.length; j += 1) {
      Y[v[j]] += 1;
    }
  }
  let y = 1n;
  for (let i = 0; i < Y.length; i += 1) {
    if (Y[i] % 2 !== 0) {
      throw new RangeError();
    }
    if (i !== 0) {
      const p = primeBase[i - 1];
      const e = Y[i] / 2;
      if (e > 0) {
        if (e <= 2) {
          y = (y * BigInt(Math.pow(p, e))) % N;
        } else {
          y = (y * modPow(BigInt(p), BigInt(e), N)) % N;
        }
      }
    }
  }
  return y;
}

function QuadraticSieveFactorization(N) { // N - is not a prime
  if (typeof N !== 'bigint') {
    throw new TypeError();
  }
  for (let k = 1n;; k += 1n) {
    const kN = k * N;
    // https://trizenx.blogspot.com/2018/10/continued-fraction-factorization-method.html#:~:text=optimal%20value :

    // to limit memory usage during "solve" to 2GB:
    const limit = Math.min(2**23, (1 << 25) - 1);
    const B = Math.max(Math.min(Math.floor(Math.sqrt(L(kN) / (Number(N) > 2**160 ? 8 : 6))), limit), 1024);

    const primeBase = primes(B).filter(p => isQuadraticResidueModuloPrime(kN, p));
    for (let i = 0; i < primeBase.length; i += 1) {
      if (Number(N % BigInt(primeBase[i])) === 0) {
        return BigInt(primeBase[i]);
      }
    }
    const congruences = congruencesUsingQuadraticSieve(primeBase, kN); // congruences X_k^2 = Y_k mod N, where Y_k is smooth over the prime base
    const solutions = solve.sparseSolve(1 + primeBase.length); // find products of Y_k = Y, so that Y is a perfect square
    solutions.next();
    let c = null;
    const start = Date.now();
    let congruencesFound = 0;
    let last = start;
    while ((c = congruences.next().value) != undefined) {
      if (c.Y.length === 1 && c.Y[0] === 0) {
        const g = BigInt(gcd(abs(c.X), N));
        if (g !== 1n && g !== N) {
          return g;
        }
      } else {
        const t = function () {
          throw new TypeError(N);
        };
        const v = c.Y.map(p => (p === -1 ? 0 : 1 + indexOf(primeBase, p) || t()));
        const solution = solutions.next([v, {c: c, v: v}]).value;
        if (true) {
          congruencesFound += 1;
          const now = +Date.now();
          if (now - last > 5000 || solution != null) {
            console.debug('congruences found: ', congruencesFound, '/', primeBase.length,
                          'expected time: ', Math.round((now - start) / congruencesFound * primeBase.length),
                          'large prime congruences: ', QuadraticSieveFactorization.lpCounter,
                          'polynomials used: ', QuadraticSieveFactorization.polynomialsCounter);
            last = now;
          }
        }
        if (solution != null) {
          let x = 1n;
          for (let i = 0; i < solution.length; i += 1) {
            x = (x * solution[i].c.X) % N;
          }
          // we cannot just compute product as it is larger 2**(2**20) (max BigInt in Firefox)
          let y = computeY(primeBase, solution, N); // Y mod N === X^2 mod N
          const g = BigInt(gcd(abs(x + y), N));
          if (g !== 1n && g !== N) {
            return g;
          }
        }
      }
    }
  }
}

QuadraticSieveFactorization.testables = {
  congruencesUsingQuadraticSieve: congruencesUsingQuadraticSieve,
  squareRootModuloOddPrime: squareRootModuloOddPrime,
  isQuadraticResidueModuloPrime: isQuadraticResidueModuloPrime,
  solve: solve,
  QuadraticPolynomial: QuadraticPolynomial,
  thresholdApproximationInterval: thresholdApproximationInterval
};

export default QuadraticSieveFactorization;

// see also https://github.com/danaj/Math-Prime-Util-GMP
