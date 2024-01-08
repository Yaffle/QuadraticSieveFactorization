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
      const r = (candidate * candidate) % m !== n % m ? candidate2 : candidate;
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
  if (!(n > 0 && n < m && p > 0 && p % 2 !== 0 && e >= 1 && +n % +p !== 0 && m < Math.floor(Math.sqrt(Number.MAX_SAFE_INTEGER * 4)))) { // + p is a prime number
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
    return Math.min(x1, m - x1);
  }
  const r = sqrtMod(n, p) | 0;
  return Math.min(r, p - r);
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
  while (i < base.length) {
    const p = base[i];
    while (value % BigInt(p) === 0n) {
      value /= BigInt(p);
      result.push(p);
    }
    i += 1;
  }
  return value === 1n ? result : null;
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
  return legendre(amodp, p) === 1;
}

function significand(a) {
  const e = Math.max(0, Number(bitLength(a)) - 1023);
  const s = Number(a >> BigInt(e));
  return s / 2**Math.floor(Math.log2(Math.abs(s)));
}

function exponent(a) {
  const e = Math.max(0, Number(bitLength(a)) - 1023);
  const s = Number(a >> BigInt(e));
  return e + Math.floor(Math.log2(Math.abs(s)));
}

function log2(a) {
  return Math.log2(significand(a)) + exponent(a);
}

function L(N) {  // exp(sqrt(log(n)*log(log(n))))
  const lnn = log2(N) * Math.log(2);
  return Math.exp(Math.sqrt(lnn * Math.log(lnn)));
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
  return new Float64Array(array);
}
function FastMod(array, m, mInv) { // mInv === (1 + 2**-52) / m
  m = -0 + m;
  mInv = -0 + mInv;
  const n = array.length - 1;
  let result = array[n];
  result = result - Math.floor(result * mInv) * m;
  if (n > 0) {
    const x = 2**51 - Math.floor(2**51 * mInv) * m;
    let i = n;
    do {
      i -= 1;
      result = result * x + array[i];
      result = result - Math.floor(result * mInv) * m;
    } while (i !== 0);
  }
  return -0 + result;
}

//squareRootModuloOddPrime(4865648, 9749, 2)  // huge size of p**e

function exp2(x) {
  let y = Math.floor(Math.pow(2, Math.floor(x)) * Math.exp(Math.LN2 * (x - Math.floor(x))));
  if (y % 2 === 0) {
    y += 1;
  }
  return y;
}

const useMultiplePolynomials = true;


// Q=((ax+b)**2-n)/a
// max value: sqrt(n)*M * 1/sqrt(2)
// a~=sqrt(2n)/M

// Q2=((2ax+b)**2-n)/(4a)
// max value: sqrt(n)*M * 1/(2*sqrt(2)) - max is two times smaller
// a=sqrt(n/2)/M

// (A * x + B)**2 - N = A * (A * x**2 + 2 * B * x + C), A * C = B**2 - N
function QuadraticPolynomial(A, B, N, AFactors, useQ2Form) {
  if (typeof A !== 'bigint' || typeof B !== 'bigint' || typeof N !== 'bigint') {
    throw new TypeError();
  }
  const BBmN = (B * B - N);
  if (useQ2Form && N % 4n !== 1n) {
    throw new RangeError();
  }
  if (BBmN % ((useQ2Form ? 4n : 1n) * A) !== 0n) {
    throw new TypeError();
  }
  const C = BBmN / (useQ2Form ? 4n * A : A);
  this.A = A;
  this.B = B;
  this.C = C;
  this.AFactors = AFactors;
  const u = (significand(B) / significand(A)) * Math.pow(2, exponent(B) - exponent(A)); // B / A
  const v = Math.sqrt(significand(N) / Math.pow(significand(A), 2)) * Math.pow(2, exponent(N) / 2 - exponent(A)); // N**(1/2) / A
  this.x1 = (useQ2Form ? 1/2 : 1) * (-u - v);
  this.x2 = (useQ2Form ? 1/2 : 1) * (-u + v);
  this.log2a = log2(A);
  this.useQ2Form = useQ2Form;
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
    return Math.round(Math.pow(significand(A), 1 / n) * Math.pow(2, exponent(A) / n));
  };
  const useQ2Form = N % 8n === 1n;
  const S = useQ2Form ? BigInt(sqrt(N / 2n)) / BigInt(M) : BigInt(sqrt(2n * N)) / BigInt(M);
  const e = log2(S);
  if (primes.length < 42) {
    throw new TypeError();//TODO:
  }
  const max1 = Math.log2(primes[primes.length - 1]);
  
  // see https://www.cecm.sfu.ca/~mmonagan/papers/NT4.pdf
  // "... Contini [5] recommends minimizing the number of duplicate relations found by requiring that the sets {qi} differ by at least two primes ..."
  const elementPrimes = 2;
  const k = Math.max(elementPrimes, Math.ceil(e / Math.min(14.5, max1) / elementPrimes) * elementPrimes); // number of small primes
  console.debug('k: ', k, 'useQ2Form: ', useQ2Form);
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
          const element = [];
          for (let i = 0; i < elementPrimes; i += 1) {
            element.push(nextPrime());
          }
          console.assert(k % elementPrimes === 0);
          combinations = getCombinations(elements, k / elementPrimes - 1).map(c => [element].concat(c));
          elements.push(element);
          //console.log(elements.length, combinations.length, p**k / Number(S));
        }
        const qPrimes = combinations.pop().reduce((array, pair) => array.concat(pair), []);
        //console.debug('qPrimes', qPrimes.join(' '));
        const q = BigInt(qPrimes.reduce((p, a) => p * BigInt(a), 1n));
        const qInv = modInverse(q % N, N);
        if (qInv === 0n) {
          //TODO: what to do here - ?
          return this.next();
        }
        const A = q;
        let Bs = squareRootsModuloOddPrimesProduct(N, qPrimes, 1);
        for (let i = 0; i < Bs.length; i += 1) {
          Bs[i] = Bs[i] < 0n ? Bs[i] + A : Bs[i];
          if (Bs[i] < 0n || Bs[i] >= A) throw new Error();
        }
        if (useQ2Form) {
          Bs = Bs.map(B => B % 2n === 0n ? B - A : B);
        }
        Bs = Bs.slice(0, Bs.length / 2);
        //DO NOT SORT!!!
        //Bs.sort((a, b) => Number(BigInt(a) - BigInt(b)));
        const aFactors = useQ2Form ? [2, 2].concat(qPrimes) : qPrimes.slice(0);
        aFactors.sort((a, b) => a - b);
        for (let i = 0; i < Bs.length; i += 1) {
          const B = Bs[i];
          polynomials.push(new QuadraticPolynomial(A, B, N, aFactors, useQ2Form));
        }
      }
      QuadraticSieveFactorization.polynomialsCounter += 1;
      return polynomials.shift();
    }
  };
};
QuadraticPolynomial.prototype.X = function (x) {
  return (this.A * BigInt((this.useQ2Form ? 2 : 1) * x) + this.B);
};
QuadraticPolynomial.prototype.Y = function (x, s, primes) {
  if (typeof x !== 'number') {
    throw new TypeError();
  }
  const Y = this.A * (x * x >= 2**53 ? BigInt(x) * BigInt(x) : BigInt(x * x)) + this.B * BigInt((this.useQ2Form ? 1 : 2) * x) + this.C;
  if (s === undefined && primes === undefined) {
    return Y;// for debugging
  }
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

const wasmCode = new Uint8Array([0, 97, 115, 109, 1, 0, 0, 0, 1, 40, 4, 96, 7, 127, 127, 127, 127, 127, 127, 127, 1, 127, 96, 2, 127, 127, 1, 127, 96, 6, 127, 127, 127, 127, 127, 127, 0, 96, 9, 127, 127, 127, 127, 127, 127, 127, 127, 127, 1, 127, 2, 15, 1, 3, 101, 110, 118, 6, 109, 101, 109, 111, 114, 121, 2, 0, 0, 3, 5, 4, 0, 1, 2, 3, 7, 85, 4, 16, 115, 105, 110, 103, 108, 101, 66, 108, 111, 99, 107, 83, 105, 101, 118, 101, 0, 0, 15, 102, 105, 110, 100, 83, 109, 111, 111, 116, 104, 69, 110, 116, 114, 121, 0, 1, 24, 117, 112, 100, 97, 116, 101, 87, 104, 101, 101, 108, 115, 73, 110, 116, 101, 114, 110, 97, 108, 78, 101, 120, 116, 0, 2, 17, 104, 97, 110, 100, 108, 101, 83, 109, 97, 108, 108, 87, 104, 101, 101, 108, 115, 0, 3, 10, 158, 6, 4, 217, 1, 1, 4, 127, 32, 0, 32, 3, 106, 33, 7, 32, 1, 32, 3, 106, 33, 8, 32, 2, 32, 3, 106, 33, 3, 32, 2, 32, 4, 106, 33, 9, 3, 64, 32, 3, 32, 9, 71, 4, 64, 32, 7, 40, 2, 0, 33, 1, 32, 8, 40, 2, 0, 33, 0, 32, 3, 40, 2, 0, 34, 4, 65, 255, 255, 255, 63, 113, 33, 2, 32, 4, 65, 27, 118, 33, 4, 3, 64, 32, 0, 32, 5, 72, 4, 64, 32, 0, 45, 0, 0, 32, 4, 106, 33, 10, 32, 1, 32, 1, 45, 0, 0, 32, 4, 106, 58, 0, 0, 32, 0, 32, 10, 58, 0, 0, 32, 1, 32, 2, 106, 33, 1, 32, 0, 32, 2, 106, 33, 0, 12, 1, 11, 11, 32, 1, 32, 5, 72, 4, 64, 32, 1, 32, 1, 45, 0, 0, 32, 4, 106, 58, 0, 0, 32, 1, 32, 2, 106, 33, 2, 32, 0, 33, 1, 32, 2, 33, 0, 11, 32, 7, 32, 1, 32, 6, 107, 54, 2, 0, 32, 8, 32, 0, 32, 6, 107, 54, 2, 0, 32, 7, 65, 4, 106, 33, 7, 32, 8, 65, 4, 106, 33, 8, 32, 3, 65, 4, 106, 33, 3, 12, 1, 11, 11, 65, 0, 11, 40, 1, 1, 123, 32, 0, 253, 15, 33, 2, 3, 64, 32, 1, 253, 0, 4, 0, 32, 2, 253, 44, 253, 83, 69, 4, 64, 32, 1, 65, 16, 106, 33, 1, 12, 1, 11, 11, 32, 1, 11, 197, 1, 2, 2, 127, 3, 123, 3, 64, 32, 6, 32, 0, 65, 2, 116, 72, 4, 64, 32, 3, 32, 6, 106, 34, 7, 253, 0, 4, 0, 32, 1, 32, 6, 106, 253, 0, 4, 0, 32, 5, 253, 17, 253, 177, 1, 34, 8, 32, 8, 253, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 55, 32, 2, 32, 6, 106, 253, 0, 4, 0, 253, 12, 255, 255, 255, 7, 255, 255, 255, 7, 255, 255, 255, 7, 255, 255, 255, 7, 253, 78, 34, 8, 253, 78, 253, 174, 1, 34, 9, 253, 177, 1, 34, 10, 32, 10, 65, 31, 253, 172, 1, 32, 8, 253, 78, 253, 174, 1, 33, 10, 32, 7, 32, 10, 32, 4, 32, 6, 106, 34, 7, 253, 0, 4, 0, 32, 9, 253, 177, 1, 34, 9, 32, 9, 65, 31, 253, 172, 1, 32, 8, 253, 78, 253, 174, 1, 34, 8, 253, 182, 1, 253, 11, 4, 0, 32, 7, 32, 10, 32, 8, 253, 184, 1, 253, 11, 4, 0, 32, 6, 65, 16, 106, 33, 6, 12, 1, 11, 11, 11, 208, 2, 2, 9, 127, 5, 123, 32, 6, 33, 9, 3, 64, 32, 10, 32, 0, 65, 2, 116, 72, 4, 64, 32, 1, 32, 10, 106, 253, 0, 4, 0, 33, 19, 32, 2, 32, 10, 106, 253, 0, 4, 0, 33, 20, 32, 4, 32, 10, 106, 253, 0, 4, 0, 33, 18, 32, 5, 32, 10, 106, 253, 0, 4, 0, 33, 21, 32, 7, 33, 12, 3, 64, 32, 8, 32, 12, 74, 4, 64, 32, 19, 32, 12, 40, 2, 0, 34, 13, 253, 17, 34, 22, 253, 177, 1, 32, 18, 253, 181, 1, 32, 20, 32, 22, 253, 177, 1, 32, 18, 253, 181, 1, 253, 183, 1, 32, 21, 253, 62, 253, 83, 4, 64, 32, 10, 33, 11, 3, 64, 32, 11, 32, 0, 65, 2, 116, 72, 32, 11, 32, 10, 65, 16, 106, 72, 113, 4, 64, 32, 3, 32, 11, 106, 40, 2, 0, 65, 255, 255, 255, 63, 113, 33, 16, 65, 1, 32, 2, 32, 11, 106, 40, 2, 0, 34, 14, 32, 1, 32, 11, 106, 40, 2, 0, 34, 15, 27, 4, 64, 32, 15, 32, 13, 107, 32, 16, 111, 4, 127, 32, 14, 32, 13, 107, 32, 16, 111, 5, 65, 0, 11, 69, 4, 64, 32, 9, 65, 2, 116, 32, 11, 65, 2, 117, 34, 17, 54, 2, 0, 32, 9, 65, 1, 106, 65, 2, 116, 32, 12, 32, 7, 107, 65, 2, 117, 34, 16, 54, 2, 0, 32, 9, 65, 2, 106, 33, 9, 32, 14, 32, 15, 70, 4, 64, 32, 9, 65, 2, 116, 32, 17, 54, 2, 0, 32, 9, 65, 1, 106, 65, 2, 116, 32, 16, 54, 2, 0, 32, 9, 65, 2, 106, 33, 9, 11, 11, 11, 32, 11, 65, 4, 106, 33, 11, 12, 1, 11, 11, 11, 32, 12, 65, 4, 106, 33, 12, 12, 1, 11, 11, 32, 10, 65, 16, 106, 33, 10, 12, 1, 11, 11, 32, 9, 32, 6, 107, 11]);

let wasmModule = null;
function instantiateWasm(memorySize) {
  if (wasmModule == null) {
    wasmModule = new WebAssembly.Module(wasmCode);
  }
  const pages = Math.ceil(memorySize / 2**16);
  const memory = new WebAssembly.Memory({
    initial: pages,
    maximum: pages
  });
  const buffer = memory.buffer;
  const exports = new WebAssembly.Instance(wasmModule, {env: { memory: memory }}).exports;
  return Object.assign({}, exports, {memory: {buffer: buffer}});
}

// TOWO: WebAssembly (~17% faster)
function instantiate(memorySize) {
  if (true && globalThis.WebAssembly != null) {
    try {
      return instantiateWasm(memorySize);
    } catch (error) {
      console.error(error);
    }
  }
  const buffer = new ArrayBuffer(memorySize);
  const exports = AsmModule(globalThis, null, buffer);
  return Object.assign({}, exports, {memory: {buffer: buffer}});
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
    if (Number(N) > 2**240) {
      sieveSize1 = Math.floor(sieveSize1 / 3.2);
    } else {
      sieveSize1 = Math.floor(sieveSize1 / 1.5);
    }
  }

  const q = Math.ceil(sieveSize1 / (typeof navigator !== 'undefined' && navigator.hardwareConcurrency === 12 ? 2.75 * 2**20 : 6 * 2**20));
  console.debug('q', q);
  const segmentSize = Math.ceil(Math.ceil(sieveSize1 / q) / 2**15) * 2**15;
  const sieveSize = segmentSize * q;
  console.debug('sieveSize', sieveSize);

  const SHIFT = 0;
  const MAX = 255;
  const SCALE = 2**0;//TODO:

  const log2B = Math.log2(primes.length === 0 ? Math.sqrt(2) : +primes[primes.length - 1]);
  const largePrimesThreshold = log2B + Math.min(Math.log2(N < 2**240 ? 100 : 400), log2B);
  const largePrimes = new Map(); // faster (?)

  // see https://www.youtube.com/watch?v=TvbQVj2tvgc
  const wheels0 = [];
  for (let i = 0; i < primes.length; i += 1) {
    const p = +primes[i];
    for (let beta = 1, pInBeta = p; pInBeta <= sieveSize || beta === 1; beta += 1, pInBeta *= p) {
      const nmodpInBeta = Number(N % BigInt(pInBeta));
      if (nmodpInBeta % p === 0) {
        //console.warn('N has a factor in prime base', N, p);
        if (beta === 1) {
          wheels0.push({step: pInBeta, p: p, root: 0});
        }
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
  while (wheels0.length % 4 !== 0) {
    wheels0.pop();
  }
  console.debug('wheels', wheels0.length);

  const wheelLogs0 = new Float64Array(wheels0.length);
  let invCacheKey = 0n;
  const zeroInvs = [];

  function nextValidHeapSize(size) {
    size = Math.max(size, 2**12);
    if (size <= 2**24) {
      return Math.pow(2, Math.ceil(Math.log2(size - 0.5)));
    }
    return Math.ceil(size / 2**24) * 2**24;
  }
  
  const wheelsCount = wheels0.length;
  console.assert(segmentSize % 4 === 0);

  let memorySize = 0;
  memorySize += segmentSize * 1;

  const wheelRoots1 = memorySize >> 2;
  memorySize += wheelsCount * 4;
  const wheelRoots2 = memorySize >> 2;
  memorySize += wheelsCount * 4;
  const wheelSteps = memorySize >> 2;
  memorySize += wheelsCount * 4;

  const storage = memorySize >> 2;
  memorySize += (16 * 1024) * 4;//TODO: what size to use?

  const wheelRoots = memorySize >> 2;
  memorySize += wheelsCount * 4;
  const invCache = memorySize >> 2;
  memorySize += wheelsCount * 4;
  const smoothEntriesX = memorySize >> 2;
  memorySize += 512 * 4;//TODO: what size?

  const alpha = memorySize >> 2;
  memorySize += 30 * wheelsCount * 4; //TODO: what size to use?

  const divTestA = memorySize >> 2;
  memorySize += wheelsCount * 4;
  const divTestB = memorySize >> 2;
  memorySize += wheelsCount * 4;

  const bufferSize = nextValidHeapSize(memorySize);
  const exports = instantiate(bufferSize);
  const singleBlockSieve = exports.singleBlockSieve;
  const findSmoothEntry = exports.findSmoothEntry;
  const updateWheelsInternalNext = exports.updateWheelsInternalNext;
  const fillAlpha = exports.fillAlpha;
  const handleSmallWheels = exports.handleSmallWheels;

  const arrayBuffer = exports.memory.buffer;
  const SIEVE_SEGMENT = new Uint8Array(arrayBuffer);
  const heap32 = new Int32Array(arrayBuffer);

  for (let i = 0; i < wheelsCount; i += 1) {
    const w = wheels0[i];
    const wheelLog = Math.log2(w.p) * (w.step === 2 || w.root === 0 ? 0.5 : 1);
    const log = Math.round(wheelLog * SCALE) | 0;
    if (log >= 2**8 || w.step >= 2**27) {
      throw new RangeError();
    }

    heap32[wheelSteps + i] = w.step | (log << 27);
    heap32[wheelRoots + i] = w.root;
    wheelLogs0[i] = wheelLog;
  }

  const lpStrategy = function (p, polynomial, x, pb) {
    // https://ru.wikipedia.org/wiki/Алгоритм_Диксона#Стратегия_LP
    const lp = largePrimes.get(p);
    if (lp == undefined) {
      // storing polynomial + x has smaller memory usage
      largePrimes.set(p, {polynomial: polynomial, x: x, pb: pb.slice(0)});
    } else {
      const s = BigInt(p);
      const sInverse = modInverse(s, N);
      if (sInverse === 0n) {
        return new CongruenceOfsquareOfXminusYmoduloN(s, [0], N);//?
      } else {
        const X = polynomial.X(x);
        const Y = polynomial.Y(x, s, pb);
        const lpX = lp.polynomial.X(lp.x);
        const lpY = lp.polynomial.Y(lp.x, s, lp.pb);
        const X1 = (sInverse * lpX * X) % N;
        if (Y != null && lpY != null) {
          const Y1 = Y.concat(lpY);
          return new CongruenceOfsquareOfXminusYmoduloN(X1, Y1, N);
        } else {
          console.count('bad lp');
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
    baseOffsets = new Float64Array(wheels0.length);
    // - Number(baseOffset % BigInt(pInBeta))
    for (let i = 0; i < wheels0.length; i += 1) {
      baseOffsets[i] = Number(baseOffset % BigInt(wheels0[i].step)) | 0;
    }
  }

  function checkWheels(offset) {
    for (let k = 0; k < wheelsCount; k += 1) {
      const p = heap32[wheelSteps + k] & 134217727;
      for (let v = 0; v <= 1; v += 1) {
        const root = (v === 0 ? heap32[wheelRoots1 + k] : heap32[wheelRoots2 + k]);
        if (root !== sieveSize) {
          const x = BigInt(+root + offset);
          const X = ((polynomial.useQ2Form ? 2n : 1n) * polynomial.A * x + polynomial.B); // polynomial.X(x)
          const Y = X * X - N;
          if (root < 0 || root >= p || Y % ((polynomial.useQ2Form ? 4n : 1n) * polynomial.A) !== 0n || (Y / ((polynomial.useQ2Form ? 4n : 1n) * polynomial.A)) % BigInt(p) !== 0n) {
            throw new Error();
          }
        }
      }
    }
  }

  /*

  export function singleBlockSieve(wheelRoots1:i32, wheelRoots2:i32, wheelSteps:i32, startWheel:i32, endWheel:i32, subsegmentEnd:i32, s:i32):i32 {
    let wr1 = wheelRoots1 + startWheel;
    let wr2 = wheelRoots2 + startWheel;
    let ws = wheelSteps + startWheel;
    const end = wheelSteps + endWheel;
    while (ws !== end) {
      let kpplusr = i32.load(wr1);
      let kpplusr2 = i32.load(wr2);
      const step = i32.load(ws) & 134217727;
      const log2p = i32.load(ws) >>> 27;
      while (kpplusr2 < subsegmentEnd) {
        const log = i32.load8_u(kpplusr) + log2p;
        const log2 = i32.load8_u(kpplusr2) + log2p;
        i32.store8(kpplusr, log);
        i32.store8(kpplusr2, log2);
        kpplusr += step;
        kpplusr2 += step;
      }
      if (kpplusr < subsegmentEnd) {
        const log = i32.load8_u(kpplusr) + log2p;
        i32.store8(kpplusr, log);
        kpplusr += step;
        const tmp = kpplusr;
        kpplusr = kpplusr2;
        kpplusr2 = tmp;
      }
      i32.store(wr1, kpplusr - s);
      i32.store(wr2, kpplusr2 - s);
      wr1 += 4;
      wr2 += 4;
      ws += 4;
    }
    return 0;
  }
  export function findSmoothEntry(thresholdApproximation:i32, i:i32):i32 {
    let t = i8x16.splat(i8(thresholdApproximation));
    while (v128.any_true(i8x16.ge_u(v128.load(i), t)) == 0) {
      i += 16;
    }
    return i;
  }
  export function updateWheelsInternalNext(wheelsCount:i32, alphav:i32, wheelSteps:i32, wheelRoots1:i32, wheelRoots2:i32, e:i32):void {
    for (let i = 0; i < (wheelsCount << 2); i += 16) {
      let a = v128.load(alphav + i);
      const p = v128.and(v128.load(wheelSteps + i), i32x4.splat(134217727));
      let r1 = v128.load(wheelRoots1 + i);
      let r2 = v128.load(wheelRoots2 + i);
      a = i32x4.sub(a, i32x4.splat(e));
      a = i32x4.add(a, v128.and(i32x4.eq(a, i32x4.splat(0)), p));
      r1 = i32x4.sub(r1, a);
      r2 = i32x4.sub(r2, a);
      r1 = i32x4.add(r1, v128.and(i32x4.shr_s(r1, 31), p)); // r1 mod p
      r2 = i32x4.add(r2, v128.and(i32x4.shr_s(r2, 31), p)); // r2 mod p
      v128.store(wheelRoots1 + i, i32x4.min_s(r1, r2));
      v128.store(wheelRoots2 + i, i32x4.max_s(r1, r2));
    }
  }
  export function handleSmallWheels(wheelsCount:i32, wheelRoots1:i32, wheelRoots2:i32, wheelSteps:i32, divTestA:i32, divTestB:i32, storage:i32, smoothEntriesXStart:i32, smoothEntriesXEnd:i32):i32 {
    let k = storage;
    for (let j = 0; j < (wheelsCount << 2); j += 16) {
      const proot1 = v128.load(wheelRoots1 + j);
      const proot2 = v128.load(wheelRoots2 + j);
      const ta = v128.load(divTestA + j);
      const tb = v128.load(divTestB + j);
      for (let i = smoothEntriesXStart; i < smoothEntriesXEnd; i += 4) {
        const e = i32x4.splat(i32.load(i));
        // divisibility test is based on https://math.stackexchange.com/a/1251328 and https://lomont.org/posts/2017/divisibility-testing/ :
        if (v128.any_true(i32x4.le_u(i32x4.min_u(i32x4.mul(i32x4.sub(proot1, e), ta), i32x4.mul(i32x4.sub(proot2, e), ta)), tb))) {
          const e = i32.load(i);
          for (let j1 = j; j1 < j + 16 && j1 < (wheelsCount << 2); j1 += 4) {
            const proot1 = i32.load(wheelRoots1 + j1);
            const proot2 = i32.load(wheelRoots2 + j1);
            const p = i32.load(wheelSteps + j1) & 134217727;
            if (proot1 !== 0 || proot2 !== 0) {
              if ((proot1 - e) % p === 0 ||
                  (proot2 - e) % p === 0) {
                i32.store((k) << 2, j1 >> 2);
                i32.store((k + 1) << 2, (i - smoothEntriesXStart) >> 2);
                k += 2;
                if (proot1 === proot2) {
                  i32.store((k) << 2, j1 >> 2);
                  i32.store((k + 1) << 2, (i - smoothEntriesXStart) >> 2);
                  k += 2;
                }
              }
            }
          }
        }
      }
    }
    return k - storage;
  }

  */


  function computeDivTestAB(d) {
    // see https://math.stackexchange.com/a/1251328 and https://lomont.org/posts/2017/divisibility-testing/
    if (d % 2 === 0) {
      if (d !== 2**Math.round(Math.log2(d))) {
        throw new RangeError();
      }
      // power of two
      return {a: 2**32 / d, b: 0};
    }
    //TODO: optimize slightly
    const a = Number(modInverse(BigInt(d), 2n**32n));
    return {a: a, b: Math.floor((2**32 - 1) / d)};
  }

  //console.log(computeDivTestAB(5)); - {a: 3435973837, b: 858993459}

  for (let i = 0; i < wheelsCount; i += 1) {
    const p = heap32[wheelSteps + i] & 134217727;
    const tmp = computeDivTestAB(p)
    heap32[divTestA + i] = tmp.a;
    heap32[divTestB + i] = tmp.b;
  }

  function mod(a, m, mInv) {
    return a - Math.floor(a * mInv) * m;
  }

  let BPrev = 0n;
  let Bdistances = [];
  let counternext = 0;

  const updateWheels = function (polynomial, offset) {
    offset = -0 + offset;
    //recalculate roots based on the formula:
    //proot = ((-B + root) * modInv(A, p)) % p;
    //+some optimizations to minimize bigint usage and modInverseSmall calls
    const AA = FastModBigInt((polynomial.useQ2Form ? 2n : 1n) * polynomial.A);
    const bsign = polynomial.B < 0n ? -1 : +1;
    const BB = FastModBigInt(polynomial.B < 0n ? -polynomial.B : polynomial.B);
    const useCache = BigInt(polynomial.A) === BigInt(invCacheKey);
    if (!useCache) {
      //  first one: ((-B + root) * modInv(A, p) - offset) % p
      //  next proots: (-(B - Bprev) * modInv(A, p) + prootPrev) % p, where (-(B - Bprev) * modInv(A, p)) mod p is cached
      zeroInvs.length = 0;
      for (let i = 0; i < wheelsCount; i += 1) {
        const p = -0 + (heap32[wheelSteps + i] & 134217727);
        const pInv = (1 + 2**-52) / p;
        //const a = Number(polynomial.A % BigInt(p));
        const a = -0 + FastMod(AA, p, pInv);
        const invA = modInverseSmall(a, p) | 0;
        heap32[invCache + i] = invA;
        if (invA === 0) {
          zeroInvs.push(i);
        }
        // find roots for the first polynomial:
        let b = -0 + FastMod(BB, p, pInv);
        b = bsign < 0 ? -b : b;
        const root = -0 + heap32[wheelRoots + i];
        let x1 = ((p - b) + (p - root)) * invA - offset;
        let x2 = ((p - b) + root) * invA - offset;
        x1 = mod(x1, p, pInv); // x1 mod p
        x2 = mod(x2, p, pInv); // x2 mod p
        const r1 = Math.min(x1, x2);
        const r2 = Math.max(x1, x2);
        heap32[wheelRoots1 + i] = r1;
        heap32[wheelRoots2 + i] = r2;
      }
      BPrev = 0n;
      //console.log('Bdistances.length', Bdistances.length, counternext);
      Bdistances.length = 0;
      counternext = 0;
    }
    if (BPrev === 0n) {
      BPrev = polynomial.B;
    } else {
      let d = polynomial.B - BPrev;
      BPrev = polynomial.B;
      let e = 0;
      if (d < 0n) {
        d += (polynomial.useQ2Form ? 2n : 1n) * polynomial.A;
        e = 1;
      }
      if (d < 0n || d >= polynomial.A * 2n) {
        throw new RangeError();
      }
      let v = Bdistances.indexOf(d);
      if (v === -1) {
        Bdistances.push(d);
        const dd = FastModBigInt(d < 0n ? -d : d);
        v = Bdistances.length - 1;
        const alphav = alpha + v * wheelsCount;
        for (let i = 0; i < wheelsCount; i += 1) {
          const p = -0 + (heap32[wheelSteps + i] & 134217727);
          const invA = -0 + heap32[invCache + i];
          const pInv = (1 + 2**-52) / p;
          const d = FastMod(dd, p, pInv);
          let a = (p - d) * invA;
          a = a + sieveSize; // correction
          a = mod(a, p, pInv);
          a = p - a;
          heap32[alphav + i] = a;
        }
      }
      counternext += 1;
      updateWheelsInternalNext(wheelsCount, (alpha + v * wheelsCount) << 2, wheelSteps << 2, wheelRoots1 << 2, wheelRoots2 << 2, e);
    }
    for (let j = 0; j < zeroInvs.length; j += 1) {
      const i = zeroInvs[j];
      // single root:
      // x = (2B)^-1*(-C) (mod p)
      // skip as the performance is not better
      heap32[wheelRoots1 + i] = sieveSize;
      heap32[wheelRoots2 + i] = sieveSize;
      
      if (polynomial.useQ2Form) {
        if (wheels0[i].step % 2 === 0) {
          const p = wheels0[i].step;
          const pInv = 1.0 / p;
          const a = Number(polynomial.A % BigInt(p));
          const b = Number(polynomial.B % BigInt(p));
          const c = Number(polynomial.C % BigInt(p));
          const aInv = modInverseSmall(a, p);
          const r0 = heap32[wheelRoots + i];
          for (let k = 0; k < (p === 2 ? 1 : 2); k += 1) {
            const r = k === 0 ? r0 : p - r0;
            console.assert((-b - r) % 2 === 0);
            console.assert((-b + r) % 2 === 0);
            let r1 = (-b - r) / 2 * aInv - offset;
            let r2 = (-b + r) / 2 * aInv - offset;
            r1 = r1 - Math.floor(r1 / p) * p;
            r2 = r2 - Math.floor(r2 / p) * p;
            let test1 = mod(mod(a * mod(r1 + offset, p, pInv) + b, p, pInv) * mod(r1 + offset, p, pInv) + c, p, pInv) === 0;
            let test2 = mod(mod(a * mod(r2 + offset, p, pInv) + b, p, pInv) * mod(r2 + offset, p, pInv) + c, p, pInv) === 0;
            if (test1 && test2) {
              heap32[wheelRoots1 + i] = Math.min(r1, r2);
              heap32[wheelRoots2 + i] = Math.max(r1, r2);
            }
            if (p === 2) {
              // for (let i = 0; i < p; i++) { if (polynomial.Y(i) % BigInt(p) === 0n) { console.log('root', i+offset%p); } } console.log('done');
              if (r1 !== r2) {
                const log = Math.round(1 * SCALE) | 0;
                heap32[wheelSteps + i] = 2 | (log << 27);
                wheelLogs0[i] = 1;
              } else {
                throw new Error();
              }
            }
          }
        }
      }
    }
    //...
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
    while (i < wheels0.length && lcm(p, wheels0[i].step) <= segmentSize / 4) {
      p = lcm(p, wheels0[i].step);
      i += 1;
    }
    return i;
  };
  const smallWheels = getSmallWheels();

  const copyCycle = function (array, cycleLength, limit) {
    if (typeof limit !== 'number' || typeof cycleLength !== 'number') {
      throw new TypeError();
    }
    if (limit > array.length) {
      throw new RangeError();
    }
    for (let i = cycleLength; i < limit; i += cycleLength) {
      array.copyWithin(i, 0, Math.min(limit - i, cycleLength));
    }
  };

  QuadraticSieveFactorization.smallSegmentTime = 0;
  QuadraticSieveFactorization.largeSegmentTime = 0;
  QuadraticSieveFactorization.receivingTime = 0;

  const updateSieveSegment = function (segmentStart) {
    let cycleLength = 1;
    SIEVE_SEGMENT[0] = SHIFT;
    for (let j = 0; j < smallWheels; j += 1) {
      const newCycleLength = +lcm(cycleLength, heap32[wheelSteps + j] & 134217727);
      copyCycle(SIEVE_SEGMENT, cycleLength, newCycleLength);
      cycleLength = newCycleLength;
      const p = heap32[wheelSteps + j] & 134217727;
      const log2p = heap32[wheelSteps + j] >>> 27;
      const r1 = (heap32[wheelRoots1 + j] | 0);
      if (r1 !== sieveSize) {
        for (let k = (r1 + newCycleLength - segmentStart % newCycleLength) % p; k < newCycleLength; k += p) {
          SIEVE_SEGMENT[k] = (SIEVE_SEGMENT[k] + log2p) | 0;
        }
      }
      const r2 = (heap32[wheelRoots2 + j] | 0);
      if (r2 !== sieveSize) {
        for (let k = (r2 + newCycleLength - segmentStart % newCycleLength) % p; k < newCycleLength; k += p) {
          SIEVE_SEGMENT[k] = (SIEVE_SEGMENT[k] + log2p) | 0;
        }
      }
    }
    copyCycle(SIEVE_SEGMENT, cycleLength, segmentSize);
    //for (let j = 0; j < segmentSize; j += 1) {
    //  SIEVE_SEGMENT[j] = SHIFT;
    //}
    // "Block Sieving Algorithms" by Georg Wambach and Hannes Wettig May 1995
    const m = (typeof navigator !== 'undefined' && navigator.hardwareConcurrency === 12 ? 1 : 1.5);
    const V = Math.min(0 + wheelsCount - smallWheels, Math.floor(64 * 3 * m * (N > 2**240 ? 4 : 1)));
    const S = Math.floor((1 << 15) * m);
    const t1 = performance.now();
    let subsegmentEnd = 0;
    while (subsegmentEnd + S <= segmentSize) {
      subsegmentEnd += S;
      singleBlockSieve(wheelRoots1 * 4, wheelRoots2 * 4, wheelSteps * 4, smallWheels * 4, smallWheels * 4 + V * 4, subsegmentEnd, 0);
    }
    QuadraticSieveFactorization.smallSegmentTime += performance.now() - t1;
    const t2 = performance.now();
    singleBlockSieve(wheelRoots1 * 4, wheelRoots2 * 4, wheelSteps * 4, smallWheels * 4, wheelsCount * 4, segmentSize, segmentSize);
    QuadraticSieveFactorization.largeSegmentTime += performance.now() - t2;
  };

  const smoothEntries = [];
  const smoothEntries2 = [];
  const smoothEntries3 = [];

  const findSmoothEntries = function (offset, polynomial) {
    if (typeof offset !== "number") {
      throw new TypeError();
    }
    
    const commonThreshold = (Math.round((polynomial.log2AbsY(0) - largePrimesThreshold) * SCALE + SHIFT) | 0) - 9;

    let i = 0;
    let thresholdApproximation = 0;
    while (i < segmentSize) {
      // it is slow to compute the threshold on every iteration, so trying to optimize:

      //TODO: the threshold calculation is much more simple in the Youtube videos (?)
      thresholdApproximation = useMultiplePolynomials ? commonThreshold : Math.floor((polynomial.log2AbsY(i + offset) - largePrimesThreshold) * SCALE + SHIFT + 0.5) | 0;
      const j = useMultiplePolynomials ? segmentSize : Math.min(segmentSize, thresholdApproximationInterval(polynomial, i + offset, (thresholdApproximation - SHIFT) * (1 / SCALE) + largePrimesThreshold, sieveSize) - offset);

      while (i < j) {
        if (i < j - 1) {
          const tmp = SIEVE_SEGMENT[j - 1];
          SIEVE_SEGMENT[j - 1] = MAX;
          i = findSmoothEntry(thresholdApproximation, i);
          while (thresholdApproximation > SIEVE_SEGMENT[i]) {
            i += 1;
          }
          SIEVE_SEGMENT[j - 1] = tmp;
        }
        const t = Math.round((polynomial.log2AbsY(i + offset) - largePrimesThreshold) * SCALE + SHIFT) | 0;
        if (t <= SIEVE_SEGMENT[i]) {
          smoothEntries.push(i + offset);
          smoothEntries2.push(-0 + (SIEVE_SEGMENT[i] - SHIFT) * (1 / SCALE));
        }
        i += 1;
      }
    }
  };

  function checkFactorization(x) {
    let p = 0;
    for (let n = 0; n < wheelsCount; n += 1) {
      const log2p = heap32[wheelSteps + n] >>> 27;
      const step = heap32[wheelSteps + n] & 134217727;
      for (let v = 0; v <= 1; v += 1) {
        if ((x - (v === 0 ? (heap32[wheelRoots1 + n] | 0) : (heap32[wheelRoots2 + n] | 0)) - (n < smallWheels ? 0 : segmentSize)) % step === 0) {
          if (polynomial.AFactors.indexOf(step) === -1) {
            console.log(step);
            p += log2p;
          }
        }
      }
    }
    return p;
  }

  function applyOffset(offset) {
    for (let j = 0; j < wheelsCount; j += 1) {
      const step = heap32[wheelSteps + j] & 134217727;
      let r1 = (0 + (heap32[wheelRoots + j] | 0) - baseOffsets[j] - offset) % step;
      r1 += (r1 < 0 ? step : 0);
      let r2 = (0 - (heap32[wheelRoots + j] | 0) - baseOffsets[j] - offset) % step;
      r2 += (r2 < 0 ? step : 0);
      heap32[wheelRoots1 + j] = Math.min(r1, r2);
      heap32[wheelRoots2 + j] = Math.max(r1, r2);
    }
  }

  function findPreciseSmoothEntries(offset) {
    const smoothEntries2A = new Float64Array(smoothEntries.length);
    if (smoothEntries.length > 512) {
      throw new Error();//!!!
    }
    for (let i = 0; i < smoothEntries.length; i += 1) {
      heap32[smoothEntriesX + i] = (smoothEntries[i] - offset) - sieveSize;
    }
    for (let j = 0; j < smallWheels; j += 1) {
      const step = heap32[wheelSteps + j] & 134217727;
      if (heap32[wheelRoots1 + j] !== sieveSize) {
        let x = (heap32[wheelRoots1 + j] + (0 - sieveSize) % step);
        heap32[wheelRoots1 + j] = x <= 0 ? x + step : x;
      } else {
        heap32[wheelRoots1 + j] = 0;
      }
      if (heap32[wheelRoots2 + j] !== sieveSize) {
        let x = (heap32[wheelRoots2 + j] + (0 - sieveSize) % step);
        heap32[wheelRoots2 + j] = x <= 0 ? x + step : x;
      } else {
        heap32[wheelRoots2 + j] = 0;
      }
    }
    const t = performance.now();
    const k = handleSmallWheels(wheelsCount, wheelRoots1 << 2, wheelRoots2 << 2, wheelSteps << 2, divTestA << 2, divTestB << 2, storage, smoothEntriesX << 2, (smoothEntriesX + smoothEntries.length) << 2);
    QuadraticSieveFactorization.receivingTime += performance.now() - t;

    for (let v = 0; v < k; v += 2) {
      const j = heap32[storage + v];
      const i = heap32[storage + v + 1];
      const step = heap32[wheelSteps + j] & 134217727;
      smoothEntries2A[i] += +wheelLogs0[j];
      smoothEntries3[i].push(step);
    }
    for (let i = 0; i < smoothEntries2.length; i += 1) {
      const e = Math.abs(smoothEntries2[i] - smoothEntries2A[i]);
      if (e >= 9 && e < 100) {
        console.error(e);
      }
      smoothEntries2[i] = smoothEntries2A[i];
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

          while (smoothEntries3.length < smoothEntries2.length) {
            smoothEntries3.push([]);
          }
          for (let i = 0; i < smoothEntries3.length; i += 1) {
            smoothEntries3[i].length = 0;
          }

          findPreciseSmoothEntries(offset);
        }


          //Note: separate loop over "smooth entries" is better for performance, seems
          for (let i = i1 + 1; i < smoothEntries.length; i += 1) {
            const x = smoothEntries[i];
            const value = +smoothEntries2[i];
            const threshold = +polynomial.log2AbsY(x);
            if (threshold - value <= log2B) {
              const X = polynomial.X(x);
              let Y = polynomial.Y(x, 1n, smoothEntries3[i]);
              if (Y == null) {
                // this may happen because of prime powers
                // or primes used to make "polynomial.A"
                Y = polynomial.Y(x, 1n, smoothEntries3[i].concat(zeroInvs.map(i => wheels0[i].step)));
              }
              if (Y != null) {
                i1 = i;
                return {value: new CongruenceOfsquareOfXminusYmoduloN(X, Y, N), done: false};
              } else {
                // may happen when exp2(threshold - value) is a multiplier
                console.count('wrong entry', exp2(threshold - value));
                //console.log(threshold, value, checkFactorization(x - offset));
              }
            } else if (threshold - value < 2 * log2B) {
              const p = exp2(threshold - value);
              //if (!isProbablyPrime(p)) {
                //console.debug('wrong large prime?', p);
              //}
              const c = lpStrategy(p, polynomial, x, smoothEntries3[i]);
              if (c != null) {
                i1 = i;
                QuadraticSieveFactorization.lpCounter += 1;
                return {value: c, done: false};
              }
            } else {
              console.count('too big', (threshold - value) / log2B);
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


// a/n is represented as (a,n)
function legendre(a, n) {
    if (typeof a !== 'number' || typeof n !== 'number') {
      throw new TypeError();
    }
    // from https://en.wikipedia.org/wiki/Jacobi_symbol#Implementation_in_C++ :
    a = a | 0;
    n = n | 0;
    //console.assert(n > 0 && n%2 == 1);
    //step 1
    a = (a | 0) % (n | 0);
    var t = 1;
    var r = 0;
    //step 3
    while (a !== 0) {
        //step 2
        while ((a & 1) === 0) {
            a >>= 1;
            r = n & 7;
            if (r === 3 || r === 5) {
                t = -t;
            }
        }
        //step 4
        r = n;
        n = a;
        a = r;
        if ((a & 3) === 3 && (n & 3) === 3) {
            t = -t;
        }
        a = (a | 0) % (n | 0);
    }
    return n === 1 ? t : 0;
}

function getBestMultiplier(n, primesList) {
  // https://ir.cwi.nl/pub/27839/27839.pdf

  // f (m, n) = --2 - + L g(p, mn) logp,
  const scores = new Array(150).fill(0);
  for (let m = 1; m < scores.length; m += 1) {
    scores[m] = -Math.log(m) / 2;
  }

  for (let i = 0; i < primesList.length && i < 300; i += 1) {
    const p = primesList[i];
    if (p === 2) {
      for (let m = 1; m < scores.length; m += 1) {
        const q2formExtraScore = 1;
        scores[m] += [0, 2 + q2formExtraScore, 0, 0.5, 0, 1, 0, 0.5][(m * Number(n % 8n)) % 8] * Math.log(2);
      }
    } else {
      const lnp = legendre(Number(n % BigInt(p)), p);
      const cp = 2 / (p - 1) * Math.log(p);
      for (let m = 1; m < scores.length; m += 1) {
        scores[m] += (lnp * legendre(m, p) === 1 ? cp : 0);
      }
    }
  }

  let max = 0;
  let best = 1;
  for (let m = 1; m <= scores.length; m += 1) {
    var y = +scores[m];
    if (+y > +max) {
      max = y;
      best = m;
    }
  }

  //console.log('best: ', best, 'scores: ', scores);
  return best;
}

function QuadraticSieveFactorization(N) { // N - is not a prime
  if (typeof N !== 'bigint') {
    throw new TypeError();
  }
  // https://trizenx.blogspot.com/2018/10/continued-fraction-factorization-method.html#:~:text=optimal%20value :
  // to limit memory usage during "solve" to 2GB:
  const memoryBasedLimit = Math.floor(((performance.memory || {jsHeapSizeLimit: 0}).jsHeapSizeLimit || 0) / 2**32 < 0.99 ? 2**23.5 : 2**23.75);
  const limit = Math.min(memoryBasedLimit, (1 << 25) - 1);
  const B = Math.max(Math.min(Math.floor(Math.sqrt(L(N) / (Number(N) > 2**240 ? 24 : 6))), limit), 1024);
  const primesList = primes(B);
  let k = 1n;
  k = Number(N) > 2**64 ? BigInt(getBestMultiplier(N, primesList)) : 1n;
  for (;; k += 1n) {
    if (k !== 1n) {
      console.debug('multiplier', k);
    }
    const kN = k * N;
    const primeBase = primesList.filter(p => isQuadraticResidueModuloPrime(kN, p));
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
          if (false && congruencesFound % 400 === 0) {
            console.debug('smallSegmentTime: ' + QuadraticSieveFactorization.smallSegmentTime,
                          'largeSegmentTime: ' + QuadraticSieveFactorization.largeSegmentTime,
                          'receivingTime:' + QuadraticSieveFactorization.receivingTime);
            return 1n;
          }
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
