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
  return s / 2**Math.floor(Math.log2(s));
}

function exponent(a) {
  const e = Math.max(0, Number(bitLength(a)) - 1023);
  const s = Number(a >> BigInt(e));
  return e + Math.floor(Math.log2(s));
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
  return array;
}
function FastMod(array, integer) {
  const n = array.length - 1;
  let result = array[n];
  const v = integer;
  const inv = (1 + 2**-52) / v;
  result = result - Math.floor(result * inv) * v;
  if (n > 0) {
    const x = 2**51 - Math.floor(2**51 * inv) * v;
    let i = n;
    do {
      i -= 1;
      result = result * x + array[i];
      result = result - Math.floor(result * inv) * v;
    } while (i !== 0);
  }
  return result;
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
  this.AFactors = useQ2Form ? AFactors.concat([2, 2]) : AFactors;
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
  console.debug('k', k, max1);
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
          Bs[i] = Bs[i] < 0n ? A + Bs[i] : Bs[i];
          if (Bs[i] < 0n || Bs[i] >= A) throw new Error();
        }
        Bs = Bs.filter(B => B % 2n !== 0n);
        Bs.sort((a, b) => Number(BigInt(a) - BigInt(b)));
        for (let i = 0; i < Bs.length; i += 1) {
          const B = Bs[i];
          polynomials.push(new QuadraticPolynomial(A, B, N, qPrimes, useQ2Form));
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


//TODO: const vs splat (?)

const wasmCode = new Uint8Array([0, 97, 115, 109, 1, 0, 0, 0, 1, 59, 5, 96, 8, 127, 127, 127, 127, 127, 127, 127, 127, 1, 127, 96, 7, 127, 127, 127, 127, 127, 127, 127, 1, 127, 96, 2, 127, 127, 1, 127, 96, 11, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 1, 127, 96, 10, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 1, 127, 2, 15, 1, 3, 101, 110, 118, 6, 109, 101, 109, 111, 114, 121, 2, 0, 0, 3, 6, 5, 0, 1, 2, 3, 4, 7, 116, 5, 32, 102, 105, 110, 100, 80, 114, 101, 99, 105, 115, 101, 83, 109, 111, 111, 116, 104, 69, 110, 116, 114, 105, 101, 115, 73, 110, 116, 101, 114, 110, 97, 108, 0, 0, 16, 115, 105, 110, 103, 108, 101, 66, 108, 111, 99, 107, 83, 105, 101, 118, 101, 0, 1, 15, 102, 105, 110, 100, 83, 109, 111, 111, 116, 104, 69, 110, 116, 114, 121, 0, 2, 20, 117, 112, 100, 97, 116, 101, 87, 104, 101, 101, 108, 115, 73, 110, 116, 101, 114, 110, 97, 108, 0, 3, 17, 104, 97, 110, 100, 108, 101, 83, 109, 97, 108, 108, 87, 104, 101, 101, 108, 115, 0, 4, 10, 187, 19, 5, 230, 2, 1, 6, 127, 32, 7, 33, 0, 3, 64, 32, 1, 32, 2, 72, 4, 64, 32, 1, 32, 3, 106, 65, 2, 116, 40, 2, 0, 34, 12, 32, 6, 106, 32, 1, 32, 5, 106, 65, 2, 116, 40, 2, 0, 65, 255, 255, 255, 63, 113, 34, 9, 107, 33, 10, 32, 1, 32, 4, 106, 65, 2, 116, 40, 2, 0, 34, 13, 32, 6, 106, 32, 9, 107, 33, 8, 65, 0, 33, 11, 3, 64, 32, 10, 65, 0, 78, 4, 64, 32, 10, 65, 6, 117, 45, 0, 0, 32, 11, 32, 8, 65, 6, 117, 45, 0, 0, 114, 114, 33, 11, 32, 10, 32, 9, 107, 33, 10, 32, 8, 32, 9, 107, 33, 8, 12, 1, 11, 11, 32, 11, 32, 8, 65, 31, 117, 32, 9, 113, 32, 8, 106, 65, 6, 117, 45, 0, 0, 114, 65, 0, 65, 1, 32, 13, 32, 12, 27, 27, 4, 64, 32, 6, 32, 12, 106, 32, 9, 107, 33, 8, 3, 64, 32, 8, 65, 0, 78, 4, 64, 32, 8, 65, 6, 117, 45, 0, 0, 34, 10, 4, 64, 32, 10, 65, 1, 32, 8, 65, 3, 117, 65, 7, 113, 116, 113, 4, 64, 32, 0, 65, 2, 116, 32, 1, 54, 2, 0, 32, 0, 65, 1, 106, 65, 2, 116, 32, 8, 54, 2, 0, 32, 0, 65, 2, 106, 33, 0, 11, 11, 32, 8, 32, 9, 107, 33, 8, 12, 1, 11, 11, 32, 6, 32, 13, 106, 32, 9, 107, 33, 8, 3, 64, 32, 8, 65, 0, 78, 4, 64, 32, 8, 65, 6, 117, 45, 0, 0, 34, 10, 4, 64, 32, 10, 65, 1, 32, 8, 65, 3, 117, 65, 7, 113, 116, 113, 4, 64, 32, 0, 65, 2, 116, 32, 1, 54, 2, 0, 32, 0, 65, 1, 106, 65, 2, 116, 32, 8, 54, 2, 0, 32, 0, 65, 2, 106, 33, 0, 11, 11, 32, 8, 32, 9, 107, 33, 8, 12, 1, 11, 11, 11, 32, 1, 65, 1, 106, 33, 1, 12, 1, 11, 11, 32, 0, 32, 7, 107, 11, 217, 1, 1, 4, 127, 32, 0, 32, 3, 106, 33, 7, 32, 1, 32, 3, 106, 33, 8, 32, 2, 32, 3, 106, 33, 3, 32, 2, 32, 4, 106, 33, 9, 3, 64, 32, 3, 32, 9, 71, 4, 64, 32, 7, 40, 2, 0, 33, 1, 32, 8, 40, 2, 0, 33, 0, 32, 3, 40, 2, 0, 34, 4, 65, 255, 255, 255, 63, 113, 33, 2, 32, 4, 65, 27, 118, 33, 4, 3, 64, 32, 0, 32, 5, 72, 4, 64, 32, 0, 45, 0, 0, 32, 4, 106, 33, 10, 32, 1, 32, 1, 45, 0, 0, 32, 4, 106, 58, 0, 0, 32, 0, 32, 10, 58, 0, 0, 32, 1, 32, 2, 106, 33, 1, 32, 0, 32, 2, 106, 33, 0, 12, 1, 11, 11, 32, 1, 32, 5, 72, 4, 64, 32, 1, 32, 1, 45, 0, 0, 32, 4, 106, 58, 0, 0, 32, 1, 32, 2, 106, 33, 2, 32, 0, 33, 1, 32, 2, 33, 0, 11, 32, 7, 32, 1, 32, 6, 107, 54, 2, 0, 32, 8, 32, 0, 32, 6, 107, 54, 2, 0, 32, 7, 65, 4, 106, 33, 7, 32, 8, 65, 4, 106, 33, 8, 32, 3, 65, 4, 106, 33, 3, 12, 1, 11, 11, 65, 0, 11, 40, 1, 1, 123, 32, 0, 253, 15, 33, 2, 3, 64, 32, 1, 253, 0, 4, 0, 32, 2, 253, 44, 253, 83, 69, 4, 64, 32, 1, 65, 16, 106, 33, 1, 12, 1, 11, 11, 32, 1, 11, 134, 8, 2, 14, 123, 1, 127, 32, 6, 183, 154, 253, 20, 33, 13, 3, 64, 32, 25, 32, 0, 65, 2, 116, 72, 4, 64, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 32, 2, 32, 25, 106, 253, 0, 4, 0, 34, 22, 253, 12, 255, 255, 255, 255, 0, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 253, 78, 253, 80, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 241, 1, 33, 16, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 32, 3, 32, 25, 106, 253, 0, 4, 0, 34, 23, 253, 12, 255, 255, 255, 255, 0, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 253, 78, 253, 80, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 241, 1, 33, 17, 32, 5, 65, 1, 107, 65, 3, 116, 34, 6, 32, 4, 106, 43, 3, 0, 253, 20, 34, 11, 32, 9, 32, 25, 106, 253, 0, 4, 0, 34, 14, 253, 242, 1, 253, 117, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 32, 1, 32, 25, 106, 253, 0, 4, 0, 253, 12, 255, 255, 255, 7, 255, 255, 255, 7, 255, 255, 255, 7, 255, 255, 255, 7, 253, 78, 34, 19, 253, 12, 255, 255, 255, 255, 0, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 253, 78, 253, 80, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 241, 1, 34, 18, 32, 11, 253, 136, 2, 33, 12, 32, 11, 32, 10, 32, 25, 106, 253, 0, 4, 0, 34, 15, 253, 242, 1, 253, 117, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 32, 19, 65, 32, 253, 205, 1, 253, 80, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 241, 1, 34, 19, 32, 11, 253, 136, 2, 33, 11, 32, 6, 4, 64, 253, 12, 0, 0, 0, 0, 0, 0, 32, 67, 0, 0, 0, 0, 0, 0, 32, 67, 32, 14, 253, 242, 1, 253, 117, 32, 18, 253, 12, 0, 0, 0, 0, 0, 0, 32, 67, 0, 0, 0, 0, 0, 0, 32, 67, 253, 136, 2, 33, 20, 253, 12, 0, 0, 0, 0, 0, 0, 32, 67, 0, 0, 0, 0, 0, 0, 32, 67, 32, 15, 253, 242, 1, 253, 117, 32, 19, 253, 12, 0, 0, 0, 0, 0, 0, 32, 67, 0, 0, 0, 0, 0, 0, 32, 67, 253, 136, 2, 33, 24, 3, 64, 32, 12, 32, 20, 32, 6, 65, 8, 107, 34, 6, 32, 4, 106, 43, 3, 0, 253, 20, 34, 21, 253, 135, 2, 34, 12, 32, 14, 253, 242, 1, 253, 117, 32, 18, 32, 12, 253, 136, 2, 33, 12, 32, 11, 32, 24, 32, 21, 253, 135, 2, 34, 11, 32, 15, 253, 242, 1, 253, 117, 32, 19, 32, 11, 253, 136, 2, 33, 11, 32, 6, 13, 0, 11, 11, 32, 7, 32, 25, 106, 32, 18, 32, 12, 253, 241, 1, 34, 20, 32, 18, 32, 16, 253, 241, 1, 253, 240, 1, 32, 17, 32, 13, 253, 135, 2, 34, 12, 32, 14, 253, 242, 1, 253, 117, 32, 18, 32, 12, 253, 136, 2, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 240, 1, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 81, 32, 19, 32, 11, 253, 241, 1, 34, 21, 32, 19, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 32, 22, 65, 32, 253, 205, 1, 253, 80, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 241, 1, 34, 11, 253, 241, 1, 253, 240, 1, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 32, 23, 65, 32, 253, 205, 1, 253, 80, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 241, 1, 34, 12, 32, 13, 253, 135, 2, 34, 22, 32, 15, 253, 242, 1, 253, 117, 32, 19, 32, 22, 253, 136, 2, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 240, 1, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 81, 65, 32, 253, 203, 1, 253, 80, 34, 22, 32, 20, 32, 16, 253, 240, 1, 32, 17, 32, 13, 253, 135, 2, 34, 16, 32, 14, 253, 242, 1, 253, 117, 32, 18, 32, 16, 253, 136, 2, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 240, 1, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 81, 32, 21, 32, 11, 253, 240, 1, 32, 12, 32, 13, 253, 135, 2, 34, 11, 32, 15, 253, 242, 1, 253, 117, 32, 19, 32, 11, 253, 136, 2, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 240, 1, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 81, 65, 32, 253, 203, 1, 253, 80, 34, 11, 253, 182, 1, 253, 11, 4, 0, 32, 8, 32, 25, 106, 32, 22, 32, 11, 253, 184, 1, 253, 11, 4, 0, 32, 25, 65, 16, 106, 33, 25, 12, 1, 11, 11, 65, 0, 11, 196, 6, 3, 9, 127, 10, 123, 2, 124, 32, 4, 183, 33, 30, 32, 5, 33, 10, 3, 64, 32, 13, 32, 0, 65, 2, 116, 72, 4, 64, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 32, 1, 32, 13, 106, 253, 0, 4, 0, 34, 19, 253, 12, 255, 255, 255, 255, 0, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 253, 78, 253, 80, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 241, 1, 32, 30, 253, 20, 34, 25, 253, 240, 1, 34, 20, 32, 8, 32, 13, 106, 253, 0, 4, 0, 34, 24, 253, 242, 1, 253, 117, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 32, 3, 32, 13, 106, 253, 0, 4, 0, 253, 12, 255, 255, 255, 7, 255, 255, 255, 7, 255, 255, 255, 7, 255, 255, 255, 7, 253, 78, 34, 21, 253, 12, 255, 255, 255, 255, 0, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 253, 78, 253, 80, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 241, 1, 34, 23, 32, 20, 253, 136, 2, 33, 20, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 32, 19, 65, 32, 253, 205, 1, 253, 80, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 241, 1, 32, 25, 253, 240, 1, 34, 19, 32, 9, 32, 13, 106, 253, 0, 4, 0, 34, 22, 253, 242, 1, 253, 117, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 32, 21, 65, 32, 253, 205, 1, 253, 80, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 241, 1, 34, 21, 32, 19, 253, 136, 2, 33, 19, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 32, 2, 32, 13, 106, 253, 0, 4, 0, 34, 26, 253, 12, 255, 255, 255, 255, 0, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 253, 78, 253, 80, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 241, 1, 32, 25, 253, 240, 1, 34, 27, 32, 24, 253, 242, 1, 253, 117, 32, 23, 32, 27, 253, 136, 2, 33, 27, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 32, 26, 65, 32, 253, 205, 1, 253, 80, 253, 12, 0, 0, 0, 0, 0, 0, 48, 67, 0, 0, 0, 0, 0, 0, 48, 67, 253, 241, 1, 32, 25, 253, 240, 1, 34, 25, 32, 22, 253, 242, 1, 253, 117, 32, 21, 32, 25, 253, 136, 2, 33, 25, 32, 6, 33, 11, 3, 64, 32, 7, 32, 11, 74, 4, 64, 32, 11, 43, 3, 0, 34, 29, 253, 20, 34, 26, 32, 24, 253, 242, 1, 253, 117, 32, 23, 32, 26, 253, 136, 2, 34, 28, 32, 20, 253, 71, 32, 26, 32, 22, 253, 242, 1, 253, 117, 32, 21, 32, 26, 253, 136, 2, 34, 26, 32, 19, 253, 71, 253, 80, 32, 28, 32, 27, 253, 71, 32, 26, 32, 25, 253, 71, 253, 80, 253, 80, 253, 83, 4, 64, 32, 29, 252, 2, 33, 17, 32, 13, 33, 12, 3, 64, 32, 12, 32, 0, 65, 2, 116, 72, 32, 12, 32, 13, 65, 16, 106, 72, 113, 4, 64, 32, 3, 32, 12, 106, 40, 2, 0, 65, 255, 255, 255, 63, 113, 33, 14, 65, 1, 32, 2, 32, 12, 106, 40, 2, 0, 34, 16, 32, 1, 32, 12, 106, 40, 2, 0, 34, 15, 27, 4, 64, 32, 17, 32, 4, 32, 15, 106, 107, 32, 14, 111, 4, 127, 32, 17, 32, 4, 32, 16, 106, 107, 32, 14, 111, 5, 65, 0, 11, 69, 4, 64, 32, 10, 65, 2, 116, 32, 12, 65, 2, 117, 34, 14, 54, 2, 0, 32, 10, 65, 1, 106, 65, 2, 116, 32, 11, 32, 6, 107, 65, 3, 117, 34, 18, 54, 2, 0, 32, 10, 65, 2, 106, 33, 10, 32, 15, 32, 16, 70, 4, 64, 32, 10, 65, 2, 116, 32, 14, 54, 2, 0, 32, 10, 65, 1, 106, 65, 2, 116, 32, 18, 54, 2, 0, 32, 10, 65, 2, 106, 33, 10, 11, 11, 11, 32, 12, 65, 4, 106, 33, 12, 12, 1, 11, 11, 11, 32, 11, 65, 8, 106, 33, 11, 12, 1, 11, 11, 32, 13, 65, 16, 106, 33, 13, 12, 1, 11, 11, 32, 10, 32, 5, 107, 11]);

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
      sieveSize1 >>= 1;
    }
  }
  //console.debug('sieveSize1', Math.log2(sieveSize1));
  
  const q = Math.ceil(sieveSize1 / (typeof navigator !== 'undefined' && navigator.hardwareConcurrency === 12 ? 2.75 * 2**20 : 6 * 2**20));
  console.debug('q', q);
  const segmentSize = Math.ceil(Math.ceil(sieveSize1 / q) / 48) * 48;
  const sieveSize = segmentSize * q;
  const SHIFT = 0;
  const MAX = 255;
  const SCALE = 2**0;//TODO:

  const log2B = Math.log2(primes.length === 0 ? Math.sqrt(2) : +primes[primes.length - 1]);
  const largePrimesThreshold = log2B + Math.min(Math.log2(300), log2B);
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
  memorySize += memorySize % 8;
  const stepInvsEven = memorySize >> 3;
  memorySize += wheelsCount / 2 * 8;
  const stepInvsOdd = memorySize >> 3;
  memorySize += wheelsCount / 2 * 8;
  const BBoffset = memorySize >> 3;
  memorySize += 256 * 8;//?
  const smoothEntriesX = memorySize >> 3;
  memorySize += 512 * 4;//TODO: what size?

  const bufferSize = nextValidHeapSize(memorySize);
  const exports = instantiate(bufferSize);
  const findPreciseSmoothEntriesInternal = exports.findPreciseSmoothEntriesInternal;
  const singleBlockSieve = exports.singleBlockSieve;
  const findSmoothEntry = exports.findSmoothEntry;
  const updateWheelsInternal = exports.updateWheelsInternal;
  const handleSmallWheels = exports.handleSmallWheels;

  const arrayBuffer = exports.memory.buffer;
  const SIEVE_SEGMENT = new Uint8Array(arrayBuffer);
  const heap32 = new Int32Array(arrayBuffer);
  const f64array = new Float64Array(arrayBuffer);

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
    f64array[(i % 2 === 0 ? stepInvsEven : stepInvsOdd) + Math.floor(i / 2)] = (1.0 + 2**-52) / +w.step;
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

  export function findPreciseSmoothEntriesInternal(offset:i32, A:i32, wheelsCount:i32, wheelRoots1:i32, wheelRoots2:i32, wheelSteps:i32, sieveSize:i32, storage:i32):i32 {
    let k = storage;
    for (let j = A; j < wheelsCount; j += 1) {
      const proot1 = i32.load((wheelRoots1 + j) << 2);
      const proot2 = i32.load((wheelRoots2 + j) << 2);
      const step = i32.load((wheelSteps + j) << 2) & 134217727;
      // "rotate" the wheel instead:
      let a = proot1 + sieveSize - step;
      let b = proot2 + sieveSize - step;
      //if (b < a) throw new Error();
      let found = 0;
      while (a >= 0) {
        found = found | i32.load8_u(b >> 6) | i32.load8_u(a >> 6);
        a = (a - step) | 0;
        b = (b - step) | 0;
      }
      b = (b + ((b >> 31) & step)) | 0;
      found = found | i32.load8_u(b >> 6);

      //if (b >= 0) throw new Error();
      //countersFound[found ? 1 : 0] += 1;
      if (found !== 0) {
        if (proot1 !== 0 || proot2 !== 0) {
          let a = proot1 + sieveSize - step;
          while (a >= 0) {
            if (i32.load8_u(a >> 6) !== 0) {
              if ((i32.load8_u(a >> 6) & (1 << ((a >> (6 - 3)) & 7))) !== 0) {
                i32.store((k) << 2, j);
                i32.store((k + 1) << 2, a);
                k += 2;
              }
            }
            a = (a - step) | 0;
          }
          let b = proot2 + sieveSize - step;
          while (b >= 0) {
            if (i32.load8_u(b >> 6) !== 0) {
              if ((i32.load8_u(b >> 6) & (1 << ((b >> (6 - 3)) & 7))) !== 0) {
                i32.store((k) << 2, j);
                i32.store((k + 1) << 2, b);
                k += 2;
              }
            }
            b = (b - step) | 0;
          }
        }
      }
    }
    return k - storage;
  };
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
  function i32x4_to_f64x2(x:v128):v128 {
    const twoTo52 = i64x2.splat(0x4330000000000000); // 2**52
    return f64x2.sub(v128.or(twoTo52, x), twoTo52);
  }
  function f64x2_to_i32x4(x:v128):v128 {
    const twoTo52 = i64x2.splat(0x4330000000000000); // 2**52
    return v128.xor(f64x2.add(x, twoTo52), twoTo52);
  }
  function madd(a:v128, b:v128, c:v128):v128 {
    return f64x2.relaxed_madd(a, b, c);
    //return f64x2.add(f64x2.mul(a, b), c);
  }
  function mod(x:v128, m:v128, mInv:v128):v128 {
    return f64x2.relaxed_nmadd(f64x2.floor(f64x2.mul(x, mInv)), m, x);
    //return f64x2.sub(x, f64x2.mul(f64x2.floor(f64x2.mul(x, mInv)), m));
  }
  export function updateWheelsInternal(wheelsCount:i32, wheelSteps:i32, wheelRoots:i32, invCache:i32, BB:i32, BBlength:i32, offset:i32, wheelRoots1:i32, wheelRoots2:i32, stepInvsEven:i32, stepInvsOdd:i32):i32 {
    const offsetValue = f64x2.splat(-f64(offset));
    for (let i = 0; i < (wheelsCount << 2); i += 16) {
      const pc = v128.and(v128.load(wheelSteps + i), i32x4.splat(134217727));
      const rootc = v128.load(wheelRoots + i);
      const invAc = v128.load(invCache + i);

      const mask = i64x2.splat(0x00000000FFFFFFFF); // 2**32 - 1

      const p_even = i32x4_to_f64x2(v128.and(pc, mask));
      const p_odd = i32x4_to_f64x2(i64x2.shr_u(pc, 32));

      const root_even = i32x4_to_f64x2(v128.and(rootc, mask));
      const root_odd = i32x4_to_f64x2(i64x2.shr_u(rootc, 32));

      const invA_even = i32x4_to_f64x2(v128.and(invAc, mask));
      const invA_odd = i32x4_to_f64x2(i64x2.shr_u(invAc, 32));

      //const b = Number(polynomial.B % BigInt(p));
      const pInv_even = v128.load(stepInvsEven + i); // (1 + 2**-52) / p
      const pInv_odd = v128.load(stepInvsOdd + i); // (1 + 2**-52) / p

      // FastMod(BB, p):
      let j = (BBlength - 1) << 3;
      let BBj = f64x2.splat(f64.load(BB + j));
      let b_even = BBj;
      let b_odd = BBj;
      b_even = mod(b_even, p_even, pInv_even);
      b_odd = mod(b_odd, p_odd, pInv_odd);

      let x_even = i64x2.splat(0x4320000000000000); // 2**51
      let x_odd = i64x2.splat(0x4320000000000000); // 2**51
      x_even = mod(x_even, p_even, pInv_even);
      x_odd = mod(x_odd, p_odd, pInv_odd);
      if (j !== 0) {
        do {
          j -= 8;
          BBj = f64x2.splat(f64.load(BB + j));
          b_even = madd(b_even, x_even, BBj);
          b_odd = madd(b_odd, x_odd, BBj);
          b_even = mod(b_even, p_even, pInv_even);
          b_odd = mod(b_odd, p_odd, pInv_odd);
        } while (j !== 0);
      }
      b_even = f64x2.sub(p_even, b_even);
      b_odd = f64x2.sub(p_odd, b_odd);

      let x1_even = madd(f64x2.add(b_even, f64x2.sub(p_even, root_even)), invA_even, offsetValue);
      let x1_odd = madd(f64x2.add(b_odd, f64x2.sub(p_odd, root_odd)), invA_odd, offsetValue);
      let x2_even = madd(f64x2.add(b_even, root_even), invA_even, offsetValue);
      let x2_odd = madd(f64x2.add(b_odd, root_odd), invA_odd, offsetValue);

      x1_even = mod(x1_even, p_even, pInv_even); // x1 mod p
      x1_odd = mod(x1_odd, p_odd, pInv_odd); // x1 mod p
      x2_even = mod(x2_even, p_even, pInv_even); // x2 mod p
      x2_odd = mod(x2_odd, p_odd, pInv_odd); // x2 mod p

      const x1c = v128.or(f64x2_to_i32x4(x1_even),
                          i64x2.shl(f64x2_to_i32x4(x1_odd), 32));
      const x2c = v128.or(f64x2_to_i32x4(x2_even),
                          i64x2.shl(f64x2_to_i32x4(x2_odd), 32));

      const r1 = i32x4.min_s(x1c, x2c);
      const r2 = i32x4.max_s(x1c, x2c);

      v128.store(wheelRoots1 + i, r1);
      v128.store(wheelRoots2 + i, r2);
    }
    return 0;
  };
  export function handleSmallWheels(A:i32, wheelRoots1:i32, wheelRoots2:i32, wheelSteps:i32, sieveSize:i32, storage:i32, smoothEntriesXStart:i32, smoothEntriesXEnd:i32, stepInvsEven:i32, stepInvsOdd:i32):i32 {
    const sieveSizef64 = f64(sieveSize);
    let k = storage;
    for (let j = 0; j < (A << 2); j += 16) {
      const proot1c = v128.load(wheelRoots1 + j);
      const proot2c = v128.load(wheelRoots2 + j);
      const pc = v128.and(v128.load(wheelSteps + j), i32x4.splat(134217727));

      const mask = i64x2.splat(0x00000000FFFFFFFF); // 2**32 - 1

      const p_even = i32x4_to_f64x2(v128.and(pc, mask));
      const p_odd = i32x4_to_f64x2(i64x2.shr_u(pc, 32));
      
      const proot1_even = i32x4_to_f64x2(v128.and(proot1c, mask));
      const proot1_odd = i32x4_to_f64x2(i64x2.shr_u(proot1c, 32));

      const proot2_even = i32x4_to_f64x2(v128.and(proot2c, mask));
      const proot2_odd = i32x4_to_f64x2(i64x2.shr_u(proot2c, 32));

      const pInv_even = v128.load(stepInvsEven + j); // (1 + 2**-52) / p
      const pInv_odd = v128.load(stepInvsOdd + j); // (1 + 2**-52) / p

      const sieveSizex2 = f64x2.splat(sieveSizef64);
      let a_even = f64x2.add(proot1_even, sieveSizex2);
      let a_odd = f64x2.add(proot1_odd, sieveSizex2);
      let b_even = f64x2.add(proot2_even, sieveSizex2);
      let b_odd = f64x2.add(proot2_odd, sieveSizex2);
      a_even = mod(a_even, p_even, pInv_even);
      a_odd = mod(a_odd, p_odd, pInv_odd);
      b_even = mod(b_even, p_even, pInv_even);
      b_odd = mod(b_odd, p_odd, pInv_odd);

      for (let i = smoothEntriesXStart; i < smoothEntriesXEnd; i += 8) {
        const e = f64x2.splat(f64.load(i));
        const x_even = mod(e, p_even, pInv_even);
        const x_odd = mod(e, p_odd, pInv_odd);
        if (v128.any_true(v128.or(v128.or(f64x2.eq(x_even, a_even), f64x2.eq(x_odd, a_odd)),
                                  v128.or(f64x2.eq(x_even, b_even), f64x2.eq(x_odd, b_odd))))) {
          const e = i32(f64.load(i));
          for (let j1 = j; j1 < j + 16 && j1 < (A << 2); j1 += 4) {
            const proot1 = i32.load(wheelRoots1 + j1);
            const proot2 = i32.load(wheelRoots2 + j1);
            const step = i32.load(wheelSteps + j1) & 134217727;
            if (proot1 !== 0 || proot2 !== 0) {
              if ((e - (proot1 + sieveSize)) % step == 0 ||
                  (e - (proot2 + sieveSize)) % step == 0) {
                i32.store((k) << 2, j1 >> 2);
                i32.store((k + 1) << 2, (i - smoothEntriesXStart) >> 3);
                k += 2;
                if (proot1 === proot2) {
                  i32.store((k) << 2, j1 >> 2);
                  i32.store((k + 1) << 2, (i - smoothEntriesXStart) >> 3);
                  k += 2;
                }
              }
            }
          }
        }
      }
    }
    return k - storage;
  };

  */

  function mod(a, m) {
    return a - Math.floor(a / m) * m;
  }

  const updateWheels = function (polynomial, offset) {
    offset = -0 + offset;
    //recalculate roots based on the formula:
    //proot = ((-B + root) * modInv(A, p)) % p;
    //+some optimizations to minimize bigint usage and modInverseSmall calls
    const AA = FastModBigInt((polynomial.useQ2Form ? 2n : 1n) * polynomial.A);
    const BB = FastModBigInt(polynomial.B);
    const useCache = BigInt(polynomial.A) === BigInt(invCacheKey);
    if (!useCache) {
      zeroInvs.length = 0;
      for (let i = 0; i < wheelsCount; i += 1) {
        const p = -0 + (heap32[wheelSteps + i] & 134217727);
        //const a = Number(polynomial.A % BigInt(p));
        const a = -0 + FastMod(AA, p);
        const invA = modInverseSmall(a, p) | 0;
        heap32[invCache + i] = invA;
        if (invA === 0) {
          zeroInvs.push(i);
        }
      }
    }
    for (let i = 0; i < BB.length; i += 1) {
      f64array[BBoffset + i] = BB[i];
    }
    updateWheelsInternal(wheelsCount, wheelSteps << 2, wheelRoots << 2, invCache << 2, BBoffset << 3, BB.length, offset, wheelRoots1 << 2, wheelRoots2 << 2, stepInvsEven << 3, stepInvsOdd << 3);
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
            let test1 = mod(mod(a * mod(r1 + offset, p) + b, p) * mod(r1 + offset, p) + c, p) === 0;
            let test2 = mod(mod(a * mod(r2 + offset, p) + b, p) * mod(r2 + offset, p) + c, p) === 0;
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




  const updateSieveSegment = function (segmentStart) {
    if (typeof segmentStart !== 'number') {
      throw new TypeError();
    }
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
    const V = Math.min(0 + wheelsCount - smallWheels, Math.floor(64 * 3 * m * (wheelsCount > 2**16 ? 4 : 1)));
    const S = (1 << 15);
    let subsegmentEnd = 0;
    while (subsegmentEnd + S <= segmentSize) {
      subsegmentEnd += S;
      singleBlockSieve(wheelRoots1 * 4, wheelRoots2 * 4, wheelSteps * 4, smallWheels * 4, smallWheels * 4 + V * 4, subsegmentEnd, 0);
    }
    singleBlockSieve(wheelRoots1 * 4, wheelRoots2 * 4, wheelSteps * 4, smallWheels * 4, wheelsCount * 4, segmentSize, segmentSize);
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

globalThis.countersx = [0, 0, 0, 0];



  const set = new Uint8Array(arrayBuffer, 0, (sieveSize >> 6) + 1); // reusing sieve just to avoid some pointer arithmetic
//globalThis.countersFound = [0, 0];
  const findPreciseSmoothEntries = function (offset) {
    const smoothEntries2A = new Float64Array(smoothEntries.length);
    if (smoothEntries.length > 512) {
      throw new Error();//!!!
    }
    for (let i = 0; i < smoothEntries.length; i += 1) {
      f64array[smoothEntriesX + i] = -0 + (smoothEntries[i] - offset);
    }
    for (let i = smoothEntries.length; i < smoothEntries.length + 1; i += 1) {
      f64array[smoothEntriesX + i] = f64array[smoothEntriesX + (smoothEntries.length - 1)];
    }
    let A = Math.max(smallWheels, Math.min(Math.ceil(wheelsCount * 1.5 / smoothEntries.length), wheelsCount));
    A += (4 - A % 4) % 4;
    for (let j = 0; j < smallWheels; j += 1) {
      const step = heap32[wheelSteps + j] & 134217727;
      if (heap32[wheelRoots1 + j] !== sieveSize) {
        heap32[wheelRoots1 + j] = heap32[wheelRoots1 + j] + (0 - sieveSize) % step + step;
      } else {
        heap32[wheelRoots1 + j] = 0;
      }
      if (heap32[wheelRoots2 + j] !== sieveSize) {
        heap32[wheelRoots2 + j] = heap32[wheelRoots2 + j] + (0 - sieveSize) % step + step;
      } else {
        heap32[wheelRoots2 + j] = 0;
      }
    }
    const k1 = handleSmallWheels(A, wheelRoots1 << 2, wheelRoots2 << 2, wheelSteps << 2, sieveSize, storage, smoothEntriesX << 3, (smoothEntriesX + smoothEntries.length) << 3, stepInvsEven << 3, stepInvsOdd << 3);
    for (let i = 0; i < set.length; i += 4) {
      heap32[i >> 2] = 0;
    }
    for (let i = 0; i < smoothEntries.length; i += 1) {
      const e = (smoothEntries[i] - offset);
      set[e >> 6] |= (1 << ((e >> (6 - 3)) & 7));
    }
    const k = k1 + findPreciseSmoothEntriesInternal(offset, A, wheelsCount, wheelRoots1, wheelRoots2, wheelSteps, sieveSize, storage + k1);
    for (let v = 0; v < k; v += 2) {
      const j = heap32[storage + v];
      const a = heap32[storage + v + 1];
      const i = v < k1 ? a : indexOf(smoothEntries, 0 + a + offset);
      if (i !== -1) {
        const step = heap32[wheelSteps + j] & (2**24 - 1);
        smoothEntries2A[i] += +wheelLogs0[j];
        smoothEntries3[i].push(step);
      }
    }
    for (let i = 0; i < smoothEntries2.length; i += 1) {
      const e = Math.abs(smoothEntries2[i] - smoothEntries2A[i]);
      if (e >= 9 && e < 100) {
        console.error(e);
      }
      smoothEntries2[i] = smoothEntries2A[i];
    }
  };

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
            if (threshold - value < 1) {
              const X = polynomial.X(x);
              const Y = polynomial.Y(x, 1n, smoothEntries3[i]);
              if (Y != null) {
                i1 = i;
                return {value: new CongruenceOfsquareOfXminusYmoduloN(X, Y, N), done: false};
              } else {
                console.count('?');
                //console.log(threshold, value, checkFactorization(x - offset));
              }
            } else {
              if (threshold - value < log2B + log2B) {
                const p = exp2(threshold - value);
                const c = lpStrategy(p, polynomial, x, smoothEntries3[i]);
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

  //8.9848939430165
  //console.log('best: ', best, 'scores: ', scores);
  if (best !== 1) {
    console.debug('multiplier', best);
  }
  return best;
}

function QuadraticSieveFactorization(N) { // N - is not a prime
  if (typeof N !== 'bigint') {
    throw new TypeError();
  }
  // https://trizenx.blogspot.com/2018/10/continued-fraction-factorization-method.html#:~:text=optimal%20value :
  // to limit memory usage during "solve" to 2GB:
  const limit1 = Math.floor(2**23.5);
  const limit = Math.min(limit1, (1 << 25) - 1);

  const B = Math.max(Math.min(Math.floor(Math.sqrt(L(N) / (Number(N) > 2**240 ? 24 : 6))), limit), 1024);
  const primesList = primes(B);
  let k = 1n;
  k = Number(N) > 2**64 ? BigInt(getBestMultiplier(N, primesList)) : 1n;
  for (;; k += 1n) {
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
          const now = +Date.now();
          if (congruencesFound === 150) {
            //return 1n;
          }
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