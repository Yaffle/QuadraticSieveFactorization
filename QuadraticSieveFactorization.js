/*jshint esversion:11, bitwise:false*/

import solve from './solve.js';
import sqrtMod from './sqrtMod.js';
import wast2wasm from './wast2wasm.js';

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

function log(N) {
  const e = Math.max(Number(bitLength(N)) - 4 * 12, 0);
  const lnn = Math.log(Number(N >> BigInt(e))) + Math.log(2) * e;
  return lnn;
}

function L(N) {  // exp(sqrt(log(n)*log(log(n))))
  const lnn = log(N);
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


const wast = (strings) => String.raw({ raw: strings });

const wastCode = wast`

(module
 (type $0 (func (param i32 i32 i32 i32 i32 i32 i32 i32) (result i32)))
 (type $1 (func (param i32 i32 i32 i32 i32 i32 i32) (result i32)))
 (type $2 (func (param i32 i32) (result i32)))
 (type $3 (func (param i32 i32 i32 i32 i32 i32 i32 i32 i32) (result i32)))
 (import "env" "memory" (memory $0 0))
 (export "findPreciseSmoothEntriesInternal" (func $module/findPreciseSmoothEntriesInternal))
 (export "singleBlockSieve" (func $module/singleBlockSieve))
 (export "findSmoothEntry" (func $module/findSmoothEntry))
 (export "updateWheelsInternal" (func $module/updateWheelsInternal))
 (func $module/findPreciseSmoothEntriesInternal (param $0 i32) (param $1 i32) (param $2 i32) (param $3 i32) (param $4 i32) (param $5 i32) (param $6 i32) (param $7 i32) (result i32)
  (local $8 i32)
  (local $9 i32)
  (local $10 i32)
  (local $11 i32)
  (local $12 i32)
  (local $13 i32)
  (local.set $0
   (local.get $7)
  )
  (loop $for-loop|0
   (if
    (i32.lt_s
     (local.get $1)
     (local.get $2)
    )
    (block
     (local.set $10
      (i32.add
       (local.tee $12
        (i32.load
         (i32.shl
          (i32.add
           (local.get $1)
           (local.get $3)
          )
          (i32.const 2)
         )
        )
       )
       (local.tee $8
        (i32.sub
         (local.get $6)
         (local.tee $9
          (i32.and
           (i32.load
            (i32.shl
             (i32.add
              (local.get $1)
              (local.get $5)
             )
             (i32.const 2)
            )
           )
           (i32.const 134217727)
          )
         )
        )
       )
      )
     )
     (local.set $8
      (i32.add
       (local.get $8)
       (local.tee $13
        (i32.load
         (i32.shl
          (i32.add
           (local.get $1)
           (local.get $4)
          )
          (i32.const 2)
         )
        )
       )
      )
     )
     (local.set $11
      (i32.const 0)
     )
     (loop $do-loop|1
      (local.set $11
       (i32.or
        (i32.load8_u
         (i32.shr_s
          (local.get $10)
          (i32.const 6)
         )
        )
        (i32.or
         (local.get $11)
         (i32.load8_u
          (i32.shr_s
           (local.get $8)
           (i32.const 6)
          )
         )
        )
       )
      )
      (local.set $8
       (i32.sub
        (local.get $8)
        (local.get $9)
       )
      )
      (br_if $do-loop|1
       (i32.ge_s
        (local.tee $10
         (i32.sub
          (local.get $10)
          (local.get $9)
         )
        )
        (i32.const 0)
       )
      )
     )
     (if
      (select
       (i32.or
        (local.get $11)
        (i32.load8_u
         (i32.shr_s
          (i32.add
           (i32.and
            (i32.shr_s
             (local.get $8)
             (i32.const 31)
            )
            (local.get $9)
           )
           (local.get $8)
          )
          (i32.const 6)
         )
        )
       )
       (i32.const 0)
       (select
        (i32.const 1)
        (local.get $13)
        (local.get $12)
       )
      )
      (block
       (local.set $8
        (i32.sub
         (i32.add
          (local.get $6)
          (local.get $12)
         )
         (local.get $9)
        )
       )
       (loop $while-continue|2
        (if
         (i32.ge_s
          (local.get $8)
          (i32.const 0)
         )
         (block
          (if
           (local.tee $10
            (i32.load8_u
             (i32.shr_s
              (local.get $8)
              (i32.const 6)
             )
            )
           )
           (if
            (i32.and
             (local.get $10)
             (i32.shl
              (i32.const 1)
              (i32.and
               (i32.shr_s
                (local.get $8)
                (i32.const 3)
               )
               (i32.const 7)
              )
             )
            )
            (block
             (i32.store
              (i32.shl
               (local.get $0)
               (i32.const 2)
              )
              (local.get $1)
             )
             (i32.store
              (i32.shl
               (i32.add
                (local.get $0)
                (i32.const 1)
               )
               (i32.const 2)
              )
              (local.get $9)
             )
             (i32.store
              (i32.shl
               (i32.add
                (local.get $0)
                (i32.const 2)
               )
               (i32.const 2)
              )
              (local.get $8)
             )
             (local.set $0
              (i32.add
               (local.get $0)
               (i32.const 3)
              )
             )
            )
           )
          )
          (local.set $8
           (i32.sub
            (local.get $8)
            (local.get $9)
           )
          )
          (br $while-continue|2)
         )
        )
       )
       (local.set $8
        (i32.sub
         (i32.add
          (local.get $6)
          (local.get $13)
         )
         (local.get $9)
        )
       )
       (loop $while-continue|3
        (if
         (i32.ge_s
          (local.get $8)
          (i32.const 0)
         )
         (block
          (if
           (local.tee $10
            (i32.load8_u
             (i32.shr_s
              (local.get $8)
              (i32.const 6)
             )
            )
           )
           (if
            (i32.and
             (local.get $10)
             (i32.shl
              (i32.const 1)
              (i32.and
               (i32.shr_s
                (local.get $8)
                (i32.const 3)
               )
               (i32.const 7)
              )
             )
            )
            (block
             (i32.store
              (i32.shl
               (local.get $0)
               (i32.const 2)
              )
              (local.get $1)
             )
             (i32.store
              (i32.shl
               (i32.add
                (local.get $0)
                (i32.const 1)
               )
               (i32.const 2)
              )
              (local.get $9)
             )
             (i32.store
              (i32.shl
               (i32.add
                (local.get $0)
                (i32.const 2)
               )
               (i32.const 2)
              )
              (local.get $8)
             )
             (local.set $0
              (i32.add
               (local.get $0)
               (i32.const 3)
              )
             )
            )
           )
          )
          (local.set $8
           (i32.sub
            (local.get $8)
            (local.get $9)
           )
          )
          (br $while-continue|3)
         )
        )
       )
      )
     )
     (local.set $1
      (i32.add
       (local.get $1)
       (i32.const 1)
      )
     )
     (br $for-loop|0)
    )
   )
  )
  (i32.sub
   (local.get $0)
   (local.get $7)
  )
 )
 (func $module/singleBlockSieve (param $0 i32) (param $1 i32) (param $2 i32) (param $3 i32) (param $4 i32) (param $5 i32) (param $6 i32) (result i32)
  (local $7 i32)
  (local $8 i32)
  (local $9 i32)
  (local $10 i32)
  (local $11 i32)
  (local.set $8
   (local.get $3)
  )
  (loop $for-loop|0
   (if
    (i32.gt_s
     (local.get $4)
     (local.get $8)
    )
    (block
     (local.set $7
      (i32.load
       (i32.add
        (local.get $0)
        (local.get $8)
       )
      )
     )
     (local.set $3
      (i32.load
       (i32.add
        (local.get $1)
        (local.get $8)
       )
      )
     )
     (local.set $9
      (i32.and
       (local.tee $10
        (i32.load
         (i32.add
          (local.get $2)
          (local.get $8)
         )
        )
       )
       (i32.const 134217727)
      )
     )
     (local.set $10
      (i32.shr_u
       (local.get $10)
       (i32.const 27)
      )
     )
     (loop $while-continue|1
      (if
       (i32.lt_s
        (local.get $3)
        (local.get $5)
       )
       (block
        (local.set $11
         (i32.add
          (i32.load8_u
           (local.get $3)
          )
          (local.get $10)
         )
        )
        (i32.store8
         (local.get $7)
         (i32.add
          (i32.load8_u
           (local.get $7)
          )
          (local.get $10)
         )
        )
        (i32.store8
         (local.get $3)
         (local.get $11)
        )
        (local.set $7
         (i32.add
          (local.get $7)
          (local.get $9)
         )
        )
        (local.set $3
         (i32.add
          (local.get $3)
          (local.get $9)
         )
        )
        (br $while-continue|1)
       )
      )
     )
     (if
      (i32.gt_s
       (local.get $5)
       (local.get $7)
      )
      (block
       (i32.store8
        (local.get $7)
        (i32.add
         (i32.load8_u
          (local.get $7)
         )
         (local.get $10)
        )
       )
       (local.set $9
        (i32.add
         (local.get $7)
         (local.get $9)
        )
       )
       (local.set $7
        (local.get $3)
       )
       (local.set $3
        (local.get $9)
       )
      )
     )
     (i32.store
      (i32.add
       (local.get $0)
       (local.get $8)
      )
      (i32.sub
       (local.get $7)
       (local.get $6)
      )
     )
     (i32.store
      (i32.add
       (local.get $1)
       (local.get $8)
      )
      (i32.sub
       (local.get $3)
       (local.get $6)
      )
     )
     (local.set $8
      (i32.add
       (local.get $8)
       (i32.const 4)
      )
     )
     (br $for-loop|0)
    )
   )
  )
  (i32.const 0)
 )
 (func $module/findSmoothEntry (param $0 i32) (param $1 i32) (result i32)
  (local $2 v128)
  (local.set $2
   (i8x16.splat
    (local.get $0)
   )
  )
  (loop $while-continue|0
   (if
    (i32.eqz
     (v128.any_true
      (i8x16.ge_u
       (v128.load
        (local.get $1)
       )
       (local.get $2)
      )
     )
    )
    (block
     (local.set $1
      (i32.add
       (local.get $1)
       (i32.const 16)
      )
     )
     (br $while-continue|0)
    )
   )
  )
  (local.get $1)
 )
 (func $module/updateWheelsInternal (param $0 i32) (param $1 i32) (param $2 i32) (param $3 i32) (param $4 i32) (param $5 i32) (param $6 i32) (param $7 i32) (param $8 i32) (result i32)
  (local $9 v128)
  (local $10 v128)
  (local $11 i32)
  (local $12 v128)
  (local $13 v128)
  (local $14 v128)
  (local $15 v128)
  (local $16 v128)
  (local $17 v128)
  (local $18 v128)
  (local $19 v128)
  (local $20 v128)
  (local $21 v128)
  (local $22 v128)
  (local $23 v128)
  (local.set $12
   (f64x2.splat
    (f64.convert_i32_s
     (local.get $6)
    )
   )
  )
  (loop $for-loop|0
   (if
    (i32.lt_s
     (local.get $11)
     (i32.shl
      (local.get $0)
      (i32.const 2)
     )
    )
    (block
     (local.set $14
      (f64x2.sub
       (v128.or
        (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
        (v128.and
         (i64x2.shr_u
          (local.tee $20
           (v128.load
            (i32.add
             (local.get $2)
             (local.get $11)
            )
           )
          )
          (i32.const 0)
         )
         (v128.const i32x4 0xffffffff 0x00000000 0xffffffff 0x00000000)
        )
       )
       (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
      )
     )
     (local.set $15
      (f64x2.sub
       (v128.or
        (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
        (v128.and
         (i64x2.shr_u
          (local.tee $21
           (v128.load
            (i32.add
             (local.get $3)
             (local.get $11)
            )
           )
          )
          (i32.const 0)
         )
         (v128.const i32x4 0xffffffff 0x00000000 0xffffffff 0x00000000)
        )
       )
       (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
      )
     )
     (local.set $10
      (f64x2.sub
       (local.tee $9
        (f64x2.splat
         (f64.load
          (i32.add
           (local.tee $6
            (i32.shl
             (i32.sub
              (local.get $5)
              (i32.const 1)
             )
             (i32.const 3)
            )
           )
           (local.get $4)
          )
         )
        )
       )
       (f64x2.mul
        (f64x2.floor
         (f64x2.mul
          (local.get $9)
          (local.tee $13
           (f64x2.div
            (v128.const i32x4 0x00000001 0x3ff00000 0x00000001 0x3ff00000)
            (local.tee $16
             (f64x2.sub
              (v128.or
               (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
               (v128.and
                (i64x2.shr_u
                 (local.tee $17
                  (v128.and
                   (v128.load
                    (i32.add
                     (local.get $1)
                     (local.get $11)
                    )
                   )
                   (v128.const i32x4 0x07ffffff 0x07ffffff 0x07ffffff 0x07ffffff)
                  )
                 )
                 (i32.const 0)
                )
                (v128.const i32x4 0xffffffff 0x00000000 0xffffffff 0x00000000)
               )
              )
              (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
             )
            )
           )
          )
         )
        )
        (local.get $16)
       )
      )
     )
     (local.set $9
      (f64x2.sub
       (local.get $9)
       (f64x2.mul
        (f64x2.floor
         (f64x2.mul
          (local.get $9)
          (local.tee $22
           (f64x2.div
            (v128.const i32x4 0x00000001 0x3ff00000 0x00000001 0x3ff00000)
            (local.tee $17
             (f64x2.sub
              (v128.or
               (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
               (v128.and
                (i64x2.shr_u
                 (local.get $17)
                 (i32.const 32)
                )
                (v128.const i32x4 0xffffffff 0x00000000 0xffffffff 0x00000000)
               )
              )
              (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
             )
            )
           )
          )
         )
        )
        (local.get $17)
       )
      )
     )
     (if
      (local.get $6)
      (block
       (local.set $18
        (f64x2.sub
         (v128.const i32x4 0x00000000 0x43200000 0x00000000 0x43200000)
         (f64x2.mul
          (f64x2.floor
           (f64x2.mul
            (v128.const i32x4 0x00000000 0x43200000 0x00000000 0x43200000)
            (local.get $13)
           )
          )
          (local.get $16)
         )
        )
       )
       (local.set $23
        (f64x2.sub
         (v128.const i32x4 0x00000000 0x43200000 0x00000000 0x43200000)
         (f64x2.mul
          (f64x2.floor
           (f64x2.mul
            (v128.const i32x4 0x00000000 0x43200000 0x00000000 0x43200000)
            (local.get $22)
           )
          )
          (local.get $17)
         )
        )
       )
       (loop $do-loop|1
        (local.set $10
         (f64x2.sub
          (local.tee $10
           (f64x2.add
            (f64x2.mul
             (local.get $10)
             (local.get $18)
            )
            (local.tee $19
             (f64x2.splat
              (f64.load
               (i32.add
                (local.tee $6
                 (i32.sub
                  (local.get $6)
                  (i32.const 8)
                 )
                )
                (local.get $4)
               )
              )
             )
            )
           )
          )
          (f64x2.mul
           (f64x2.floor
            (f64x2.mul
             (local.get $10)
             (local.get $13)
            )
           )
           (local.get $16)
          )
         )
        )
        (local.set $9
         (f64x2.sub
          (local.tee $9
           (f64x2.add
            (f64x2.mul
             (local.get $9)
             (local.get $23)
            )
            (local.get $19)
           )
          )
          (f64x2.mul
           (f64x2.floor
            (f64x2.mul
             (local.get $9)
             (local.get $22)
            )
           )
           (local.get $17)
          )
         )
        )
        (br_if $do-loop|1
         (local.get $6)
        )
       )
      )
     )
     (v128.store
      (i32.add
       (local.get $7)
       (local.get $11)
      )
      (i32x4.min_s
       (local.tee $20
        (v128.or
         (i64x2.shl
          (v128.and
           (f64x2.add
            (f64x2.sub
             (local.tee $10
              (f64x2.sub
               (f64x2.mul
                (f64x2.add
                 (local.tee $18
                  (f64x2.add
                   (f64x2.sub
                    (local.get $16)
                    (local.get $10)
                   )
                   (local.get $16)
                  )
                 )
                 (local.get $14)
                )
                (local.get $15)
               )
               (local.get $12)
              )
             )
             (f64x2.mul
              (f64x2.floor
               (f64x2.mul
                (local.get $10)
                (local.get $13)
               )
              )
              (local.get $16)
             )
            )
            (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
           )
           (v128.const i32x4 0xffffffff 0x00000000 0xffffffff 0x00000000)
          )
          (i32.const 0)
         )
         (i64x2.shl
          (v128.and
           (f64x2.add
            (f64x2.sub
             (local.tee $20
              (f64x2.sub
               (f64x2.mul
                (f64x2.add
                 (local.tee $19
                  (f64x2.add
                   (f64x2.sub
                    (local.get $17)
                    (local.get $9)
                   )
                   (local.get $17)
                  )
                 )
                 (local.tee $9
                  (f64x2.sub
                   (v128.or
                    (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
                    (v128.and
                     (i64x2.shr_u
                      (local.get $20)
                      (i32.const 32)
                     )
                     (v128.const i32x4 0xffffffff 0x00000000 0xffffffff 0x00000000)
                    )
                   )
                   (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
                  )
                 )
                )
                (local.tee $10
                 (f64x2.sub
                  (v128.or
                   (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
                   (v128.and
                    (i64x2.shr_u
                     (local.get $21)
                     (i32.const 32)
                    )
                    (v128.const i32x4 0xffffffff 0x00000000 0xffffffff 0x00000000)
                   )
                  )
                  (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
                 )
                )
               )
               (local.get $12)
              )
             )
             (f64x2.mul
              (f64x2.floor
               (f64x2.mul
                (local.get $20)
                (local.get $22)
               )
              )
              (local.get $17)
             )
            )
            (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
           )
           (v128.const i32x4 0xffffffff 0x00000000 0xffffffff 0x00000000)
          )
          (i32.const 32)
         )
        )
       )
       (local.tee $9
        (v128.or
         (i64x2.shl
          (v128.and
           (f64x2.add
            (f64x2.sub
             (local.tee $14
              (f64x2.sub
               (f64x2.mul
                (f64x2.sub
                 (local.get $18)
                 (local.get $14)
                )
                (local.get $15)
               )
               (local.get $12)
              )
             )
             (f64x2.mul
              (f64x2.floor
               (f64x2.mul
                (local.get $14)
                (local.get $13)
               )
              )
              (local.get $16)
             )
            )
            (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
           )
           (v128.const i32x4 0xffffffff 0x00000000 0xffffffff 0x00000000)
          )
          (i32.const 0)
         )
         (i64x2.shl
          (v128.and
           (f64x2.add
            (f64x2.sub
             (local.tee $9
              (f64x2.sub
               (f64x2.mul
                (f64x2.sub
                 (local.get $19)
                 (local.get $9)
                )
                (local.get $10)
               )
               (local.get $12)
              )
             )
             (f64x2.mul
              (f64x2.floor
               (f64x2.mul
                (local.get $9)
                (local.get $22)
               )
              )
              (local.get $17)
             )
            )
            (v128.const i32x4 0x00000000 0x43300000 0x00000000 0x43300000)
           )
           (v128.const i32x4 0xffffffff 0x00000000 0xffffffff 0x00000000)
          )
          (i32.const 32)
         )
        )
       )
      )
     )
     (v128.store
      (i32.add
       (local.get $8)
       (local.get $11)
      )
      (i32x4.max_s
       (local.get $20)
       (local.get $9)
      )
     )
     (local.set $11
      (i32.add
       (local.get $11)
       (i32.const 16)
      )
     )
     (br $for-loop|0)
    )
   )
  )
  (i32.const 0)
 )
)

`;

let wasmModule = null;
function instantiateWasm(memorySize) {
  if (wasmModule == null) {
    const code = wast2wasm(wastCode);
    wasmModule = new WebAssembly.Module(code);
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
  const BBoffset = memorySize >> 3;
  memorySize += 256 * 8;//?

  const bufferSize = nextValidHeapSize(memorySize);
  const exports = instantiate(bufferSize);
  const findPreciseSmoothEntriesInternal = exports.findPreciseSmoothEntriesInternal;
  const singleBlockSieve = exports.singleBlockSieve;
  const findSmoothEntry = exports.findSmoothEntry;
  const updateWheelsInternal = exports.updateWheelsInternal;

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
          const X = (polynomial.A * x + polynomial.B);
          const Y = X * X - N;
          if (Y % polynomial.A !== 0n || (Y / polynomial.A) % BigInt(p) !== 0n) {
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
      let a = (proot1 + ((sieveSize - step) | 0)) | 0;
      let b = (proot2 + ((sieveSize - step) | 0)) | 0;
      //if (b < a) throw new Error();
      let found = 0;
      do {
        found = found | i32.load8_u(b >> 6) | i32.load8_u(a >> 6);
        a = (a - step) | 0;
        b = (b - step) | 0;
      } while (a >= 0);
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
                i32.store((k + 1) << 2, step);
                i32.store((k + 2) << 2, a);
                k += 3;
              }
            }
            a = (a - step) | 0;
          }
          let b = proot2 + sieveSize - step;
          while (b >= 0) {
            if (i32.load8_u(b >> 6) !== 0) {
              if ((i32.load8_u(b >> 6) & (1 << ((b >> (6 - 3)) & 7))) !== 0) {
                i32.store((k) << 2, j);
                i32.store((k + 1) << 2, step);
                i32.store((k + 2) << 2, b);
                k += 3;
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
    for (let wheel = startWheel; wheel < endWheel; wheel += 4) {
      let kpplusr = i32.load(wheelRoots1 + wheel);
      let kpplusr2 = i32.load(wheelRoots2 + wheel);
      const step = i32.load(wheelSteps + wheel) & 134217727;
      const log2p = i32.load(wheelSteps + wheel) >>> 27;
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
      i32.store(wheelRoots1 + wheel, kpplusr - s);
      i32.store(wheelRoots2 + wheel, kpplusr2 - s);
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
  export function updateWheelsInternal(wheelsCount:i32, wheelSteps:i32, wheelRoots:i32, invCache:i32, BB:i32, BBlength:i32, offset:i32, wheelRoots1:i32, wheelRoots2:i32):i32 {
    const offsetValue = f64x2.splat(f64(offset));
    for (let i = 0; i < (wheelsCount << 2); i += 16) {
      const pc = v128.and(v128.load(wheelSteps + i), i32x4.splat(134217727));
      const rootc = v128.load(wheelRoots + i);
      const invAc = v128.load(invCache + i);

      const twoTo52 = i64x2.splat(0x4330000000000000); // 2**52
      const mask = i64x2.splat(0x00000000FFFFFFFF); // 2**32 - 1

      const p_even = f64x2.sub(v128.or(twoTo52, v128.and(i64x2.shr_u(pc, 0), mask)), twoTo52);
      const p_odd = f64x2.sub(v128.or(twoTo52, v128.and(i64x2.shr_u(pc, 32), mask)), twoTo52);

      const root_even = f64x2.sub(v128.or(twoTo52, v128.and(i64x2.shr_u(rootc, 0), mask)), twoTo52);
      const root_odd = f64x2.sub(v128.or(twoTo52, v128.and(i64x2.shr_u(rootc, 32), mask)), twoTo52);

      const invA_even = f64x2.sub(v128.or(twoTo52, v128.and(i64x2.shr_u(invAc, 0), mask)), twoTo52);
      const invA_odd = f64x2.sub(v128.or(twoTo52, v128.and(i64x2.shr_u(invAc, 32), mask)), twoTo52);

      //const b = Number(polynomial.B % BigInt(p));
      const pInv_even = f64x2.div(i64x2.splat(0x3FF0000000000001), p_even); // (1 + 2**-52) / p
      const pInv_odd = f64x2.div(i64x2.splat(0x3FF0000000000001), p_odd); // (1 + 2**-52) / p
      //const b = -0 + FastMod(BB, p);

      // FastMod(BB, p):
      let j = (BBlength - 1) << 3;
      let BBj = f64x2.splat(f64.load(BB + j));
      let b_even = BBj;
      let b_odd = BBj;
      b_even = f64x2.sub(b_even, f64x2.mul(f64x2.floor(f64x2.mul(b_even, pInv_even)), p_even));
      b_odd = f64x2.sub(b_odd, f64x2.mul(f64x2.floor(f64x2.mul(b_odd, pInv_odd)), p_odd));
      if (j !== 0) {
        let x_even = i64x2.splat(0x4320000000000000); // 2**51
        let x_odd = i64x2.splat(0x4320000000000000); // 2**51
        x_even = f64x2.sub(x_even, f64x2.mul(f64x2.floor(f64x2.mul(x_even, pInv_even)), p_even));
        x_odd = f64x2.sub(x_odd, f64x2.mul(f64x2.floor(f64x2.mul(x_odd, pInv_odd)), p_odd));
        do {
          j -= 8;
          BBj = f64x2.splat(f64.load(BB + j));
          b_even = f64x2.add(f64x2.mul(b_even, x_even), BBj);
          b_odd = f64x2.add(f64x2.mul(b_odd, x_odd), BBj);
          b_even = f64x2.sub(b_even, f64x2.mul(f64x2.floor(f64x2.mul(b_even, pInv_even)), p_even));
          b_odd = f64x2.sub(b_odd, f64x2.mul(f64x2.floor(f64x2.mul(b_odd, pInv_odd)), p_odd));
        } while (j !== 0);
      }

      const e_even = f64x2.add(f64x2.sub(p_even, b_even), p_even);
      const e_odd = f64x2.add(f64x2.sub(p_odd, b_odd), p_odd);
      let x1_even = f64x2.sub(f64x2.mul(f64x2.add(e_even, root_even), invA_even), offsetValue);
      let x1_odd = f64x2.sub(f64x2.mul(f64x2.add(e_odd, root_odd), invA_odd), offsetValue);
      let x2_even = f64x2.sub(f64x2.mul(f64x2.sub(e_even, root_even), invA_even), offsetValue);
      let x2_odd = f64x2.sub(f64x2.mul(f64x2.sub(e_odd, root_odd), invA_odd), offsetValue);
      x1_even = f64x2.sub(x1_even, f64x2.mul(f64x2.floor(f64x2.mul(x1_even, pInv_even)), p_even)); // x1 mod p
      x1_odd = f64x2.sub(x1_odd, f64x2.mul(f64x2.floor(f64x2.mul(x1_odd, pInv_odd)), p_odd)); // x1 mod p
      x2_even = f64x2.sub(x2_even, f64x2.mul(f64x2.floor(f64x2.mul(x2_even, pInv_even)), p_even)); // x2 mod p
      x2_odd = f64x2.sub(x2_odd, f64x2.mul(f64x2.floor(f64x2.mul(x2_odd, pInv_odd)), p_odd)); // x2 mod p

      const x1c = v128.or(i64x2.shl(v128.and(f64x2.add(x1_even, twoTo52), mask), 0),
                          i64x2.shl(v128.and(f64x2.add(x1_odd, twoTo52), mask), 32));
      const x2c = v128.or(i64x2.shl(v128.and(f64x2.add(x2_even, twoTo52), mask), 0),
                          i64x2.shl(v128.and(f64x2.add(x2_odd, twoTo52), mask), 32));

      const r1 = i32x4.min_s(x1c, x2c);
      const r2 = i32x4.max_s(x1c, x2c);

      v128.store(wheelRoots1 + i, r1);
      v128.store(wheelRoots2 + i, r2);
    }
    return 0;
  };
  */

  const updateWheels = function (polynomial, offset) {
    offset = -0 + offset;
    //recalculate roots based on the formula:
    //proot = ((-B + root) * modInv(A, p)) % p;
    //+some optimizations to minimize bigint usage and modInverseSmall calls
    const AA = FastModBigInt(polynomial.A);
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
    updateWheelsInternal(wheelsCount, wheelSteps << 2, wheelRoots << 2, invCache << 2, BBoffset << 3, BB.length, offset, wheelRoots1 << 2, wheelRoots2 << 2);
    for (let j = 0; j < zeroInvs.length; j += 1) {
      const i = zeroInvs[j];
      // single root:
      // x = (2B)^-1*(-C) (mod p)
      // skip as the performance is not better
      heap32[wheelRoots1 + i] = sieveSize;
      heap32[wheelRoots2 + i] = sieveSize;
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
    while (i < wheels0.length && lcm(p, wheels0[i].step) <= segmentSize / 5) {
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
      for (let k = ((heap32[wheelRoots1 + j] | 0) + newCycleLength - segmentStart % newCycleLength) % p; k < newCycleLength; k += p) {
        SIEVE_SEGMENT[k] = (SIEVE_SEGMENT[k] + log2p) | 0;
      }
      for (let k = ((heap32[wheelRoots2 + j] | 0) + newCycleLength - segmentStart % newCycleLength) % p; k < newCycleLength; k += p) {
        SIEVE_SEGMENT[k] = (SIEVE_SEGMENT[k] + log2p) | 0;
      }
    }
    copyCycle(SIEVE_SEGMENT, cycleLength, segmentSize);
    //for (let j = 0; j < segmentSize; j += 1) {
    //  SIEVE_SEGMENT[j] = SHIFT;
    //}
    // "Block Sieving Algorithms" by Georg Wambach and Hannes Wettig May 1995
    const m = (typeof navigator !== 'undefined' && navigator.hardwareConcurrency === 12 ? 1 : 1.5);
    const V = Math.min(0 + wheelsCount - smallWheels, Math.floor(64 * 3 * m * (wheelsCount > 2**18 ? 2 : 1)));
    const S = Math.floor(2**15 * m - V * 4);
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
    let i = 0;
    let thresholdApproximation = 0;
    while (i < segmentSize) {
      // it is slow to compute the threshold on every iteration, so trying to optimize:

      //TODO: the threshold calculation is much more simple in the Youtube videos (?)
      thresholdApproximation = Math.floor((polynomial.log2AbsY(i + offset) - largePrimesThreshold) * SCALE + SHIFT + 0.5) | 0;
      const j = Math.min(segmentSize, thresholdApproximationInterval(polynomial, i + offset, (thresholdApproximation - SHIFT) * (1 / SCALE) + largePrimesThreshold, sieveSize) - offset);

      while (i < j) {
        if (i < j - 1 && j + 3 < segmentSize) {
          const tmp = SIEVE_SEGMENT[j - 1];
          SIEVE_SEGMENT[j - 1] = MAX;
          i = findSmoothEntry(thresholdApproximation, i);
          while (thresholdApproximation >= SIEVE_SEGMENT[i]) {
            i += 1;
          }
          SIEVE_SEGMENT[j - 1] = tmp;
        }
        if (thresholdApproximation < SIEVE_SEGMENT[i]) {
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

  function handleSmallWheels(smoothEntries2A, offset) {
    const smoothEntriesX = new Float64Array(smoothEntries.length);
    for (let i = 0; i < smoothEntries.length; i += 1) {
      smoothEntriesX[i] = -0 + (smoothEntries[i] - offset);
    }
    const A = Math.max(smallWheels, Math.min(Math.ceil(wheelsCount * 1 / 2 / smoothEntries.length), wheelsCount));
    for (let j = 0; j < A; j += 1) {
      let proot1 = heap32[wheelRoots1 + j] | 0;
      let proot2 = heap32[wheelRoots2 + j] | 0;
      const step = heap32[wheelSteps + j] & 134217727;
      const step1 = -0 + step;
      const stepInv = (1 + 2**-52) / step1;
      //const stepInv = (1 + 2**-52) / step1;
      let a = -0 + (proot1 + (j < smallWheels ? 0 : sieveSize));
      let b = -0 + (proot2 + (j < smallWheels ? 0 : sieveSize));
      a = a - Math.floor(a * stepInv) * step1;
      b = b - Math.floor(b * stepInv) * step1;
      if (proot1 !== 0 || proot2 !== 0 || j < smallWheels) {
        for (let i = 0; i < smoothEntriesX.length; i += 1) {
          const e = smoothEntriesX[i];
          const x = e - Math.floor(e * stepInv) * step1;
          if (x === a || x === b) {
            smoothEntries2A[i] += +wheelLogs0[j];
            smoothEntries3[i].push(step);
            if (proot1 === proot2) {
              smoothEntries2A[i] += +wheelLogs0[j];
              smoothEntries3[i].push(step);
            }
          }
        }
      }
    }
    return A;
  };

    
  /*
  
  */

  const set = new Uint8Array(arrayBuffer, 0, (sieveSize >> 6) + 1); // reusing sieve just to avoid some pointer arithmetic
//globalThis.countersFound = [0, 0];
  const findPreciseSmoothEntries = function (offset) {
    const smoothEntries2A = new Float64Array(smoothEntries.length);
    const A = handleSmallWheels(smoothEntries2A, offset);
    for (let i = 0; i < set.length; i += 1) {
      set[i] = 0;
    }
    for (let i = 0; i < smoothEntries.length; i += 1) {
      const e = (smoothEntries[i] - offset);
      set[e >> 6] |= (1 << ((e >> (6 - 3)) & 7));
    }
    const k = findPreciseSmoothEntriesInternal(offset, A, wheelsCount, wheelRoots1, wheelRoots2, wheelSteps, sieveSize, storage);
    for (let v = 0; v < k; v += 3) {
      const j = heap32[storage + v];
      const step = heap32[storage + v + 1];
      const a = heap32[storage + v + 2];
      const i = indexOf(smoothEntries, 0 + a + offset);
      if (i !== -1) {
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
  const scores = new Array(101).fill(0);
  for (let m = 1; m < scores.length; m += 1) {
    scores[m] = -Math.log(m) / 2;
  }

  for (let i = 0; i < primesList.length && i < 300; i += 1) {
    const p = primesList[i];
    if (p === 2) {
      for (let m = 1; m < scores.length; m += 1) {
        scores[m] += [0, 2, 0, 0.5, 0, 1, 0, 0.5][(m * Number(n % 8n)) % 8] * Math.log(2);
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