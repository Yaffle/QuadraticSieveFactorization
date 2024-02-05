function nmadd(a, b, p) {
  const at = 134217729.0 * a;
  const ahi = at - (at - a);
  const alo = a - ahi;
  const bt = 134217729.0 * b;
  const bhi = bt - (bt - b);
  const blo = b - bhi;
  return ((p - ahi * bhi) - ahi * blo - alo * bhi) - alo * blo;
}

// |a| < m/2+1, |b| < m/2+1
function modMultiplySmall53(a, b, m, mInv) {
  const p = a * b;
  const r1 = nmadd(a, b, p);
  const q = Math.floor(p * mInv + 0.5); // rounding can be replaced by floor(x + 0.5) or ceil(x - 0.5) or round(x) or rint(x)
  const r2 = nmadd(q, m, p);
  const r = r2 - r1;
  const mr = 0.0 - r;
  const rpm = r + m;
  const rmm = r - m;
  return (rmm < mr ? (rpm < mr ? rpm : r) : rmm);
}

function modPowSmall53(b, e, m, mInv) {
  let a = 1;
  while (e !== 0) {
    if (e !== Math.floor(e / 2) * 2) {
      a = modMultiplySmall53(a, b, m, mInv);
    }
    e = Math.floor(e / 2);
    b = modMultiplySmall53(b, b, m, mInv);
  }
  return a;
}

// https://en.wikipedia.org/wiki/Miller–Rabin_primality_test#Miller–Rabin_test
function isProbablyPrime(n) {
  // only Miller-Rabin test for base = 2
  if (typeof n !== 'number') {
    throw new TypeError();
  }
  if (n > 2**53) {
    throw new RangeError();
  }
  if (n < 2.0) {
    throw new RangeError();
  }
  if (n === 2.0) {
    return true;
  }
  let s = 0;
  let d = n - 1.0;
  while (d - Math.floor(d / 2.0) * 2.0 === 0.0) {
    d *= 0.5;
    s += 1;
  }
  const nInv = 1.0 / n;
  let x = modPowSmall53(2.0, d, n, nInv);//!!!
  let y = -0;
  for (let i = 0; i < s; i += 1) {
    y = modMultiplySmall53(x, x, n, nInv);
    if (y === 1.0 && x !== 1.0 && x !== -1.0) {
      return false;
    }
    x = y;
  }
  if (y !== 1.0) {
    return false;
  }
  return true;
}

export default isProbablyPrime;
