# QuadraticSieveFactorization
Integer factorization using [Quadratic Sieve](https://en.wikipedia.org/wiki/Quadratic_sieve) algorithm in JavaScript using native BigInt

There is series of videos explaining the algorithm at https://www.youtube.com/playlist?list=PL0OUqr2O9PxLd35SgBiWIxuLgm7mYksfp .
See also links in the code.

Example
```javascript
import factorize from './QuadraticSieveFactorization.js';
console.time();
const f = factorize(2n**128n + 1n);
console.timeEnd();
// ~110ms
console.assert(f === 5704689200685129054721n || f === 59649589127497217n, f);
```
