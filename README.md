# QuadraticSieveFactorization
Integer factorization using [Quadratic Sieve](https://en.wikipedia.org/wiki/Quadratic_sieve) algorithm in JavaScript using native BigInt

There is series of videos explaining the algorithm at https://www.youtube.com/playlist?list=PL0OUqr2O9PxLd35SgBiWIxuLgm7mYksfp .

Useful info can also be found at https://www.rieselprime.de/ziki/Self-initializing_quadratic_sieve and at https://www.enseignement.polytechnique.fr/informatique/INF558/TD/td_5/S0025-5718-1987-0866119-8.pdf .

See other links in the code.

# Example
```javascript
import factorize from './QuadraticSieveFactorization.js';
console.time();
const f = factorize(2n**128n + 1n);
console.timeEnd();
// ~110ms
console.assert(f === 5704689200685129054721n || f === 59649589127497217n, f);
```

# Usage notes:
* Do not call for the **prime numbers**. It may hang for them. Check if the number is prime instead.
* Do not call for the **[perfect powers](https://en.wikipedia.org/wiki/Perfect_power)**. it may hang for them. Check if the number is a perfect power instead. 
* Do not call for the **numbers with a small factor**, it is as slow as for semiprimes with similar factor size for them. Try other algorithms to check for small factors instead.
* The returned value is a some factor, not necessary prime.

See https://www.rieselprime.de/ziki/Factorization for the more detailed usage notes.

# Demo
See [demo](https://yaffle.github.io/QuadraticSieveFactorization/demo.html).

# Performance

It took almost -11 hours- 6.5 hours to factor [RSA-100](https://en.wikipedia.org/wiki/RSA_numbers#RSA-100) on Core i7-1165G7 .
