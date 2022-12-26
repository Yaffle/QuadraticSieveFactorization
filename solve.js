
"use strict";

const BitSetWordSize = 31; // see https://v8.dev/blog/pointer-compression

function packedArray(n) {
  // `%DebugPrint(array)` in `node --allow-native-syntax`
  // see https://v8.dev/blog/elements-kinds
  const array = [];
  for (let i = 0; i < n; i += 1) {
    array.push(0);
  }
  return array.slice(0); // slice to reduce the size of the internal storage
}
function BitSet(size) {
  const n = Math.ceil(size / (4 * BitSetWordSize)) * 4;
  this.data = packedArray(n);
  this.size = size;
}
BitSet.prototype.nextSetBit = function (index) {
  if ((index | 0) >= (this.size | 0)) {
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
  if (x === (-1 << (BitSetWordSize - 1))) {
    // -x overflows
    r += BitSetWordSize - 1;
  } else {
    // https://stackoverflow.com/questions/61442006/whats-the-most-efficient-way-of-getting-position-of-least-significant-bit-of-a
    r += 31 - Math.clz32(x & -(+x));
  }
  return q * BitSetWordSize + r;
};
BitSet.prototype.toggle = function (index) {
  if ((index | 0) >= (this.size | 0)) {
    throw new RangeError();
  }
  const q = Math.floor(index / BitSetWordSize);
  const r = index % BitSetWordSize;
  this.data[q] ^= (r === BitSetWordSize - 1 ? ((-1) << r) : (1 << r));
};
BitSet.prototype.xor = function (other) {
  const a = this.data;
  const b = other.data;
  const n = a.length | 0;
  if (n !== b.length || n % 4 !== 0) {
    throw new RangeError();
  }
  for (let i = 0; i < n; i += 4) {
    a[i + 0] ^= b[i + 0] | 0;
    a[i + 1] ^= b[i + 1] | 0;
    a[i + 2] ^= b[i + 2] | 0;
    a[i + 3] ^= b[i + 3] | 0;
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
    next: function solve(rawRowAndValue) {
      while (true) {
        if (state === 1) {
          state = 0;
          return {value: nextSolution, done: false};
        }
        state = 1;
        const rawRow = rawRowAndValue[0];
        const associatedValue = rawRowAndValue[1];
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
            //console.assert(row.nextSetBit(pivotColumn) > pivotColumn || row.nextSetBit(pivotColumn) === -1);
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

export default solve;
