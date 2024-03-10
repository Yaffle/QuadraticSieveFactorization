
    const wasmCode = new Uint8Array([0, 97, 115, 109, 1, 0, 0, 0, 1, 22, 3, 96, 4, 126, 126, 126, 126, 1, 126, 96, 3, 126, 126, 127, 1, 126, 96, 2, 126, 127, 1, 126, 3, 4, 3, 0, 1, 2, 7, 17, 1, 13, 80, 111, 108, 108, 97, 114, 100, 115, 82, 104, 111, 54, 52, 0, 2, 10, 143, 7, 3, 174, 1, 1, 4, 126, 32, 0, 66, 32, 136, 34, 5, 32, 1, 66, 255, 255, 255, 255, 15, 131, 34, 4, 126, 32, 0, 66, 255, 255, 255, 255, 15, 131, 34, 6, 32, 4, 126, 66, 32, 136, 124, 33, 7, 32, 1, 66, 32, 136, 34, 4, 32, 5, 126, 32, 7, 66, 32, 136, 124, 32, 4, 32, 6, 126, 32, 7, 66, 255, 255, 255, 255, 15, 131, 124, 66, 32, 136, 124, 34, 4, 32, 3, 32, 0, 32, 1, 126, 126, 34, 0, 66, 32, 136, 34, 1, 32, 2, 66, 32, 136, 34, 3, 126, 32, 2, 66, 255, 255, 255, 255, 15, 131, 34, 5, 32, 1, 126, 32, 0, 66, 255, 255, 255, 255, 15, 131, 34, 0, 32, 5, 126, 66, 32, 136, 124, 34, 1, 66, 32, 136, 124, 32, 0, 32, 3, 126, 32, 1, 66, 255, 255, 255, 255, 15, 131, 124, 66, 32, 136, 124, 34, 0, 125, 32, 2, 66, 0, 32, 0, 32, 4, 86, 27, 124, 11, 156, 5, 2, 8, 126, 4, 127, 32, 0, 33, 3, 65, 2, 33, 13, 3, 64, 32, 13, 65, 192, 0, 72, 4, 64, 32, 3, 66, 2, 32, 0, 32, 3, 126, 125, 126, 33, 3, 32, 13, 32, 13, 106, 33, 13, 12, 1, 11, 11, 32, 3, 33, 9, 66, 2, 33, 8, 66, 127, 32, 0, 130, 66, 1, 124, 33, 7, 3, 64, 32, 8, 66, 0, 82, 4, 64, 32, 8, 66, 1, 131, 167, 4, 64, 32, 4, 32, 0, 32, 7, 125, 34, 3, 125, 32, 0, 66, 0, 32, 3, 32, 4, 86, 27, 124, 33, 4, 11, 32, 7, 32, 0, 32, 7, 125, 34, 3, 125, 32, 0, 66, 0, 32, 3, 32, 7, 86, 27, 124, 33, 7, 32, 8, 66, 1, 136, 33, 8, 12, 1, 11, 11, 32, 1, 33, 3, 66, 127, 32, 0, 130, 66, 1, 124, 33, 7, 3, 64, 32, 3, 66, 0, 82, 4, 64, 32, 3, 66, 1, 131, 167, 4, 64, 32, 6, 32, 0, 32, 7, 125, 34, 1, 125, 32, 0, 66, 0, 32, 1, 32, 6, 86, 27, 124, 33, 6, 11, 32, 7, 32, 0, 32, 7, 125, 34, 1, 125, 32, 0, 66, 0, 32, 1, 32, 7, 86, 27, 124, 33, 7, 32, 3, 66, 1, 136, 33, 3, 12, 1, 11, 11, 66, 1, 33, 3, 66, 127, 32, 0, 130, 66, 1, 124, 33, 8, 3, 64, 32, 3, 66, 0, 82, 4, 64, 32, 3, 66, 1, 131, 167, 4, 64, 32, 5, 32, 0, 32, 8, 125, 34, 1, 125, 32, 0, 66, 0, 32, 1, 32, 5, 86, 27, 124, 33, 5, 11, 32, 8, 32, 0, 32, 8, 125, 34, 1, 125, 32, 0, 66, 0, 32, 1, 32, 8, 86, 27, 124, 33, 8, 32, 3, 66, 1, 136, 33, 3, 12, 1, 11, 11, 65, 1, 33, 13, 32, 5, 33, 3, 32, 4, 33, 1, 3, 64, 32, 2, 32, 11, 79, 4, 64, 32, 1, 33, 10, 3, 64, 32, 1, 32, 1, 32, 0, 32, 9, 16, 0, 34, 1, 32, 0, 32, 6, 125, 34, 7, 125, 32, 0, 66, 0, 32, 1, 32, 7, 84, 27, 124, 33, 1, 32, 11, 65, 1, 106, 34, 11, 32, 13, 65, 3, 108, 65, 2, 118, 77, 4, 126, 32, 1, 33, 4, 32, 11, 33, 12, 32, 5, 5, 32, 10, 32, 1, 125, 32, 1, 32, 10, 125, 32, 1, 32, 10, 84, 27, 33, 7, 32, 3, 32, 5, 82, 4, 64, 32, 3, 32, 7, 32, 0, 32, 9, 16, 0, 33, 7, 11, 32, 11, 65, 255, 0, 113, 69, 32, 11, 32, 13, 70, 114, 32, 14, 114, 4, 126, 66, 0, 32, 7, 32, 9, 126, 34, 3, 66, 32, 136, 34, 7, 32, 0, 66, 32, 136, 34, 8, 126, 32, 7, 32, 0, 66, 255, 255, 255, 255, 15, 131, 34, 7, 126, 32, 3, 66, 255, 255, 255, 255, 15, 131, 34, 3, 32, 7, 126, 66, 32, 136, 124, 34, 7, 66, 32, 136, 124, 32, 3, 32, 8, 126, 32, 7, 66, 255, 255, 255, 255, 15, 131, 124, 66, 32, 136, 124, 34, 3, 125, 32, 0, 66, 0, 32, 3, 66, 0, 82, 27, 124, 33, 7, 32, 0, 33, 3, 3, 64, 32, 3, 66, 0, 82, 4, 64, 32, 7, 32, 3, 130, 33, 8, 32, 3, 33, 7, 32, 8, 33, 3, 12, 1, 11, 11, 32, 7, 66, 1, 82, 4, 64, 32, 0, 32, 7, 82, 4, 64, 32, 7, 15, 11, 32, 14, 4, 64, 32, 0, 15, 11, 65, 1, 33, 14, 32, 12, 33, 11, 32, 4, 33, 1, 11, 32, 1, 33, 4, 32, 11, 33, 12, 32, 5, 5, 32, 7, 11, 11, 33, 3, 32, 11, 32, 13, 71, 13, 0, 11, 32, 13, 65, 1, 116, 33, 13, 12, 1, 11, 11, 66, 0, 11, 63, 1, 2, 126, 32, 0, 66, 2, 88, 4, 64, 66, 0, 15, 11, 32, 0, 66, 1, 131, 80, 4, 64, 66, 2, 15, 11, 3, 64, 32, 2, 66, 1, 124, 34, 2, 66, 42, 86, 4, 64, 66, 0, 15, 11, 32, 0, 32, 2, 32, 1, 16, 1, 34, 3, 32, 0, 81, 13, 0, 11, 32, 3, 11]);
    const wasmModule = new WebAssembly.Module(wasmCode);
    const exports = new WebAssembly.Instance(wasmModule).exports;
    export default exports.PollardsRho64;
  