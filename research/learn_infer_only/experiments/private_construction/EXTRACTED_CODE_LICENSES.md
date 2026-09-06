# Attribution for extracted decoder code

The generated `build/IPFE-RLWE/rounding_extracted.c` includes the unmodified
`round_extract_gmp` function from [fentec-project/IPFE-RLWE](https://github.com/fentec-project/IPFE-RLWE),
commit `283975175b2407ab5a77e718e254d4d01671ca3a`, `src/rlwe_sife.c:257`.
Its MIT notice is reproduced below and included in the generated C file.

The generated `build/IPFE-2023/rounding_extracted.c` includes the corresponding
function from [s-adhikary/IPFE](https://github.com/s-adhikary/IPFE), commit
`06801d086b1468cdf1a5db84ef9f43552035f3f1`, `src/rlwe_sife.c:303`, associated with
Supriya Adhikary and Angshuman Karmakar's 2023 paper. This function extends the
earlier implementation with parallel directives. The earlier implementation's
copyright and MIT notice are retained for inherited code. No separate license
file was found in that pinned repository using `git ls-files`; this record does
not invent a license grant for its modifications. The excerpt is retained as
the exact research evidence for the executed decoder check.

`rlwe_source_audit.py` includes attribution and the upstream MIT notice when it
regenerates either C harness. Vendored repositories and native binaries are
ignored; pinned URLs, commits, hashes, exact extracted C and execution logs remain.

## Original implementation's license

MIT License

Copyright (c) 2021 Jose Maria Bermudo Mera and Angshuman Karmakar and Tilen Marc and Azam Soleimanian

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
