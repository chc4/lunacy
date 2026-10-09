These Uxntal programs are from the [`uxn` repository](https://git.sr.ht/~rabbits/uxn/),
commit [`3a696f8f`](https://git.sr.ht/~rabbits/uxn/commit/3a696f8fa9931857e99e50074c6994649ee62d37),
whose ROMs [Raven](https://github.com/mkeeter/raven) tests against: `uxnasm`
assembles each to the same bytes as Raven's copy of its ROM. `loop.tal` and
`loop_long.tal` are lunacy's own: a minimal loop, for looking at how an emulator
compiles one, and the same loop run long enough to time its steady state.

The `uxn` repository is released under the MIT license:

```
MIT License

Copyright (c) Devine Lu Linvega

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
```
