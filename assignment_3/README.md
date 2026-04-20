# Assignment 3
For simplicity we decided to follow the same exact process as the previous homework assignments so everything works functionally the same. All these files were simply adapted to fit the assignment 3 passes.

## Build

```bash
make
```

This builds `build/unifiedpass.so`.

## Run all tests

```bash
make tests
```

## Run one pass manually

```bash
opt -bugpoint-enable-legacy-pm=1 \
  -load-pass-plugin=build/unifiedpass.so \
  -passes='dominators' tests/simple-while-dom.bc -o /tmp/out.bc
```

Replace `dominators` with : `dead-code-elimination` or `loop-invariant-code-motion`.


