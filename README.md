# zkFold Symbolic framework
This repository contains the zkFold Symbolic framework base library as well as additional packages written using the framework.

# Documentation
The zkFold Symbolic framework can be utilized to create zero-knowledge smart contracts and privacy-preserving applications.

User documentation can be found at [docs.zkfold.io](https://docs.zkfold.io/symbolic/introduction/ "zkFold Symbolic User Documentation").

If you want to contribute to the project or find out how it works "under the hood", check out [package documentation](https://hackage.haskell.org/package/zkfold-base-0.1.0.0/candidate "zkFold Base package") on Hackage.

# Build
The package compiles with GHC 9.6.3 and Cabal 3.10.2.1. To build all packages, execute
```bash
cabal build all
```

# Tests
To run the tests, execute
```bash
cabal test all
```

# Benchmarks
To run the benchmarks, execute
```bash
cabal bench all
```