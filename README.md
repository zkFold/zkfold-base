# zkfold-base
This repository contains the base library for the ZkFold project. It includes zkFold Symbolic compiler and a number of zero knowledge proof protocols. The compiler translates a subset of Haskell into arithmetic circuits, which can be used to generate zero knowledge proofs.

# Documentation
The zkFold Symbolic language can be utilized for creating zero-knowledge smart contracts and privacy-preserving applications. User documentation can be found at <docs.zkfold.io>.

If you want to contribute to the project or find out how it works "under the hood", check out [package documentation](https://hackage.haskell.org/package/zkfold-base-0.1.0.0/candidate zkFold Base package) on Hackage.

# Build
The package compiles with GHC 9.6.3 and Cabal 3.10.2.1.

# Tests
To run the tests, execute
```bash
cabal run -- zkfold-base-test
```

# Examples
The `examples` folder contains several code examples of arithmetizable pure functions. These examples can be compiled into the arithmetic circuits with the zkFold Symbolic compiler. In order to do it, execute
```bash
cabal run -- zkfold-base-examples
```
The output is placed into the `compiled_scripts` folder.