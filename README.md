# Symbolic framework
This repository contains the zkFold Symbolic framework. Contents:
- `symbolic-base`: The core package of the framework, providing the Symbolic compiler and the base symbolic data types;
- `symbolic-apps`: Applications and smart contracts built with the framework by the zkFold team;
- `symbolic-examples`: A collection of symbolic code examples for benchmarking and testing;

# Documentation
The Symbolic framework simplifies development of zero-knowledge applications and smart contracts. Developers can implement their app's business logic in high-level Haskell, and the framework will automatically generate the corresponding zero-knowledge circuits. The framework utilizes a very general intermediate representation of the circuits, supporting a wide range of proving systems.

User documentation can be found at [docs.zkfold.io](https://docs.zkfold.io/symbolic/introduction/ "zkFold Symbolic User Documentation").

If you want to contribute to the project or find out how it works "under the hood", check out [package documentation](https://hackage.haskell.org/package/symbolic-base-0.1.0.0/candidate "zkFold Symbolic Base package") on Hackage.

# Build
The package compiles with GHC 9.6.6 and Cabal 3.10.3.0. To build all packages, execute
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