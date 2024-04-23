module Main where

import           Foreign.C.String
import           RustFfi

main :: IO ()
main = withCString "Rust 🦀" hello
