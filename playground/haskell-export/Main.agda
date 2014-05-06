module Main where

-- import Vec
import Param
import Compiled
-- fails with warning on GHC 7.8.2. Probably fixed in Agda HEAD.
-- import Builtin
-- import HOKinds

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}

postulate
  IO : Set → Set

{-# BUILTIN IO IO #-}
{-# COMPILED_TYPE IO IO #-}

postulate
  return : {A : Set} → A → IO A

{-# COMPILED return (\_ -> return) #-}

main : IO Unit
main = return unit

-- 1. safe vector ops.
-- 2. lambda calculus.(what to do there?)
--    type checker in agda, pretty printing and parsing in haskell.
