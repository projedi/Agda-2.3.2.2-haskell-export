module Param(A : Set) where

data SomeData (B : Set) : Set where
   cons1 : A → SomeData B

somefun : A → SomeData A
somefun = cons1

{-# EXPORT SomeData SomeData #-}
{-# EXPORT somefun somefun #-}
