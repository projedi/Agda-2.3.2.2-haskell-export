module Agda.Compiler.MAlonzo.Export.Builtins
   ( BuiltinMap
   , SupportedBuiltin(..)
   , getBuiltinMap
   , lookupBuiltin
   ) where

import Control.Applicative
import Control.Monad

import Control.Monad.State(get)
import Data.List(foldl')
import Data.Map(Map)
import qualified Data.Map as Map

import Agda.Syntax.Internal(QName, Term(..))
import Agda.TypeChecking.Monad(Builtin(..), TCM, stBuiltinThings)
import Agda.TypeChecking.Monad.Builtin
   ( builtinBool, builtinChar, builtinCons, builtinFalse, builtinFloat
   , builtinInteger, builtinIO, builtinList, builtinNat, builtinNil
   , builtinString, builtinSuc, builtinTrue, builtinZero
   )

import Agda.Utils.Impossible
#include "../../../undefined.h"

-- Currently used: CHAR, FLOAT, INTEGER, STRING
-- LIST and BOOL are essentially similar to EXPORT_DATA
-- NATURAL is better to leave alone - it transforms to Int, Integer
-- which are signed.
data SupportedBuiltin
   = BuiltinBool QName QName -- ^ two constructors
   | BuiltinChar
   | BuiltinFloat
   | BuiltinInteger
   | BuiltinIO
   | BuiltinList QName QName -- ^ two constructors
   | BuiltinNat QName QName -- ^ two constructors
   | BuiltinString
   deriving Show

newtype BuiltinMap = BuiltinMap (Map QName SupportedBuiltin)

lookupBuiltin :: QName -> BuiltinMap -> Maybe SupportedBuiltin
lookupBuiltin n (BuiltinMap m) = Map.lookup n m

-- TODO: This is going to be extra slow. Should be calculated before processing
-- TODO: all the definitions and stored in TCState or something.
getBuiltinMap :: TCM BuiltinMap
getBuiltinMap = do
   things <- stBuiltinThings <$> get
   let prims = foldl' (\m (n,v) -> addPrim m v $ Map.lookup n things) Map.empty
          [ (builtinChar, BuiltinChar)
          , (builtinFloat, BuiltinFloat)
          , (builtinInteger, BuiltinInteger)
          , (builtinIO, BuiltinIO)
          , (builtinString, BuiltinString)
          ]
       datas = foldl' (\m (n,v,cs) -> addData m v (map (flip Map.lookup things) cs) $ Map.lookup n things) Map.empty
          [ (builtinBool, BuiltinBool, [builtinTrue, builtinFalse])
          , (builtinList, BuiltinList, [builtinNil, builtinCons])
          , (builtinNat, BuiltinNat, [builtinZero, builtinSuc])
          ]
   return $ BuiltinMap $ prims `Map.union` datas
 where addPrim m _ Nothing = m
       addPrim m v (Just (Builtin (Def n _))) = Map.insert n v m
       addPrim _ _ _ = __IMPOSSIBLE__
       addData m _ _ Nothing = m
       addData m v [(Just (Builtin (Con c1 _))), (Just (Builtin (Con c2 _)))] (Just (Builtin (Def n _))) =
          Map.insert n (v c1 c2) m
       addData _ _ _ _ = __IMPOSSIBLE__
