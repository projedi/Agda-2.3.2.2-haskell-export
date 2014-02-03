module Agda.Compiler.MAlonzo.Export.CheckNames( checkConsName
                                              , checkFunName
                                              , checkTypeName
                                              ) where

import Control.Applicative
import Control.Monad

import qualified Data.Char as Char
import qualified Data.List as List
import Data.Set(Set)
import qualified Data.Set as Set

import Agda.TypeChecking.Monad(TCM, TypeError(..), typeError)

-- TODO: Verify with Haskell2010
-- Verifying validity of Haskell names(taken from Haskell 98 report)

isSpecial :: Char -> Bool
isSpecial c = c `List.elem` "(),;[]`{}"

isSymbol :: Char -> Bool
isSymbol c = Char.isSymbol c && not (isSpecial c) && not (c `List.elem` "_:\"'")

isDashes :: String -> Bool
isDashes ('-':'-':xs) = all (== '-') xs
isDashes _ = False

reservedNames :: Set String
reservedNames = Set.fromList
   [ "case"
   , "class"
   , "data"
   , "default"
   , "deriving"
   , "do"
   , "else"
   , "if"
   , "import"
   , "in"
   , "infix"
   , "infixl"
   , "infixr"
   , "instance"
   , "let"
   , "module"
   , "newtype"
   , "of"
   , "then"
   , "type"
   , "where"
   , "_"
   ]

isReservedId :: String -> Bool
isReservedId = flip Set.member reservedNames

isRestValid :: Char -> Bool
isRestValid c = Char.isLetter c || Char.isDigit c || (c == '\'')

isVarId :: String -> Bool
isVarId [] = False
isVarId str@(x:xs)
 | isReservedId str = False
 | otherwise = Char.isLower x && all isRestValid xs

isConId :: String -> Bool
isConId [] = False
isConId str@(x:xs)
 | isReservedId str = False
 | otherwise = Char.isUpper x && all isRestValid xs

reservedOps :: Set String
reservedOps = Set.fromList
   [ ".."
   , ":"
   , "::"
   , "="
   , "\\"
   , "|"
   , "<-"
   , "->"
   , "@"
   , "~"
   , "=>"
   ]

isReservedOp :: String -> Bool
isReservedOp = flip Set.member reservedOps

isVarSym :: String -> Bool
isVarSym [] = False
isVarSym str@(x:xs)
 | isReservedOp str || isDashes str = False
 | otherwise = isSymbol x && all (\c -> isSymbol c || (c == ':')) xs

isConSym :: String -> Bool
isConSym [] = False
isConSym str@(x:xs)
 | isReservedOp str = False
 | otherwise = (x == ':') && all (\c -> isSymbol c || (c == ':')) xs

withBrackets :: (String -> Bool) -> String -> Bool
withBrackets f str
 | head str == '(' && last str == ')' = f $ tail $ init $ str
 | otherwise = False

-- With TypeOperators extension any operator(even constructor operator)
-- can be a type operator.
-- Type operators and operators are in different namespaces(it's possible
-- for the same string to be both a type and a term operator)
isProperTypeName :: String -> Bool
isProperTypeName str = isConId str || withBrackets isVarSym str
                                   || withBrackets isConSym str

isProperConstName :: String -> Bool
isProperConstName str = isVarId str || withBrackets isVarSym str

-- TODO: Maybe put brackets around operators by hand

checkTypeName :: String -> TCM ()
checkTypeName str = when (not $ isProperTypeName str) $ typeError $
   CompilationError $ show str ++ " is not a proper Haskell typename" ++ wrongOp
 where wrongOp = if isVarSym str || isConSym str then " (use brackets around operators)" else ""

checkFunName :: String -> TCM ()
checkFunName str = when (not $ isProperConstName str) $ typeError $
   CompilationError $ show str ++ " is not a proper Haskell identificator" ++ wrongOp
 where wrongOp = if isVarSym str then " (use brackets around operators)" else ""

checkConsName :: String -> TCM ()
checkConsName = checkTypeName
