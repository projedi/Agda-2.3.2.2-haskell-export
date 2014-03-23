module Agda.Compiler.MAlonzo.Export.TypeTransform( generateExport
                                                 , generateExportData
                                                 ) where

import Control.Applicative
import Control.Monad

import Control.Monad.Trans(liftIO)
import Data.List(foldl')
import qualified Language.Haskell.Exts.Syntax as HS

import Agda.Compiler.MAlonzo.Misc(conArityAndPars, dummy, mazCoerce)
import Agda.Syntax.Common(Arg(..), Dom(..))
import Agda.Syntax.Internal( Abs(..), QName, Sort(..), Level(..), PlusLevel(..)
                           , Term(..), Type(..))
import Agda.TypeChecking.Monad( TCM, Definition(..), Defn(..), CompiledRepresentation(..)
                              , ExportedHaskell(..), TypeError(..), getConstInfo, typeError)
import Agda.TypeChecking.Conversion(leqSort)

import Agda.Utils.Impossible
#include "../../../undefined.h"

-- TODO: Are termination checks on callbacks required?
-- TODO: Parametrized modules
-- TODO: Make it impossible to have simultaneous(and several)
-- TODO: EXPORT_TYPE, EXPORT_DATA, COMPILED_DATA on one and the same type

assertSort :: Integer -> Sort -> TCM ()
assertSort n s = s `leqSort` (Type $ Max [ClosedLevel n])

exportNewtypeFromData :: Int -> Int -> [QName] -> Type -> HS.Name -> String -> TCM [HS.Decl]
exportNewtypeFromData pars ixs constrs ty name wantedName = do
   paramKinds <- assertType ty
   conpars <- mapM (((\(x,y) -> x + y) <$>) . conArityAndPars) constrs
   let extyvarcount = maximum (pars : conpars) - pars
       extyvars = map (HS.Ident . ('b':) . show) $ take extyvarcount [0..]
   return [
      HS.DataDecl dummy HS.NewType [] (HS.Ident wantedName)
         (map (uncurry HS.KindedVar) $ zip tyvars paramKinds) [
            HS.QualConDecl dummy [] [] $
               HS.ConDecl (HS.Ident wantedName) [
                  HS.UnBangedTy $ HS.TyForall (Just $ map HS.UnkindedVar extyvars) [] $
                     foldl' HS.TyApp extycons $ map HS.TyVar extyvars
               ]
         ] []
    ]
 where tyvars = map (HS.Ident . ('a':) . show) $ take tyvarcount [0..]
       extycons = HS.TyCon $ HS.UnQual name
       tyvarcount = pars + ixs
       -- TODO: assertType and assertParamType look deceptively like some
       -- TODO: Foldable operation
       assertType (El _ (Sort s)) = do
         assertSort 0 s
         return []
       assertType (El _ (Pi (Dom _ _ t) absto)) = do
          kind <- assertParamType t
          (kind :) <$> assertType (unAbs absto)
       assertType (El _ t) = do
          typeError $ GenericError $ "Unexpected type in data declaration: " ++ show t
       assertParamType (El _ (Sort s)) = do
          assertSort 0 s
          return HS.KindStar
       assertParamType (El _ (Pi (Dom _ _ t) absto)) = do
          kindFrom <- assertParamType t
          (HS.KindFn kindFrom) <$> assertParamType (unAbs absto)

{-

--- conv ---

f : A
hf :: a, if A |-> a, __IMPOSSIBLE__ otherwise
hf = f

f : E
hf :: HE, if E |-> HE, error otherwise
hf = f -- casts because of newtype

f : (A : Set) -> T
hf :: forall a. Conv(T, A |-> a)
hf = conv(f dummy)

f : T1 -> T2
hf :: Conv(T1) -> Conv(T2)
hf = \x -> conv (f (unconv x))

--- unconv ---

hf :: Conv A, A |-> a, __IMPOSSIBLE__ otherwise
f = hf

hf :: Conv E, E |-> HE, error otherwise
f = hf

hf :: Conv((A : Set) -> Conv(T))
f = \_ -> unconv hf

hf :: Conv (T1 -> T2)
f = \cb -> unconv (hf (conv cb))

-}

mazDummy :: HS.Exp
mazDummy = HS.Var (HS.UnQual $ HS.Ident "error") `HS.App` HS.Lit
   (HS.String "dummy was evaluated")

getType :: Int -> Term -> TCM HS.Type
getType vars (Var i args) = do
   let iname = HS.Ident $ "a" ++ show (vars - i - 1)
   (foldl' HS.TyApp (HS.TyVar iname)) <$> mapM (getType vars . unArg) args
getType vars (Def name args) = do
   def <- findDef name
   (foldl' HS.TyApp def) <$> mapM (getType vars . unArg) args
 where findDef name = do
          expInfo <- (exportedHaskell . defCompiledRep) <$> getConstInfo name
          case expInfo of
           Nothing -> typeError $
              GenericError "All types must be exported for function to be exported"
           Just (ExportedData _ _) -> undefined
           Just (Exported x) -> return $ HS.TyCon $ HS.UnQual $ HS.Ident x
getType vars (Pi (Dom _ _ (El _ t1)) (NoAbs _ (El _ t2))) =
   HS.TyFun <$> getType vars t1 <*> getType vars t2
getType _ _ = typeError $ GenericError
   "Only exported types, variables and arrows can be used as type arguments during export"

toCurry :: Int -> HS.Exp -> Int -> Type -> TCM (HS.Type, HS.Exp)
toCurry d f vars (El _ x@(Var _ _)) = do
   t <- getType vars x
   return (t, f)
toCurry d f vars (El _ x@(Def _ _)) = do
   t <- getType vars x
   return (t, f)
toCurry d f vars (El _ (Pi (Dom _ _ (El _ (Sort s))) absto)) = do
   assertSort 0 s
   (t, hf) <- case absto of
               Abs _ to -> toCurry d (f `HS.App` mazDummy) (vars + 1) to
               NoAbs _ to -> toCurry d (f `HS.App` mazDummy) vars to
   let iname = HS.Ident $ "a" ++ show vars
   return (HS.TyForall (Just [HS.UnkindedVar iname]) [] t, hf)
toCurry d f vars (El _ (Pi (Dom _ _ _) (Abs _ _))) = do
   typeError $ GenericError $ "Exported functions must be nondependent"
toCurry d f vars (El _ (Pi (Dom _ _ t1@(El s _)) (NoAbs _ t2))) = do
   let xname = HS.Ident $ "x" ++ show d
       x = HS.Var $ HS.UnQual xname
   (t1', x') <- fromCurry (d + 1) x vars t1
   (t2', f') <- toCurry (d + 1) (f `HS.App` (mazCoerce `HS.App` x')) vars t2
   return (t1' `HS.TyFun` t2', HS.Lambda dummy [HS.PVar xname] f')
toCurry _ _ _ _ = __IMPOSSIBLE__

fromCurry :: Int -> HS.Exp -> Int -> Type -> TCM (HS.Type, HS.Exp)
fromCurry d hf vars (El _ x@(Var _ _)) = do
   t <- getType vars x
   return (t, hf)
fromCurry d hf vars (El _ x@(Def _ _)) = do
   t <- getType vars x
   return (t, hf)
fromCurry d hf vars (El _ (Pi (Dom _ _ (El _ (Sort s))) absto)) = do
   assertSort 0 s
   (t, f) <- case absto of
              Abs _ to -> fromCurry d (HS.Lambda dummy [HS.PWildCard] hf) (vars + 1) to
              NoAbs _ to -> fromCurry d (HS.Lambda dummy [HS.PWildCard] hf) vars to
   let iname = HS.Ident $ "a" ++ show vars
   return (HS.TyForall (Just [HS.UnkindedVar iname]) [] t, f)
fromCurry d hf vars (El _ (Pi (Dom _ _ _) (Abs _ _))) = do
   typeError $ GenericError $ "Exported functions must be nondependent"
fromCurry d hf vars (El _ (Pi (Dom _ _ t1@(El s _)) (NoAbs _ t2))) = do
   let xname = HS.Ident $ "x" ++ show d
       x = HS.Var $ HS.UnQual xname
   (t1', x') <- toCurry (d + 1) x vars t1
   (t2', hf') <- fromCurry (d + 1) (hf `HS.App` x') vars t2
   return (t1' `HS.TyFun` t2', HS.Lambda dummy [HS.PVar xname] hf')
fromCurry _ _ _ _ = __IMPOSSIBLE__

exportFunction :: Type -> HS.Name -> String -> TCM [HS.Decl]
exportFunction ty name wantedName = do
   (t, f) <- toCurry 0 (HS.Var $ HS.UnQual name) 0 ty
   let fname = HS.Ident wantedName
   return [ HS.TypeSig dummy [fname] t
          , HS.FunBind [
            HS.Match dummy fname [] Nothing (HS.UnGuardedRhs f) (HS.BDecls [])
          ]]

generateExport :: Defn -> Type -> HS.Name -> String -> TCM [HS.Decl]
generateExport (Constructor{}) =
   exportFunction
generateExport (Datatype{ dataPars = pars, dataIxs = ixs, dataCons = cons }) =
   exportNewtypeFromData pars ixs cons
generateExport (Function{}) =
   exportFunction
generateExport (Record{ recPars = pars, recCon = con}) =
   exportNewtypeFromData pars 0 [con]
generateExport _ = __IMPOSSIBLE__

generateExportData :: Defn -> Type -> HS.Name -> String ->
   [HS.Name] -> [String] -> TCM [HS.Decl]
generateExportData d ty typeName wantedTypeName consNames wantedConsNames = do
   liftIO $ putStrLn "EXPORT_DATA is not yet supported"
   return []
