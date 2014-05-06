{-# LANGUAGE TupleSections #-}
module Agda.Compiler.MAlonzo.Export(addExport, getExportModule, initExportModule) where 

import Control.Applicative
import Control.Monad

import Control.Monad.State(get, modify)
import Control.Monad.Trans(liftIO)
import qualified Language.Haskell.Exts.Syntax as HS

import Agda.Compiler.MAlonzo.Export.CheckNames
import Agda.Compiler.MAlonzo.Export.TypeTransform
import Agda.Compiler.MAlonzo.Misc(curHsMod, curMName, dummy, mazRTE, unqhname)
import Agda.Syntax.Abstract(ModuleName)
import Agda.Syntax.Internal(QName)
import Agda.TypeChecking.Monad( CompiledRepresentation(..)
                              , Definition(..)
                              , Defn(..)
                              , ExportedHaskell(..)
                              , TCM
                              , TCState(..)
                              , TypeError(..)
                              , typeError
                              )
import Agda.TypeChecking.Monad.Builtin(CoinductionKit)

import Agda.Utils.Impossible
#include "../../undefined.h"

declName :: QName -> HS.Name
declName = unqhname "d"

typeName :: QName -> HS.Name
typeName = unqhname "T"

consName :: QName -> HS.Name
consName = unqhname "C"

mazExpMod :: ModuleName -> HS.ModuleName
mazExpMod = HS.ModuleName . ("MAlonzo.Export." ++) . show

modifyExportModule :: (Maybe HS.Module -> Maybe HS.Module) -> TCM ()
modifyExportModule f = modify $ \st -> st { stExportModule = f (stExportModule st) }

initExportModule :: TCM ()
initExportModule = do
   compModName <- curHsMod
   exportModName <- mazExpMod <$> curMName
   modifyExportModule $ \_ ->
      Just $ HS.Module dummy exportModName [] Nothing Nothing
         [ HS.ImportDecl dummy mazRTE True False Nothing Nothing Nothing
         , HS.ImportDecl dummy compModName False False Nothing Nothing Nothing
         ] []

addExport :: Maybe CoinductionKit -> Definition -> TCM ()
addExport kit def = do
   r <- getLocalExport kit def
   case r of
    Nothing -> return ()
    Just (exp, code) -> modifyExportModule $ f exp code
 where f _ _ Nothing = Nothing
       f exp code (Just (HS.Module l nm prs wt exps imps decls)) =
          Just $ HS.Module l nm prs wt (modifyExports exps exp) imps (code ++ decls)
       modifyExports Nothing exp = Just [exp]
       modifyExports (Just exps) exp = Just $ exp : exps

getExportModule :: TCM (Maybe HS.Module)
getExportModule = do
   mm <- stExportModule <$> get
   case mm of
    Nothing -> return Nothing
    Just (m@(HS.Module _ _ _ _ exps _ _)) ->
       case exps of
        Nothing -> return Nothing
        Just _ -> return $ Just m

getLocalExport :: Maybe CoinductionKit -> Definition ->
   TCM (Maybe (HS.ExportSpec, [HS.Decl]))
getLocalExport _ (Defn _ q ty _ _ _ _ compiled d) =
   case exportedHaskell compiled of
    Nothing -> return Nothing
    Just (Exported wantedName) -> do
       ensureNoCompiledData $ compiledHaskell compiled
       case d of
        Function{} -> do
           checkFunName wantedName
           (Just . (HS.EVar $ HS.UnQual $ HS.Ident wantedName,)) <$>
              generateExport d ty (declName q) wantedName
        Datatype{} -> do
           checkTypeName wantedName
           (Just . (HS.EAbs $ HS.UnQual $ HS.Ident wantedName,)) <$>
              generateExport d ty (typeName q) wantedName
        Record{} -> do
           checkTypeName wantedName
           (Just . (HS.EAbs $ HS.UnQual $ HS.Ident wantedName,)) <$>
               generateExport d ty (typeName q) wantedName
        Constructor{} -> do
           checkFunName wantedName
           (Just . (HS.EVar $ HS.UnQual $ HS.Ident wantedName,)) <$>
               generateExport d ty (consName q) wantedName
        _ -> __IMPOSSIBLE__
 where ensureNoCompiledData Nothing = return ()
       ensureNoCompiledData (Just _) = typeError $ GenericError
          "Cannot export compiled names"
