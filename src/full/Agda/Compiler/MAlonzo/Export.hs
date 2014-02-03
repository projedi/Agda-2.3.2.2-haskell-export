module Agda.Compiler.MAlonzo.Export(export) where 
import Control.Applicative
import Control.Monad

import Control.Monad.State(get, modify)
import Control.Monad.Trans(liftIO)
import qualified Language.Haskell.Exts.Syntax as HS

import Agda.Compiler.MAlonzo.Export.CheckNames
import Agda.Compiler.MAlonzo.Export.TypeTransform
import Agda.Compiler.MAlonzo.Misc(unqhname)
import Agda.Syntax.Internal(QName)
import Agda.TypeChecking.Monad( CompiledRepresentation(..)
                              , Definition(..)
                              , Defn(..)
                              , ExportedHaskell(..)
                              , TCM
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

export :: Maybe CoinductionKit -> Definition -> TCM [HS.Decl]
export kit def = do
   res <- getLocalExport kit def
   writeGlobalExport kit def
   return res

getLocalExport :: Maybe CoinductionKit -> Definition -> TCM [HS.Decl]
getLocalExport _ (Defn _ q ty _ _ _ _ compiled d) =
   case exportedHaskell compiled of
    Nothing -> return []
    Just (Exported wantedName) -> 
       case d of
        Function{} -> do
           checkFunName wantedName
           generateExport d ty (declName q) wantedName
        Datatype{} -> do
           checkTypeName wantedName
           generateExport d ty (typeName q) wantedName
        Record{} -> do
           checkTypeName wantedName
           generateExport d ty (typeName q) wantedName
        Constructor{} -> do
           checkFunName wantedName
           generateExport d ty (consName q) wantedName
        _ -> __IMPOSSIBLE__
    Just (ExportedData wantedTypeName wantedConsNames) -> do
       checkTypeName wantedTypeName
       mapM_ checkConsName wantedConsNames
       case d of
        Datatype{ dataCons = cs } ->
           generateExportData d ty (typeName q) wantedTypeName
              (map consName cs) wantedConsNames
        _ -> __IMPOSSIBLE__

-- TODO: Should create a module Export.ModuleName where ModuleName is a current module
-- TODO: and which would reexport all functions and data but newtype would be abstract.
-- For MAlonzo.Code.M we should produce:
-- MAlonzo.Export.M(AbstractT, DataT(..), f, g) where
-- import MAlonzo.Code.M
writeGlobalExport :: Maybe CoinductionKit -> Definition -> TCM ()
writeGlobalExport _ _ = return ()
