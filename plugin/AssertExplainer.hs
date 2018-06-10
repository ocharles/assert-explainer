{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module AssertExplainer ( plugin, assert ) where

-- assert-explainer
import qualified Constraint

-- base
import Data.Bool ( bool )
import Data.List ( foldl' )
import Control.Monad.IO.Class ( liftIO )
import Data.Foldable ( toList )
import Data.Maybe ( catMaybes )
  
-- ghc
import qualified Convert as GHC
import qualified CoreUtils
import qualified Desugar as GHC
import qualified Finder as GHC
import qualified GHC
import qualified GhcPlugins as GHC
import qualified HsExpr as Expr
import qualified HsPat as Pat
import qualified HsUtils
import qualified HsUtils as GHC
import qualified Id as GHC
import qualified IfaceEnv as GHC
import qualified PrelNames as GHC
import qualified RnExpr as GHC
import qualified TcEnv as GHC
import qualified TcEvidence as GHC
import qualified TcExpr as GHC
import qualified TcHsSyn as GHC
import qualified TcRnMonad as GHC
import qualified TcSMonad as GHC ( runTcS )
import qualified TcSimplify as GHC
import qualified TcType as GHC
import qualified Unique

-- syb
import Data.Generics ( everywhereM, listify, mkM )

-- template-haskell
import Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax as TH


{-|

The @assert-explainer@ plugin intercepts calls to 'assert' and tries to explain
them if they fail. You can use this plugin by depending on the
@assert-explainer@ library, and then adding:

@{-# OPTIONS -fplugin=AssertExplainer #-}@

to your test pragmas.
-}

plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.typeCheckResultAction = \_cliOptions -> explainAssertions }


data Names = Names
  { hs_return :: GHC.Name
  , hs_assert :: GHC.Id
  , hs_unit :: GHC.Name
  , hs_IO :: GHC.TyCon
  , hs_print :: GHC.Name
  , hs_show :: GHC.Name
  }


resolveNames :: GHC.TcM Names
resolveNames = do 
  hscEnv <-
    GHC.getTopEnv

  GHC.Found _ assertExplainerModule <-
    liftIO ( GHC.findImportedModule hscEnv ( GHC.mkModuleName "AssertExplainer" ) Nothing )

  hs_IO <-
    GHC.lookupTyCon ( GHC.ioTyConName )

  let
    hs_return =
      GHC.returnIOName

  hs_print <-
    GHC.lookupOrig GHC.sYSTEM_IO ( GHC.mkVarOcc "putStrLn" )

  hs_assert <-
    GHC.lookupId
      =<< GHC.lookupOrig assertExplainerModule ( GHC.mkVarOcc "assert" )

  let
    hs_unit =
      GHC.varName GHC.unitDataConId

  hs_show <-
    GHC.lookupOrig GHC.gHC_SHOW ( GHC.mkVarOcc "show" )

  return Names{..}


explainAssertions :: GHC.ModSummary -> GHC.TcGblEnv -> GHC.TcM GHC.TcGblEnv
explainAssertions _modSummary tcGblEnv = do 
  names <-
    resolveNames
  
  tcg_binds <-
    mkM ( rewriteAssert names ) `everywhereM` GHC.tcg_binds tcGblEnv

  return tcGblEnv { GHC.tcg_binds = tcg_binds }


assert :: Bool -> IO ()
assert =
  bool ( fail "Assertion failed!" ) ( return () )


-- | Rewrite an 'assert' call into further analysis on the expression being asserted.
rewriteAssert :: Names -> Expr.HsExpr GHC.GhcTc -> GHC.TcM ( Expr.HsExpr GHC.GhcTc )
rewriteAssert names e@( Expr.HsApp _ ( GHC.L _ ( Expr.HsVar _ ( GHC.L _ v ) ) ) ( GHC.L _ body ) ) | hs_assert names == v = do
  GHC.L _ e <-
    explain names body

  return e

rewriteAssert _ e =
  return e


data Typed = Typed
  { typedExpr :: Expr.HsExpr GHC.GhcTcId
  , typedExprType :: GHC.Type
  }
  

explain :: Names -> Expr.HsExpr GHC.GhcTc -> GHC.TcM ( Expr.LHsExpr GHC.GhcTc )
explain names e = do
  -- Find all sub-expressions in the body
  let
    subExpressions =
      listify isHsExpr e

  -- Augment each sub-expression with its type
  typedSubExpressions <-
    catMaybes <$> traverse toTyped subExpressions

  -- Filter the list of sub-expressions to just those that can be shown.
  showableSubExpresions <-
    catMaybes <$> traverse witnessShow typedSubExpressions

  -- Build an anonymous function to describe all of these subexpressions
  Right expr <- fmap ( GHC.convertToHsExpr GHC.noSrcSpan ) $ liftIO $ TH.runQ $ do
    diagnosticArgs <-
      sequence ( TH.newName "x" <$ showableSubExpresions )

    let
      diagnose te name =
        TH.noBindS ( diagnoseExpr te name )

      diagnosed =
        zipWith diagnose showableSubExpresions diagnosticArgs

    id
      ( foldl'
          ( \e name -> TH.lam1E ( TH.varP name ) e )
          ( TH.doE diagnosed )
          ( reverse diagnosticArgs )
      )

  let 
    -- Build the type of the diagnostic function
    diagnosticFunctionT =
      foldr
        GHC.mkFunTy
        ( GHC.mkTyConApp ( hs_IO names ) [ GHC.mkTyConTy GHC.unitTyCon ] )
        ( map typedExprType showableSubExpresions )

  ( diagnosticFunction, _ ) <-
    GHC.rnLExpr expr

  -- Type check our diagnostic function to find which dictionaries need to be
  -- resolved.
  ( GHC.L _ ifExpr', wanteds ) <-
    GHC.captureConstraints
      ( GHC.tcMonoExpr
        diagnosticFunction
        ( GHC.Check diagnosticFunctionT )
      )

  -- Solve wanted constraints and build a wrapper.
  wrapper <-
    GHC.mkWpLet . GHC.EvBinds . GHC.evBindMapBinds . snd
      <$> GHC.runTcS ( GHC.solveWanteds wanteds )

  -- Apply the wrapper to our type checked syntax and fully saturate the
  -- diagnostic function with the necessary arguments.
  GHC.zonkTopLExpr
    ( foldl
        ( \a b -> GHC.noLoc ( Expr.HsApp GHC.NoExt a b ) )
        ( GHC.noLoc ( Expr.HsWrap GHC.NoExt wrapper ifExpr' ) )
        ( map ( GHC.noLoc . typedExpr ) showableSubExpresions )
    )


diagnoseExpr :: Typed -> TH.Name -> TH.ExpQ
diagnoseExpr te name =
  let
    ppExpr =
      GHC.renderWithStyle
        GHC.unsafeGlobalDynFlags
        ( GHC.ppr ( typedExpr te ) )
        ( GHC.defaultUserStyle GHC.unsafeGlobalDynFlags )
  in
  [| putStrLn ( ppExpr ++ " = " ++ show $( TH.varE name ) ) |]

  -- GHC.mkHsApp
  --   ( GHC.noLoc
  --       ( Expr.HsVar GHC.NoExt ( GHC.noLoc ( hs_print names ) ) )
  --   )
  --   ( GHC.mkHsApp
  --       ( GHC.mkHsApp
  --           ( GHC.noLoc ( Expr.HsVar GHC.NoExt ( GHC.noLoc GHC.mappendName ) ) )
  --           ( GHC.noLoc
  --               ( Expr.HsLit GHC.NoExt
  --                   ( GHC.HsString
  --                       GHC.NoSourceText
  --                       ( GHC.fsLit
  --                           ( 
  --                           )
  --                       )
  --                   )
  --               )
  --           )
  --       )
  --       ( GHC.mkHsApp
  --           ( GHC.noLoc
  --               ( Expr.HsVar GHC.NoExt ( GHC.noLoc ( hs_show names ) ) )
  --           )
  --           ( GHC.noLoc
  --               ( Expr.HsVar GHC.NoExt ( GHC.noLoc ( GHC.idName name ) ) )
  --           )
  --       )
  --   )



isHsExpr :: Expr.HsExpr GHC.GhcTc -> Bool 
isHsExpr Expr.HsPar{} =
  False
isHsExpr Expr.HsLit{} =
  False
isHsExpr Expr.HsOverLit{} =
  False
isHsExpr Expr.HsWrap{} =
  False
isHsExpr _ =
  True


returnUnit names =
  Expr.HsApp GHC.NoExt
    ( GHC.noLoc ( Expr.HsVar GHC.NoExt ( GHC.noLoc ( hs_return names ) ) ) )
    ( GHC.noLoc ( Expr.HsVar GHC.NoExt ( GHC.noLoc ( hs_unit names ) ) ) )


toTyped e = do
  hs_env  <-
    GHC.getTopEnv

  ( _, mbe ) <-
    liftIO ( GHC.deSugarExpr hs_env ( GHC.noLoc e ) )

  return ( ( \x -> Typed e ( CoreUtils.exprType x ) ) <$> mbe )


witnessShow tExpr = do
  showTyCon <-
    GHC.tcLookupTyCon GHC.showClassName

  dictName <-
    GHC.newName ( GHC.mkDictOcc ( GHC.mkVarOcc "magic" ) )

  let
    dict_ty =
      GHC.mkTyConApp showTyCon [ typedExprType tExpr ]

    dict_var =
      GHC.mkVanillaGlobal dictName dict_ty

  GHC.EvBinds evBinds <-
    Constraint.getDictionaryBindings dict_var dict_ty

  case toList evBinds of
    [] ->
      return Nothing

    _ ->
      return ( Just tExpr )


abstract name e =
  Expr.HsLam GHC.NoExt
    Expr.MG
      { Expr.mg_ext = GHC.NoExt
      , Expr.mg_alts =
          GHC.noLoc
            [ GHC.noLoc
                Expr.Match
                  { Expr.m_ext = GHC.NoExt
                  , Expr.m_ctxt = Expr.LambdaExpr
                  , Expr.m_pats =
                      [ GHC.noLoc
                          ( Pat.VarPat GHC.NoExt
                              ( GHC.noLoc ( GHC.idName name ) )
                          )
                      ]
                  , Expr.m_grhss = GHC.unguardedGRHSs ( GHC.noLoc e )
                  }
            ]
      , Expr.mg_origin = GHC.Generated
      }
