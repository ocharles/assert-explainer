{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module AssertExplainer ( plugin, assert ) where

-- assert-explainer
import qualified Constraint

-- base
import Data.Bool ( bool )
import Data.List ( foldl' )
import Control.Monad ( guard )
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

-- syb
import Data.Generics ( everywhereM, listify, mkM )

-- template-haskell
import Language.Haskell.TH as TH


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


explainAssertions :: GHC.ModSummary -> GHC.TcGblEnv -> GHC.TcM GHC.TcGblEnv
explainAssertions _modSummary tcGblEnv = do 
  tcg_binds <-
    mkM rewriteAssert `everywhereM` GHC.tcg_binds tcGblEnv

  return tcGblEnv { GHC.tcg_binds = tcg_binds }


assert :: Bool -> IO ()
assert =
  bool ( fail "Assertion failed!" ) ( return () )


-- | Rewrite an 'assert' call into further analysis on the expression being asserted.
rewriteAssert :: Expr.LHsExpr GHC.GhcTc -> GHC.TcM ( Expr.LHsExpr GHC.GhcTc )
rewriteAssert e@( GHC.L _ ( Expr.HsApp _ ( GHC.L _ ( Expr.HsVar _ ( GHC.L _ v ) ) ) ( GHC.L _ body ) ) ) = do
  hscEnv <-
    GHC.getTopEnv

  GHC.Found _ assertExplainerModule <-
    liftIO ( GHC.findImportedModule hscEnv ( GHC.mkModuleName "AssertExplainer" ) Nothing )

  assertName <-
    GHC.lookupId
      =<< GHC.lookupOrig assertExplainerModule ( GHC.mkVarOcc "assert" )

  if v == assertName then
    explain body
  else
    return e

rewriteAssert e =
  return e


data Typed = Typed
  { typedExpr :: Expr.HsExpr GHC.GhcTcId
  , typedExprType :: GHC.Type
  }
  

explain :: Expr.HsExpr GHC.GhcTc -> GHC.TcM ( Expr.LHsExpr GHC.GhcTc )
explain toExplain = do
  -- Find all sub-expressions in the body
  let
    subExpressions =
      listify isHsExpr toExplain

  -- Augment each sub-expression with its type
  typedSubExpressions <-
    catMaybes <$> traverse toTyped subExpressions

  -- Filter the list of sub-expressions to just those that can be shown.
  showableSubExpresions <-
    catMaybes <$> traverse witnessShow typedSubExpressions

  -- Build an anonymous function to describe all of these subexpressions
  Right expr <-
    fmap ( GHC.convertToHsExpr GHC.noSrcSpan )
      $ liftIO
      $ TH.runQ
      $ do
          diagnosticArgs <-
            sequence ( TH.newName "x" <$ showableSubExpresions )

          let
            diagnose te name =
              TH.noBindS ( diagnoseExpr te name )

            diagnosed =
              zipWith diagnose showableSubExpresions diagnosticArgs

          foldl'
            ( \e name -> TH.lam1E ( TH.varP name ) e )
            ( TH.doE diagnosed )
            ( reverse diagnosticArgs )

  -- Rename the Template Haskell source
  ( diagnosticFunction, _ ) <-
    GHC.rnLExpr expr

  -- Build the type of the diagnostic function...
  diagnosticFunctionT <- do
    io <-
      GHC.lookupTyCon ( GHC.ioTyConName )

    return
      ( foldr
          GHC.mkFunTy
          ( GHC.mkTyConApp io [ GHC.mkTyConTy GHC.unitTyCon ] )
          ( map typedExprType showableSubExpresions ) 
      )

  -- Type check our diagnostic function to find which dictionaries need to be
  -- resolved.
  ( ifExpr', wanteds ) <-
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
        GHC.mkHsApp
        ( GHC.mkLHsWrap wrapper ifExpr' )
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


-- | Given a type-checked expression, pair the expression up with its Type.
toTyped :: Expr.HsExpr GHC.GhcTc -> GHC.TcM ( Maybe Typed )
toTyped e = do
  hs_env  <-
    GHC.getTopEnv

  ( _, mbe ) <-
    liftIO ( GHC.deSugarExpr hs_env ( GHC.noLoc e ) )

  return ( ( \x -> Typed e ( CoreUtils.exprType x ) ) <$> mbe )


-- | Given a typed expression, ensure that it has a Show instance.
witnessShow :: Typed -> GHC.TcM ( Maybe Typed )
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

  return ( tExpr <$ guard ( not ( null ( toList evBinds ) ) ) )
