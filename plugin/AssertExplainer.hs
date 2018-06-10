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

-- prettyprinter
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Text.Prettyprint.Doc.Render.Text as PP

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
  hscEnv <-
    GHC.getTopEnv

  GHC.Found _ assertExplainerModule <-
    liftIO ( GHC.findImportedModule hscEnv ( GHC.mkModuleName "AssertExplainer" ) Nothing )

  assertName <-
    GHC.lookupId
      =<< GHC.lookupOrig assertExplainerModule ( GHC.mkVarOcc "assert" )

  tcg_binds <-
    mkM ( rewriteAssert assertName ) `everywhereM` GHC.tcg_binds tcGblEnv

  return tcGblEnv { GHC.tcg_binds = tcg_binds }


assert :: Bool -> IO ()
assert =
  bool ( fail "Assertion failed!" ) ( return () )


-- | Rewrite an 'assert' call into further analysis on the expression being asserted.
rewriteAssert :: GHC.Id -> Expr.LHsExpr GHC.GhcTc -> GHC.TcM ( Expr.LHsExpr GHC.GhcTc )
rewriteAssert assertName ( GHC.L _ ( Expr.HsApp _ ( GHC.L _ ( Expr.HsVar _ ( GHC.L _ v ) ) ) body ) ) | assertName == v = do
  explain body
rewriteAssert _ e =
  return e


data Typed = Typed
  { typedExpr :: Expr.LHsExpr GHC.GhcTcId
  , typedExprType :: GHC.Type
  }


explain :: Expr.LHsExpr GHC.GhcTc -> GHC.TcM ( Expr.LHsExpr GHC.GhcTc )
explain toExplain = do
  -- Find all sub-expressions in the body
  let
    subExpressions =
      listify isInterestingSubexpr toExplain

  -- Augment each sub-expression with its type
  typedSubExpressions <-
    catMaybes <$> traverse toTyped subExpressions

  -- Filter the list of sub-expressions to just those that can be shown.
  given:showableSubExpresions <-
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
              case zipWith diagnose showableSubExpresions diagnosticArgs of
                [] ->
                  []

                diags ->
                  [ TH.noBindS
                      ( TH.doE
                          ( TH.noBindS [| putStrLn "I found the following sub-expressions:" |]
                              : diags
                          )
                      )
                  ]

          topName <-
            TH.newName "x"

          TH.lam1E
            ( TH.varP topName )
            ( foldl'
                ( \e name -> TH.lam1E ( TH.varP name ) e )
                ( TH.condE
                    ( TH.varE topName )
                    [| return () |]
                    ( TH.doE ( assertionFailed given : diagnosed ) )
                )
                ( reverse diagnosticArgs )
            )

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
          ( map
              typedExprType
              ( given : showableSubExpresions )
          )
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
  evBinds <-
    GHC.EvBinds . GHC.evBindMapBinds . snd
      <$> GHC.runTcS ( GHC.solveWanteds wanteds )

  ( _, zonkedEvBinds ) <-
    GHC.zonkTcEvBinds GHC.emptyZonkEnv evBinds

  let
    wrapper =
      GHC.mkWpLet zonkedEvBinds

  -- Apply the wrapper to our type checked syntax and fully saturate the
  -- diagnostic function with the necessary arguments.
  GHC.zonkTopLExpr
    ( foldl
        GHC.mkHsApp
        ( GHC.mkLHsWrap wrapper ifExpr' )
        ( map
            typedExpr
            ( given : showableSubExpresions )
        )
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
  -- [| PP.putDoc ( PP.pretty ppExpr <> " = " <> PP.pretty ( show $( TH.varE name ) ) ) |]
  [| putStrLn ( "  - " <> ppExpr <> " = " <> show $( TH.varE name ) ) |]


assertionFailed :: Typed -> TH.StmtQ
assertionFailed te =
  let
    ppExpr =
      GHC.renderWithStyle
        GHC.unsafeGlobalDynFlags
        ( GHC.ppr ( typedExpr te ) )
        ( GHC.defaultUserStyle GHC.unsafeGlobalDynFlags )

    srcLoc =
      GHC.renderWithStyle
        GHC.unsafeGlobalDynFlags
        ( GHC.ppr ( case typedExpr te of GHC.L l _ -> l ) )
        ( GHC.defaultUserStyle GHC.unsafeGlobalDynFlags )
    
  in
  TH.noBindS
    [| do
         putStrLn ( "Assertion failed! " <> ppExpr <> " /= True (at " <> srcLoc <> ")" )
         putStrLn ""
    |]


isInterestingSubexpr :: Expr.LHsExpr GHC.GhcTc -> Bool
isInterestingSubexpr ( GHC.L _ Expr.HsPar{} ) =
  False
isInterestingSubexpr ( GHC.L _ Expr.HsLit{}) =
  False
isInterestingSubexpr ( GHC.L _ Expr.HsOverLit{} ) =
  False
isInterestingSubexpr ( GHC.L _ Expr.HsWrap{} ) =
  False
isInterestingSubexpr _ =
  True


-- | Given a type-checked expression, pair the expression up with its Type.
toTyped :: Expr.LHsExpr GHC.GhcTc -> GHC.TcM ( Maybe Typed )
toTyped e = do
  hs_env  <-
    GHC.getTopEnv

  ( _, mbe ) <-
    liftIO ( GHC.deSugarExpr hs_env e )

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
