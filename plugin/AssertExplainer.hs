{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}

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
import qualified HsUtils
import qualified CoreUtils
import qualified Id as GHC
import qualified Desugar as GHC
import qualified Finder as GHC
import qualified GHC
import qualified GhcPlugins as GHC
import qualified HsExpr as Expr
import qualified HsPat as Pat
import qualified IfaceEnv as GHC
import qualified PrelNames as GHC
import qualified TcEnv as GHC
import qualified TcEvidence as GHC
import qualified TcExpr as GHC
import qualified TcHsSyn as GHC
import qualified TcRnMonad as GHC
import qualified TcSimplify as GHC
import qualified TcType as GHC
import qualified TcSMonad as GHC ( runTcS )

-- syb
import Data.Generics ( everywhereM, listify, mkM )


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


explainAssertions :: GHC.ModSummary -> GHC.TcGblEnv -> GHC.TcM GHC.TcGblEnv
explainAssertions _modSummary tcGblEnv = do 
  hscEnv <-
    GHC.getTopEnv

  GHC.Found _ assertExplainerModule <-
    liftIO ( GHC.findImportedModule hscEnv ( GHC.mkModuleName "AssertExplainer" ) Nothing )

  names <- do
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
  let 
    diagnosticArgs =
      GHC.mkTemplateLocals ( typedExprType <$> showableSubExpresions )

    diagnose te name =
      Expr.BodyStmt GHC.NoExt 
        ( GHC.noLoc
            ( Expr.HsApp GHC.NoExt
                ( GHC.noLoc
                    ( Expr.HsVar GHC.NoExt ( GHC.noLoc ( hs_print names ) ) )
                )
                ( GHC.noLoc
                    ( Expr.HsApp GHC.NoExt
                        ( GHC.noLoc
                            ( Expr.HsApp GHC.NoExt
                                ( GHC.noLoc
                                    ( Expr.HsVar GHC.NoExt
                                        ( GHC.noLoc GHC.mappendName )
                                    )
                                )
                                ( GHC.noLoc
                                    ( Expr.HsLit GHC.NoExt
                                        ( GHC.HsString
                                            GHC.NoSourceText
                                            ( GHC.fsLit ( GHC.renderWithStyle GHC.unsafeGlobalDynFlags ( GHC.ppr ( typedExpr te ) ) ( GHC.defaultUserStyle GHC.unsafeGlobalDynFlags ) ++ " = " ) )
                                        )
                                    )
                                )
                            )
                        )
                        ( GHC.noLoc
                            ( Expr.HsApp GHC.NoExt
                                ( GHC.noLoc ( Expr.HsVar GHC.NoExt ( GHC.noLoc ( hs_show names ) ) ) )
                                ( GHC.noLoc ( Expr.HsVar GHC.NoExt ( GHC.noLoc ( GHC.idName name ) ) ) )
                            )
                        )
                    )
                )
            )
        )
        ( GHC.mkRnSyntaxExpr GHC.thenIOName )
        Expr.noSyntaxExpr

    diagnosticFunction = 
      foldl'
        ( \e name -> abstract name e )
        ( Expr.HsDo GHC.NoExt
            Expr.DoExpr
            ( GHC.noLoc
                ( map
                    GHC.noLoc
                    ( zipWith diagnose showableSubExpresions diagnosticArgs
                        ++
                          [ Expr.LastStmt GHC.NoExt
                              ( GHC.noLoc ( returnUnit names ) )
                              False
                              Expr.noSyntaxExpr
                          ]
                    )
                ) 
            ) 
        )
        ( reverse diagnosticArgs )

  -- Build the type of the diagnostic function
  let
    fTy =
      foldr
        GHC.mkFunTy
        ( GHC.mkTyConApp ( hs_IO names ) [ GHC.mkTyConTy GHC.unitTyCon ] )
        ( map typedExprType showableSubExpresions )

  ( GHC.L _ ifExpr', wanteds ) <-
    GHC.captureConstraints
      ( GHC.tcMonoExpr
        ( GHC.noLoc diagnosticFunction )
        ( GHC.Check fTy )
      )

  wrapper <-
    GHC.mkWpLet . GHC.EvBinds . GHC.evBindMapBinds . snd <$> GHC.runTcS ( GHC.solveWanteds wanteds )

  GHC.zonkTopLExpr
    ( foldl
        ( \a b -> GHC.noLoc ( Expr.HsApp GHC.NoExt a b ) )
        ( GHC.noLoc ( Expr.HsWrap GHC.NoExt wrapper ifExpr' ) )
        ( map ( GHC.noLoc . typedExpr ) showableSubExpresions )
    )


isHsExpr :: Expr.HsExpr GHC.GhcTc -> Bool 
isHsExpr ( Expr.HsPar{} ) =
  False
isHsExpr ( Expr.HsLit{} ) =
  False
isHsExpr ( Expr.HsOverLit{} ) =
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
              
