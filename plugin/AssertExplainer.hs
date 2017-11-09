{-# LANGUAGE TemplateHaskell #-}

module AssertExplainer (plugin, assert) where

import qualified Explain

import Control.Arrow (second)
import Data.Generics hiding (mkTyConApp, TyCon)
import Data.Traversable
import DsBinds
import DsMonad
import ErrUtils (pprErrMsgBagWithLoc)
import GhcPlugins
import HERMIT.GHC.TypeChecker
import qualified Language.Haskell.TH.Syntax as TH
import PprCore (pprCoreExpr)
import TcEvidence
import TcRnMonad
import TcSMonad
import TcSimplify
import Unique

-- | The @assert-explainer@ plugin intercepts calls to 'assert' and tries to
-- explain them if they fail. You can use this plugin by depending on the
-- @assert-explainer@ library, and then adding:
--
-- @{-# OPTIONS -fplugin=AssertExplainer #-}@
--
-- to your test pragmas.
plugin :: Plugin
plugin =
  defaultPlugin { installCoreToDos = install }


install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo =
  return (CoreDoPluginPass "assert-explainer" explain : todo)


-- | A core-to-core pass that finds 'assert' calls and adds failure reasoning.
explain :: ModGuts -> CoreM ModGuts
explain guts = do
  mg_binds' <- everywhereM (mkM (rewriteAssert guts)) (mg_binds guts)
  return guts { mg_binds = mg_binds' }


-- | Rewrite an 'assert' call into further analysis on the expression being asserted.
rewriteAssert :: ModGuts -> Expr CoreBndr -> CoreM (Expr CoreBndr)
rewriteAssert guts e = do
  assertId <- nameToId 'assert
  case e of
    App (Var v) body | v == assertId -> do
      name <- mkSysLocalM (fsLit "assertBody") (exprType body)
      id'True <- nameToId 'True
      dataCon'True <- nameToDatacon 'True
      dataCon'False <- nameToDatacon 'False
      expr'bind <- mkBind guts
      result <-
        Case body name (exprType (App (Var v) body))
          <$> sequence
            [ (,,) <$> pure (DataAlt dataCon'False) <*> pure [] <*> (expr'bind <$> explainFvs guts body <*> pure e)
            , pure (DataAlt dataCon'True, [], App (Var v) (Var id'True))
            ]
      putMsg $ pprCoreExpr result
      return result
    _ -> return e


-- | Given any expression, try and 'Show' all of the free variables.
explainFvs :: ModGuts -> Expr CoreBndr -> CoreM (Expr CoreBndr)
explainFvs guts body = do
  putStrLnId <- nameToId 'putStrLn
  explains <- for (uniqSetToList (exprFreeVars body)) $ \v -> do
    expr'varName <- mkStringExpr (occNameString (nameOccName (varName v)))
    tyCon'Show <- nameToTyCon ''Show
    dict <- getDictionary guts (mkTyConApp tyCon'Show [ exprType (Var v)])
    id'explainShow <- nameToId 'Explain.explainShow
    return $ App (Var putStrLnId) $
      Var id'explainShow
        `App` Type (exprType (Var v))
        `App` dict
        `App` expr'varName
        `App` Var v

  bind <- mkBind guts
  return (foldl1 bind explains)


-- | A macro to produce 'IO' sequencing with '(>>)'.
mkBind :: ModGuts -> CoreM (CoreExpr -> CoreExpr -> CoreExpr)
mkBind guts = do
  tyCon'Monad <- nameToTyCon ''Monad
  tyCon'IO <- nameToTyCon ''IO
  id'bind <- nameToId '(>>)
  ioDict <- getDictionary guts (mkTyConApp tyCon'Monad [mkTyConTy tyCon'IO])
  let unMonad = snd . splitAppTy
  return $ \a b ->
    Var id'bind
      `App` Type (mkTyConTy tyCon'IO)
      `App` ioDict
      `App` Type (unMonad $ exprType a)
      `App` Type (unMonad $ exprType b)
      `App` a
      `App` b


nameToId :: TH.Name -> CoreM Id
nameToId n = do
  Just name <- thNameToGhcName n
  lookupId name


nameToDatacon :: TH.Name -> CoreM DataCon
nameToDatacon n = do
  Just trueName <- thNameToGhcName n
  lookupDataCon trueName


nameToTyCon :: TH.Name -> CoreM TyCon
nameToTyCon n = do
  Just trueName <- thNameToGhcName n
  lookupTyCon trueName


--------------------------------------------------------------------------------

-- Blindly copied from HERMIT & Herbie

runTcM :: ModGuts -> TcM a -> CoreM a
runTcM guts m = do
  env <- getHscEnv
  dflags <- getDynFlags
  -- What is the effect of HsSrcFile (should we be using something else?)
  -- What should the boolean flag be set to?
  (msgs, mr) <- liftIO $ initTcFromModGuts env guts HsSrcFile False m
  let showMsgs (warns, errs) = showSDoc dflags $ vcat
                                               $    text "Errors:" : pprErrMsgBagWithLoc errs
                                                 ++ text "Warnings:" : pprErrMsgBagWithLoc warns
  maybe (fail $ showMsgs msgs) return mr

getDictionary :: ModGuts -> Type -> CoreM CoreExpr
getDictionary guts dictTy = do
    let dictVar = mkGlobalVar
            VanillaId
            (mkSystemName (mkUnique 'z' 1337) (mkVarOcc "magicDictionaryName"))
            dictTy
            vanillaIdInfo

    bnds <- runTcM guts $ do
        loc <- getCtLocM (GivenOrigin UnkSkol) Nothing
        let nonC = mkNonCanonical CtWanted
                { ctev_pred = varType dictVar
                , ctev_dest = EvVarDest dictVar
                , ctev_loc = loc
                }
            wCs = mkSimpleWC [cc_ev nonC]
        (_, evBinds) <- second evBindMapBinds <$> runTcS (solveWanteds wCs)
        bnds <- initDsTc $ dsEvBinds evBinds

        return bnds

    case bnds of
      [NonRec _ dict] -> return dict
      _ -> do
        dynFlags <- getDynFlags
        error $ showSDoc dynFlags (ppr dictTy)

-- | Assert that a 'Bool' expression is true. Throws if the expression
-- is not true.
assert :: Bool -> IO ()
assert True = return ()
assert False = error "Assertion failed!"
