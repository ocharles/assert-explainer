{-# LANGUAGE TemplateHaskell #-}

module AssertExplainer where

import Control.Arrow (second)
import Data.Generics hiding (mkTyConApp)
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

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo =
  return (CoreDoPluginPass "assert-explainer" explain : todo)

explain :: ModGuts -> CoreM ModGuts
explain guts = do
  mg_binds' <- everywhereM (mkM (rewriteAssert guts)) (mg_binds guts)
  return guts { mg_binds = mg_binds' }

isAssert :: Var -> Bool
isAssert v =
  moduleNameString (moduleName (nameModule (varName v))) == "AssertExplainer" &&
  occNameString (nameOccName (varName v)) == "assert"

rewriteAssert :: ModGuts -> Expr CoreBndr -> CoreM (Expr CoreBndr)
rewriteAssert guts e =
  case e of
    App (Var v) body | isAssert v -> do
      putMsg $ pprCoreExpr body
      name <- mkSysLocalM (fsLit "foo") (exprType body)
      (trueDatacon, trueId) <- do
        Just trueName <- thNameToGhcName 'True
        (,) <$> lookupDataCon trueName <*> lookupId trueName
      falseDatacon <- do
        Just falseName <- thNameToGhcName 'False
        lookupDataCon falseName
      result <-
        Case body name (exprType (App (Var v) body))
          <$> sequence
            [ (,,) <$> pure (DataAlt falseDatacon) <*> pure [] <*> explainFvs guts body
            , pure (DataAlt trueDatacon, [], App (Var v) (Var trueId))
            ]
      putMsg $ pprCoreExpr result
      return result
    _ -> return e

explainFvs :: ModGuts -> Expr CoreBndr -> CoreM (Expr CoreBndr)
explainFvs guts body = do
  putStrLnId <- nameToId 'putStrLn
  showId <- nameToId 'show
  concatId <- nameToId '(++)
  explains <- for (uniqSetToList (exprFreeVars body)) $ \v -> do
    prefix <- mkStringExpr (occNameString (nameOccName (varName v)) ++ ": ")
    showTyCon <- do
      Just name <- thNameToGhcName ''Show
      lookupTyCon name
    dict <- getDictionary guts (mkTyConApp showTyCon [ exprType (Var v)])
    return $ App (Var putStrLnId) $
      Var concatId
        `App` Type (exprType (mkCharExpr 'a'))
        `App` prefix
        `App` (Var showId `App` Type (exprType (Var v)) `App` dict `App` Var v)

  bind <- do
    monad <- do
      Just name <- thNameToGhcName ''Monad
      lookupTyCon name
    io <- do
      Just name <- thNameToGhcName ''IO
      lookupTyCon name
    bind <- nameToId '(>>)
    ioDict <- getDictionary guts (mkTyConApp monad [mkTyConTy io])
    let unmonad = snd . splitAppTy
    return $ \a b ->
      Var bind
        `App` Type (mkTyConTy io)
        `App` ioDict
        `App` Type (unmonad $ exprType a)
        `App` Type (unmonad $ exprType b)
        `App` a
        `App` b

  return (foldl1 bind explains)

nameToId :: TH.Name -> CoreM Id
nameToId n = do
  Just name <- thNameToGhcName n
  lookupId name

occAttributes :: OccName -> String
occAttributes o = "(" ++ ns ++ vo ++ tv ++ tc ++ d ++ ds ++ s ++ v ++ ")"
  where
    ns = (showSDocUnsafe $ pprNameSpaceBrief $ occNameSpace o) ++ ", "
    vo = if isVarOcc     o then "Var "     else ""
    tv = if isTvOcc      o then "Tv "      else ""
    tc = if isTcOcc      o then "Tc "      else ""
    d  = if isDataOcc    o then "Data "    else ""
    ds = if isDataSymOcc o then "DataSym " else ""
    s  = if isSymOcc     o then "Sym "     else ""
    v  = if isValOcc     o then "Val "     else ""


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

--         liftIO $ do
--             putStrLn $ "dictType="++showSDoc dflags (ppr dictType)
--             putStrLn $ "dictVar="++showSDoc dflags (ppr dictVar)
--
--             putStrLn $ "nonC="++showSDoc dflags (ppr nonC)
--             putStrLn $ "wCs="++showSDoc dflags (ppr wCs)
--             putStrLn $ "bnds="++showSDoc dflags (ppr bnds)
--             putStrLn $ "x="++showSDoc dflags (ppr x)

        return bnds

    case bnds of
      [NonRec _ dict] -> return dict
      _ -> do
        dynFlags <- getDynFlags
        error $ showSDoc dynFlags (ppr dictTy)

assert :: Bool -> IO ()
assert True = return ()
assert False = putStrLn "Assertion failed!"
