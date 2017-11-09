{-# LANGUAGE TemplateHaskell #-}

module AssertExplainer where

import Data.Traversable
import Class
import DsBinds
import DsMonad
import GhcPlugins hiding (trace)
import Unique
import MkId
import PrelNames
import UniqSupply
import TcRnMonad
import TcSimplify
import Type
import HERMIT.GHC.TypeChecker
import ErrUtils (pprErrMsgBagWithLoc)
import DsMonad
import TcSMonad
import DsBinds
import Control.Arrow (second)
import TcSimplify
import TcEvidence
import TcRnMonad
import TcRnTypes
import PprCore (pprCoreExpr)
import Data.Data hiding (mkTyConApp)
import Data.Generics hiding (mkTyConApp)
import GhcPlugins

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
      liftIO $ putStrLn (showExpr 0 body)
      putMsg $ pprCoreExpr body
      name <- mkSysLocalM (fsLit "foo") (exprType body)
      (trueDatacon, trueId) <- do
        Just trueName <- thNameToGhcName 'True
        (,) <$> lookupDataCon trueName <*> lookupId trueName
      (falseDatacon, falseId) <- do
        Just falseName <- thNameToGhcName 'False
        (,) <$> lookupDataCon falseName <*> lookupId falseName
      bind <- do
        Just bindName <- thNameToGhcName '(>>)
        lookupId bindName
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
  let stringType = exprType (Lit (mkMachString ""))
  explains <- for (uniqSetToList (exprFreeVars body)) $ \v -> do
      prefix <- mkStringExpr (occNameString (nameOccName (varName v)) ++ ": ")
      show <- do
        Just name <- thNameToGhcName ''Show
        lookupTyCon name
      dict <- getDictionary guts (mkTyConApp show [ exprType (Var v)])
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
    liftIO $ putStrLn $ showExpr 0  (mkTyConApp monad [mkTyConTy io])
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


nameToId n = do
  Just name <- thNameToGhcName n
  lookupId name

showExpr :: Data a => Int -> a -> String
showExpr n =
  generic `extQ` machStr
          `extQ` name `extQ` occName `extQ` moduleName `extQ` var `extQ` dataCon
  where generic :: Data a => a -> String
        generic t = indent n ++ "(" ++ showConstr (toConstr t)
                 ++ space (unwords (gmapQ (showExpr (n+1)) t)) ++ ")"
        space "" = ""
        space s  = ' ':s
        indent i = "\n" ++ replicate i ' '
        string     = show :: String -> String

        machStr (MachStr _) = "<<MachStr>>"
        machStr a = generic a

        showSDoc_ = showSDoc unsafeGlobalDynFlags

        name       = ("{Name: "++) . (++"}") . showSDoc_ . ppr :: Name -> String
        occName o   = "{OccName: "++ occNameString o ++ " " ++ occAttributes o ++ "}"
        moduleName = ("{ModuleName: "++) . (++"}") . showSDoc_ . ppr :: ModuleName -> String
        var        = ("{Var: "++) . (++"}") . showSDoc_ . ppr :: Var -> String
        dataCon    = ("{DataCon: "++) . (++"}") . showSDoc_ . ppr :: DataCon -> String

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
        (x, evBinds) <- second evBindMapBinds <$> runTcS (solveWanteds wCs)
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
        otherwise -> do
          dynFlags <- getDynFlags
          error $ showSDoc dynFlags (ppr dictTy)

assert :: Bool -> IO ()
assert True = return ()
assert False = putStrLn "Assertion failed!"
