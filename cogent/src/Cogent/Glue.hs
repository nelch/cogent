--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{- LANGUAGE FlexibleContexts -}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{- LANGUAGE LiberalTypeSynonyms -}
{- LANGUAGE MultiParamTypeClasses -}
{-# LANGUAGE MultiWayIf #-}
{- LANGUAGE OverlappingInstances -}
{-# LANGUAGE PackageImports #-}
{- LANGUAGE RankNTypes -}
{- LANGUAGE ScopedTypeVariables -}
{- LANGUAGE StandaloneDeriving -}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wwarn #-}

module Cogent.Glue where

import qualified Cogent.C.Compile as CG
import qualified Cogent.C.Render  as CG
import qualified Cogent.C.Syntax  as CG
import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Compiler
import qualified Cogent.Context   as Ctx
import qualified Cogent.Core      as CC
import qualified Cogent.Desugar   as DS
import qualified Cogent.Inference as IN
import qualified Cogent.Mono      as MN
import qualified Cogent.Parser    as PS
import           Cogent.PrettyPrint
import qualified Cogent.Surface   as SF
import qualified Cogent.TypeCheck.Assignment as TC
import qualified Cogent.TypeCheck.Base       as TC
import qualified Cogent.TypeCheck.Generator  as TC hiding (validateType)
import qualified Cogent.TypeCheck.Post       as TC
import qualified Cogent.TypeCheck.Solver     as TC
import qualified Cogent.TypeCheck.Subst      as TC
-- import qualified Cogent.TypeCheck.Util      as TC
import           Cogent.Util
import qualified Data.DList as DList
import           Data.Ex
import           Data.Nat (Nat(Zero,Suc))
import           Data.Vec as Vec hiding (repeat)

import           Control.Applicative
import           Control.Arrow (Arrow(..), second, (&&&))
import           Control.Monad.Except hiding (sequence, mapM_, mapM)
import           Control.Monad.Reader
import           Control.Monad.RWS.Strict
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Maybe
-- import Control.Monad.Writer
import qualified Data.ByteString.Char8 as B
-- import Data.Either (lefts)
import           Data.Data
import           Data.Generics
-- import qualified Data.IntMap as IM
import           Data.Loc
import           Data.List as L
import           Data.Map as M
import           Data.Maybe (fromJust, fromMaybe, isJust, maybe)
import qualified Data.Sequence as Seq
import           Data.Set as S
import           Language.C.Parser as CP hiding (parseExp, parseType)
-- import Language.C.Parser.Tokens as CT
import           Language.C.Syntax as CS
import           Lens.Micro
import           Lens.Micro.Mtl
import           Lens.Micro.TH
import           System.FilePath (replaceBaseName, replaceExtension, takeBaseName, takeExtension, (<.>))
import           Text.Parsec.Pos (newPos, SourcePos)
import           Text.Parsec.Prim as PP hiding (State)
import           Text.PrettyPrint.ANSI.Leijen (vsep)
import           Unsafe.Coerce

-- import           Debug.Trace

-- Parsing

parseFile :: [Extensions] -> [String] -> FilePath -> ExceptT String IO [CS.Definition]
parseFile exts deftypnames filename = do
#if MIN_VERSION_language_c_quote(0,11,1)
  let start = Just $ startPos filename
#else
  let start = startPos filename
#endif
  s <- lift $ B.readFile filename
  typnames <- case __cogent_ext_types of Nothing -> lift (return deftypnames); Just f -> lift $ getTypnames f
  case CP.evalP (__fixme CP.parseUnit) (CP.emptyPState exts typnames s start) of -- FIXME: check for other antiquotes
    Left err -> throwE $ "Error: Failed to parse C: " ++ show err
    Right ds -> return ds

defaultExts :: [Extensions]
defaultExts = [Antiquotation, C99, Gcc]

defaultTypnames :: [String]
defaultTypnames = []

getTypnames :: FilePath -> IO [String]
getTypnames = liftA lines . readFile


-- Another parser
{-
parseFile' :: FilePath -> ExceptT String IO CTranslUnit
parseFile' filename = do
  instream <- lift $ readInputStream filename
  let pos = initPos filename
  case parseC instream pos of
    Left err -> throwE $ "Error: Failed to parse C: " ++ show err
    Right u  -> return u
-}

-- Desugaring, Monomorphising, and CG

data TcState = TcState { _tfuncs :: Map FunName (SF.Polytype TC.TCType)
                       , _ttypes :: TC.TypeDict
                       , _consts :: Map VarName (TC.TCType, TC.TCExpr, SourcePos)
                       }

data DsState = DsState { _typedefs  :: DS.Typedefs
                       , _constdefs :: DS.Constants
                       }

data CoreTcState = CoreTcState { _funtypes :: Map FunName CC.FunctionType }

data MnState = MnState { _funMono  :: MN.FunMono
                       , _typeMono :: MN.TypeMono
                       }

data CgState = CgState { _cTypeDefs    :: [(CG.StrlType, CG.CId)]
                       , _cTypeDefMap  :: M.Map CG.StrlType CG.CId
                       , _typeSynonyms :: M.Map TypeName CG.CType
                       , _typeCorres   :: DList.DList (CG.CId, CC.Type 'Zero)
                       , _absTypes     :: M.Map TypeName (S.Set [CG.CId])
                       , _custTypeGen  :: M.Map (CC.Type 'Zero) (CG.CId, CustTyGenInfo)
                       , _funClasses   :: CG.FunClass
                       , _localOracle  :: Integer  -- FIXME: should be moved to DefnState
                       , _globalOracle :: Integer
                       }

data GlState = GlState { _tcDefs   :: [SF.TopLevel SF.RawType TC.TypedPatn TC.TypedExpr]
                       , _tcState  :: TcState
                       , _dsState  :: DsState
                       , _coreTcState  :: CoreTcState
                       , _mnState  :: MnState
                       , _cgState  :: CgState
                       }

data FileState = FileState { _file :: FilePath }

data DefnState t = DefnState { _kenv :: Vec t (TyVarName, Kind)
                             , _ectx :: [TC.ErrorContext]
                             }

data MonoState = MonoState { _inst :: (MN.Instance, Maybe Int) }  -- Either ([], Nothing), or (_:_, Just _)

makeLenses ''TcState
makeLenses ''DsState
makeLenses ''CoreTcState
makeLenses ''MnState
makeLenses ''CgState
makeLenses ''GlState
makeLenses ''FileState
makeLenses ''DefnState
makeLenses ''MonoState

type GlMono t = ReaderT (MonoState  ) (GlDefn t)
type GlDefn t = ReaderT (DefnState t) (GlFile  )
type GlFile   = ReaderT (FileState  ) (Gl      )
type Gl       = StateT  (GlState    ) (GlErr   )
type GlErr    = ExceptT (String     ) (IO      )


-- Monad transformers

-- NOTE: The 4th argument @offset'@ is used to produce more accurate source positions.
-- It also helps work around the @avoidInitial@ when parsing things. / zilinc
parseAnti :: String -> PP.Parsec String () a -> SrcLoc -> Int -> GlFile a
parseAnti s parsec loc offset' = do
  filename <- view file
  let pos = case loc of
              SrcLoc (Loc (Pos _ line col offset) _) -> newPos filename line (col + offset + offset')
              SrcLoc NoLoc -> newPos filename 0 0
  case PP.parse (PP.setPosition pos >> parsec) filename s of
    Left err -> throwError $ "Error: Cannot parse antiquote: \n" ++ show err
    Right t  -> return t

tcAnti :: (a -> TC.TcM b) -> a -> GlDefn t b
tcAnti f a = lift . lift $
  StateT $ \s -> let state = TC.TcState { TC._knownFuns    = view (tcState.tfuncs) s
                                        , TC._knownTypes   = view (tcState.ttypes) s
                                        , TC._knownConsts  = view (tcState.consts) s
                                        , TC._knownReps    = M.empty -- FIXME: Not sure what I'm doing here /liamoc
                                        }
                     turn :: s -> (Maybe b, TC.TcLogState) -> Either String (b,s)
                     turn s (Just x, TC.TcLogState l _) = Right (x,s)  -- FIXME: ignore warnings atm / zilinc
                     turn _ (_, TC.TcLogState l _) = Left $ "Error: Typecheck antiquote failed:\n" ++
                                         show (vsep $ L.map (prettyTWE __cogent_ftc_ctx_len) l)
                                         -- FIXME: may need a pp modifier `plain' / zilinc
                  in ExceptT $ fmap (turn s) (flip evalStateT state .
                                              flip runStateT mempty .
                                              runMaybeT $ f a)

desugarAnti :: (a -> DS.DS t 'Zero b) -> a -> GlDefn t b
desugarAnti m a = view kenv >>= \(fmap fst -> ts) -> lift . lift $
  StateT $ \s -> let tdefs = view (dsState.typedefs ) s
                     cdefs = view (dsState.constdefs) s
                  in return (fst (flip3 evalRWS (DS.DsState ts Nil 0 0 []) (tdefs, cdefs, []) $ DS.runDS $ m a), s)  -- FIXME: pragmas / zilinc

coreTcAnti :: (a -> IN.TC t 'Zero b) -> a -> GlDefn t b
coreTcAnti m a = view kenv >>= \(fmap snd -> ts) -> lift . lift $
  StateT $ \s -> let reader = (ts, view (coreTcState.funtypes) s)
                  in case flip evalState Nil $ flip runReaderT reader $ runExceptT $ IN.unTC $ m a of
                       Left  e -> __impossible "coreTcAnti"
                       Right x -> return (x, s)

monoAnti :: (a -> MN.Mono b) -> a -> GlMono t b
monoAnti m a = view (inst._1) >>= \is -> lift . lift . lift $
  StateT $ \s -> let fmono = view (mnState.funMono ) s
                     tmono = view (mnState.typeMono) s
                  in return (fst (flip3 evalRWS (fmono,tmono) is $ MN.runMono $ m a), s)

genAnti :: (a -> CG.Gen 'Zero b) -> a -> Gl b
genAnti m a =
  StateT $ \s -> let reader = Nil
                     state  = CG.GenState { CG._cTypeDefs    = view (cgState.cTypeDefs   ) s
                                          , CG._cTypeDefMap  = view (cgState.cTypeDefMap ) s
                                          , CG._typeSynonyms = view (cgState.typeSynonyms) s
                                          , CG._typeCorres   = view (cgState.typeCorres  ) s
                                          , CG._absTypes     = view (cgState.absTypes    ) s
                                          , CG._custTypeGen  = view (cgState.custTypeGen ) s
                                          , CG._funClasses   = view (cgState.funClasses  ) s
                                          , CG._localOracle  = view (cgState.localOracle ) s   -- FIXME
                                          , CG._globalOracle = view (cgState.globalOracle) s
                                          , CG._varPool      = M.empty
                                          , CG._ffiFuncs     = M.empty
                                          }
                  in return (fst $ evalRWS (CG.runGen $ m a) reader state, s)

traverseAnti :: (Typeable a, Data b, Monad m) => (a -> m a) -> b -> m b
traverseAnti m = everywhereM $ mkM $ m


-- Types

parseType :: String -> SrcLoc -> GlFile SF.LocType
parseType s loc = parseAnti s PS.monotype loc 4


tcType :: SF.LocType -> GlDefn t SF.RawType
tcType t = do
  tvs <- L.map fst <$> (Vec.cvtToList <$> view kenv)
  flip tcAnti t $ \t -> do TC.errCtx %= (TC.AntiquotedType t :)
                           t' <- TC.validateType tvs $ SF.stripLocT t
                           TC.postT t'

desugarType :: SF.RawType -> GlDefn t (CC.Type t)
desugarType = desugarAnti DS.desugarType

monoType :: CC.Type t -> GlMono t (CC.Type 'Zero)
monoType = monoAnti MN.monoType

genType :: CC.Type 'Zero -> Gl CG.CType
genType = genAnti CG.genType

transDeclSpec :: CS.DeclSpec -> GlMono t CS.DeclSpec
transDeclSpec (CS.AntiTypeDeclSpec strg qual s l) = do
  CS.DeclSpec [] [] tysp loc <- (fst . CG.splitCType) <$> (lift . lift . lift . genType =<<
    monoType =<< lift . desugarType =<< lift . tcType =<< (lift . lift) (parseType s l))
  return $ CS.DeclSpec strg qual tysp loc
transDeclSpec x = return x

transDecl :: CS.Decl -> GlMono t CS.Decl
transDecl (CS.AntiTypeDecl s l) =
  (snd . CG.splitCType) <$> (lift . lift . lift . genType =<< monoType =<< lift . desugarType =<< lift . tcType =<< (lift . lift) (parseType s l))
transDecl x = return x

transType :: CS.Type -> GlMono t CS.Type
transType (CS.AntiType s l) =
  CG.cType <$> (lift . lift . lift . genType =<< monoType =<< lift . desugarType =<< lift . tcType =<< (lift . lift) (parseType s l))
transType x = return x

traverseDeclSpec = traverseAnti transDeclSpec
traverseDecl     = traverseAnti transDecl
traverseType     = traverseAnti transType

-- Function calls

parseFnCall :: String -> SrcLoc -> GlFile SF.LocExpr
parseFnCall s loc = parseAnti s PS.basicExpr' loc 4

tcFnCall :: SF.LocExpr -> GlDefn t TC.TypedExpr
tcFnCall e = do
  f <- case e of
         SF.LocExpr _ (SF.TypeApp f ts _) -> return f  -- TODO: make use of Inline to perform glue code inlining / zilinc
         SF.LocExpr _ (SF.Var f) -> return f
         otherwise -> throwError $ "Error: Not a function in $exp antiquote"
  f `seq` tcExp e Nothing

genFn :: CC.TypedExpr 'Zero 'Zero VarName -> Gl CS.Exp
genFn = genAnti $ \case
  CC.TE t (CC.Fun fn _ _) -> return (CS.Var (CS.Id (CG.funEnum fn) noLoc) noLoc)
  _ -> __impossible "genFn"

genFnCall :: CC.Type 'Zero -> Gl CS.Exp
genFnCall = genAnti $ \t -> do
    enumt <- CG.typeCId t
    return (CS.Var (CS.Id (CG.funDispatch $ toCName enumt) noLoc) noLoc)

transFnCall :: CS.Exp -> GlMono t CS.Exp
transFnCall (CS.FnCall (CS.AntiExp fn loc1) [e] loc0) = do
  e'  <- lift . lift . lift . genFn =<< monoExp =<< lift . coreTcExp =<<
         lift . desugarExp =<< lift . tcFnCall =<< (lift . lift) (parseFnCall fn loc1)
  fn' <- lift . lift . lift . genFnCall =<< return . CC.exprType =<< monoExp =<< lift . coreTcExp =<<
         lift . desugarExp =<< lift . tcFnCall =<< (lift . lift) (parseFnCall fn loc1)
  return $ CS.FnCall fn' [e',e] loc0
transFnCall e = return e

transDispatch :: CS.Exp -> GlMono t CS.Exp
transDispatch (CS.FnCall (CS.Cast ty e1 loc1) [e2] loc0)
  | CS.Type dcsp decl loc2 <- ty
  , CS.AntiDeclSpec s loc3 <- dcsp = do
    disp <- lift . lift . lift . genFnCall =<< monoType =<< lift . desugarType =<<
            lift . tcType =<< (lift . lift) (parseType s loc3)
    return $ CS.FnCall disp [e1,e2] loc0
transDispatch e = return e

traverseFnCall   = traverseAnti transFnCall
traverseDispatch = traverseAnti transDispatch


-- Expressions

parseExp :: String -> SrcLoc -> GlFile SF.LocExpr
parseExp s loc = parseAnti s (PS.expr 1) loc 4

tcExp :: SF.LocExpr -> Maybe TC.TCType -> GlDefn t TC.TypedExpr
tcExp e mt = do
  base <- lift . lift $ use (tcState.consts)
  let ctx = Ctx.addScope (fmap (\(t,_,p) -> (t, p, Seq.singleton p)) base) Ctx.empty
  vs <- Vec.cvtToList <$> view kenv
  flip tcAnti e $ \e ->
    do let ?loc = SF.posOfE e
       TC.errCtx %= (TC.AntiquotedExpr e :)
       ((c,e'),flx,os) <- TC.runCG ctx (L.map fst vs) (TC.cg e =<< maybe TC.freshTVar return mt)
       (logs,subst,assign,_) <- TC.runSolver (TC.solve c) vs flx os
       TC.exitOnErr $ mapM_ TC.logTc logs
       TC.postE $ TC.applyE subst $ TC.assignE assign e'

desugarExp :: TC.TypedExpr -> GlDefn t (CC.UntypedExpr t 'Zero VarName)
desugarExp = desugarAnti DS.desugarExpr

coreTcExp :: CC.UntypedExpr t 'Zero VarName -> GlDefn t (CC.TypedExpr t 'Zero VarName)
coreTcExp = coreTcAnti IN.infer

monoExp :: CC.TypedExpr t 'Zero VarName -> GlMono t (CC.TypedExpr 'Zero 'Zero VarName)
monoExp = monoAnti MN.monoExpr

genExp :: CC.TypedExpr 'Zero 'Zero VarName -> Gl CS.Exp
genExp = genAnti $ \e -> do (v,vdecl,vstm,_) <- CG.genExpr Nothing e
                            let bis' = L.map CG.cBlockItem (vdecl ++ vstm)
                                v'   = CG.cExpr v
                            return $ CS.StmExpr (bis' ++ [CS.BlockStm (CS.Exp (Just v') noLoc)]) noLoc

transExp :: CS.Exp -> GlMono t CS.Exp
transExp (CS.AntiExp s loc) = (lift . lift) (parseExp s loc) >>= lift . flip tcExp Nothing >>=
                              lift . desugarExp >>= lift . coreTcExp >>= monoExp >>= lift . lift . lift . genExp
transExp e = return e

traverseExp = traverseAnti transExp

-- Function Id

transFuncId :: CS.Definition -> GlMono t CS.Definition
transFuncId (CS.FuncDef (CS.Func dcsp (CS.AntiId fn loc2) decl ps body loc1) loc0) =
  view (inst._2) >>= \idx -> do
    (fnName, _) <- lift . lift $ genFuncId fn loc2
    return $ CS.FuncDef (CS.Func dcsp (CS.Id (toCName $ MN.monoName fnName idx) loc2) decl ps body loc1) loc0
transFuncId d = return d

genFuncId :: String -> SrcLoc -> GlFile (FunName, [Maybe SF.LocType])
genFuncId fn loc = do
  surfaceFn <- parseFnCall fn loc
  case surfaceFn of
    SF.LocExpr _ (SF.TypeApp f ts _) -> return (f, ts)
    SF.LocExpr _ (SF.Var f)          -> return (f, [])
    _ -> throwError $ "Error: `" ++ fn ++ 
                      "' is not a valid function Id (with optional type arguments) in a $id antiquote"

-- Type Id

parseTypeId :: String -> SrcLoc -> GlFile (TypeName, [TyVarName])
parseTypeId s loc = parseAnti s ((,) <$> PS.typeConName <*> PP.many PS.variableName) loc 4

genTypeId :: CC.Type 'Zero -> Gl CG.CId
genTypeId = genAnti CG.typeCId

transTypeId :: CS.Definition -> GlMono t (CS.Definition, Maybe String)
transTypeId (CS.DecDef initgrp loc0)
  | CS.InitGroup dcsp attr0 init loc1 <- initgrp
  , CS.DeclSpec store tyqual tysp loc2 <- dcsp
  , CS.Tstruct mid fldgrp attr1 loc3 <- tysp
  , Just (CS.AntiId ty loc4) <- mid = do
    tn' <- (lift . lift) (parseType ty loc4) >>= lift . tcType  >>= lift . desugarType >>= monoType >>= lift . lift. lift . genTypeId
    let mid' = Just (CS.Id (toCName tn') loc4)
        tysp' = CS.Tstruct mid' fldgrp attr1 loc3
        dcsp' = CS.DeclSpec store tyqual tysp' loc2
        initgrp' = CS.InitGroup dcsp' attr0 init loc1
    return (CS.DecDef initgrp' loc0, Just tn')
transTypeId (CS.DecDef initgrp loc0)
  | CS.TypedefGroup dcsp attr0 [tydef] loc1 <- initgrp
  , CS.DeclSpec store tyqual tysp loc2 <- dcsp
  , CS.Tstruct mid fldgrp attr1 loc3 <- tysp
  , Just (CS.AntiId ty loc4) <- mid
  , CS.Typedef (CS.AntiId syn loc6) decl attr2 loc5 <- tydef = do
    tn'  <- (lift . lift) (parseType ty  loc4) >>= lift . tcType >>= lift . desugarType >>= monoType >>= lift . lift . lift . genTypeId
    syn' <- (lift . lift) (parseType syn loc6) >>= lift . tcType >>= lift . desugarType >>= monoType >>= lift . lift . lift . genTypeId
    when (tn' /= syn') $ throwError $ "Error: Type synonyms `" ++ syn ++ "' is somewhat different from the type `" ++ ty ++ "'"
    let tydef' = CS.Typedef (CS.Id (toCName syn') loc6) decl attr2 loc5
        mid' = Just (CS.Id (toCName tn') loc4)
        tysp' = CS.Tstruct mid' fldgrp attr1 loc3
        dcsp' = CS.DeclSpec store tyqual tysp' loc2
        initgrp' = CS.TypedefGroup dcsp' attr0 [tydef'] loc1
    return (CS.DecDef initgrp' loc0, Just tn')
transTypeId d = return (d, Nothing)

transTypeId' :: CS.TypeSpec -> GlMono t CS.TypeSpec
transTypeId' (CS.Tstruct mid fldgrp attr loc0)
  | Just (CS.AntiId ty loc1) <- mid = do
    tn' <- (lift . lift) (parseType ty loc1) >>= lift . tcType >>= lift . desugarType >>= monoType >>= lift . lift . lift . genTypeId
    return (CS.Tstruct (Just $ CS.Id (toCName tn') loc1) fldgrp attr loc0)
transTypeId' x = return x

traverseTypeId' :: CS.Definition -> GlMono t CS.Definition
traverseTypeId' (CS.DecDef initgrp loc) = CS.DecDef <$> traverseAnti transTypeId' initgrp <*> pure loc
traverseTypeId' d = return d


-- External definition

transEsc :: CS.Definition -> CS.Definition
transEsc (CS.AntiEsc s l) = CS.EscDef s l
transEsc d = d

transEscStm :: CS.Stm -> CS.Stm
transEscStm (CS.AntiEscStm s l) = CS.EscStm s l
transEscStm d = d

traverseEscStm :: CS.Definition -> GlMono t CS.Definition
traverseEscStm = traverseAnti $ return . transEscStm

-- Definition

traversals :: [(MN.Instance, Maybe Int)] -> CS.Definition -> GlDefn t [(CS.Definition, Maybe String)]
-- No type arguments, either monomorphic Cogent function, or not defined in Cogent
-- If any instances of a polymorphic function are not used anywhere, then no mono function will be generated
traversals insts d = forM insts $ \inst ->
                       flip runReaderT (MonoState inst) $
                         (traverseDecl >=> traverseDeclSpec >=> traverseType >=>
                         traverseFnCall >=> traverseDispatch >=> traverseExp >=>
                           -- NOTE: `traverseExp' has to be after `traverseFnCall' because they overlap / zilinc
                         return . transEsc >=> traverseEscStm >=>
                         transFuncId >=> transTypeId >=> firstM traverseTypeId') d

traverseOneFunc :: String -> CS.Definition -> SrcLoc -> GlFile [(CS.Definition, Maybe String)]
traverseOneFunc fn d loc = do
  -- First we need to __parse__ the function name, get the function name and the optional explicit type arguments.
  -- If the function has no explicit type arguments, then we treat it as a poly-definition;
  -- if it's applied to type arguments, then we consider it defined only for the applied types.
  -- At this point, we can't further compile this function id (treated as a function call FnCall as it
  -- can take type arguments), because any process beyond parsing requires us knowing what function it
  -- is (in a monad at least 'GlDefn'), but this is indeed what we are trying to work out. The loop-breaker
  -- is to manually extract the function name after parsing.
  (fnName, targs) <- genFuncId fn loc
  -- After getting the function name, we can construct a 'GlDefn' monad environment.
  lift $ cgState.localOracle .= 0
  monos <- lift $ use $ mnState.funMono  -- acquire all valid instantiations used in this unit.
  defs  <- lift $ use tcDefs
  case M.lookup fnName monos of
    -- This 'mono' should have entries for __all__ monomorphic (be it original monomorphic or monomorphised)
    -- functions that appear in this unit. If @Nothing@, then it means this function is not defined in Cogent
    -- or not used at all. The reason why we
    -- don't throw an exception is, IIRC, if the library implementation (or some large system) is
    -- arranged in such a way that a single @.ac@ file contains definitions for many @.cogent@
    -- files or definitions of unused Cogent functions. / zilinc (28/11/18)
    Nothing -> return []
    Just mp ->
      case L.find (SF.absFnDeclId fnName) defs of  -- function declared/defined in Cogent
        Nothing -> throwError $ "Error: Function `" ++ fn ++
                                "' is not an abstract Cogent function and thus cannot be antiquoted"
        Just tl -> do 
          let ts = tyVars tl
          -- Here we need to match the type argument given in the @.ac@ definition and the ones in the
          -- original Cogent definition, in order to decide which instantiations should be generated.
          case Vec.fromList ts of
            ExI (Flip ts') -> flip runReaderT (DefnState ts' [TC.InAntiquotedCDefn fn]) $ do
              -- NOTE: if there are type variables in the type application, the type vars must be in-scope,
              -- i.e. they must be the same ones as in the Cogent definition.

              -- NOTE: We now try to fill in missing type arguments, otherwise the typechecker might have
              -- difficulty in inferring the types. This is partially for backward compatibility reasons:
              -- For implicitly applied type arguments, if the typechecker cannot infer when you write
              -- the same in a Cogent program, it won't infer in a @.ac@ file either. Unlike before, 
              -- where we never typecheck them.
              
              -- If the type arguments are omitted, we add them back
              let targs' = L.zipWith
                             (\tv mta -> Just $ fromMaybe (SF.dummyLocT . SF.RT $ SF.TVar tv False) mta)
                             (L.map fst ts)
                             (targs ++ repeat Nothing)

              -- Then we can continue the normal compilation process.
              let SrcLoc (Loc (Pos filepath line col _) _) = loc
                  pos = newPos filepath line col
              CC.TE _ (CC.Fun _ coreTargs _) <- (flip tcExp (Nothing) >=>
                                                 desugarExp >=>
                                                 coreTcExp) $
                                                (SF.LocExpr pos (SF.TypeApp fnName targs' SF.NoInline))
              -- Matching @coreTargs@ with @ts@. More specifically: match them in @mp@, and trim
              -- those in @mp@ that don't match up @coreTargs@.
              -- E.g. if @ts = [U8,a]@ and in @mp@ we find @[U8,U32]@ and @[U8,Bool]@, we instantiate this
              --      function definition to these two types.
              --      if @ts = [U8,a]@ and @mp = ([Bool,U8],[U32,U8])@ then there's nothing we generate.
              let match :: [CC.Type t] -> [CC.Type 'Zero] -> Bool
                  match [] [] = True
                  match xs ys | L.null xs || L.null ys
                    = __impossible "match (in traverseOneFunc): number of type arguments don't match"
                  -- We for now ignore 'TVarBang's, and treat them as not matching anything.
                  match (x:xs) (y:ys) = (unsafeCoerce x == y || CC.isTVar x) && match xs ys
              let instantiations = if L.null ts then [([], Nothing)] 
                                   else L.filter (\(ms,_) -> match coreTargs ms)
                                        $ L.map (second Just) (M.toList mp)
              traversals instantiations d


traverseOneType :: String -> SrcLoc -> CS.Definition -> GlFile [(CS.Definition, Maybe String)]
traverseOneType ty l d = do   -- type defined in Cogent
  monos <- lift $ use $ mnState.typeMono
  defs  <- lift $ use tcDefs
  (tn,ts) <- parseTypeId ty l
  case M.lookup tn monos of  -- NOTE: It has to be an abstract type / zilinc
    Nothing -> return [] -- throwError $ "Error: Type `" ++ tn ++ "' is not defined / used in Cogent and thus cannot be antiquoted"
    Just s  -> do case L.find (SF.absTyDeclId tn) defs of
                    Nothing -> throwError $ "Error: Type `" ++ tn ++ "' is not an abstract Cogent type and thus cannot be antiquoted"
                    Just tl -> do let ts' = tyVars tl
                                  when (ts /= L.map fst ts') $
                                    throwError $ "Error: Type parameters in `" ++ ty ++ "' are different from those in Cogent"
                                  when (L.null ts') $
                                    throwError $ "Error: Non-parametric abstract Cogent type `" ++ tn ++ "' should not use antiquotation"
                                  case Vec.fromList ts' of
                                    ExI (Flip ts'') -> flip runReaderT (DefnState ts'' [TC.InAntiquotedCDefn ty]) $ do
                                      s' <- nubByName $ S.toList s
                                      traversals (L.zip s' (repeat Nothing)) d
 where
   nubByName :: [MN.Instance] -> GlDefn t [MN.Instance]
   nubByName ins = lift . lift $
     nubByM (\i1 i2 -> do tn1 <- mapM (genAnti CG.genType) i1
                          tn2 <- mapM (genAnti CG.genType) i2
                          return (tn1 == tn2)) ins

traverseOne :: CS.Definition -> GlFile [(CS.Definition, Maybe String)]
traverseOne d@(CS.FuncDef (CS.Func _ (CS.AntiId fn loc) _ _ _ _) _) = traverseOneFunc fn d loc
traverseOne d@(CS.DecDef initgrp  _)
  | CS.InitGroup dcsp _ _ _ <- initgrp
  , CS.DeclSpec _ _ tysp _ <- dcsp
  , CS.Tstruct mid _ _ _ <- tysp
  , Just (CS.AntiId ty l) <- mid = traverseOneType ty l d
  | CS.TypedefGroup dcsp _ _ _ <- initgrp
  , CS.DeclSpec _ _ tysp _ <- dcsp
  , CS.Tstruct mid _ _ _ <- tysp
  , Just (CS.AntiId ty l) <- mid = traverseOneType ty l d
traverseOne d = flip runReaderT (DefnState Nil [TC.InAntiquotedCDefn $ show d]) $ traversals [([], Nothing)] d  -- anything not defined in Cogent

-- | This function returns a list of pairs, of each the second component is the type name if
--   the first component is a type definition. We use the type name to generate a dedicated @.h@
--   file for that type. If the first is a function definition, then the second is always 'Nothing'.
traverseAll :: [CS.Definition] -> GlFile [(CS.Definition, Maybe String)]
traverseAll ds = concat <$> mapM traverseOne ds


-- Interface

data GlueMode = TypeMode | FuncMode deriving (Eq, Show)

glue :: GlState -> [TypeName] -> GlueMode -> [FilePath] -> ExceptT String IO [(FilePath, [CS.Definition])]
glue s typnames mode filenames = liftA (M.toList . M.fromListWith (flip (++)) . concat) .
  forM filenames $ \filename -> do
    ds <- parseFile defaultExts typnames filename
    ds' <- flip evalStateT s . flip runReaderT (FileState filename) $ traverseAll ds
    case mode of
      TypeMode -> forM ds' $ \(d, mbf) -> case mbf of
        Nothing -> throwE "Error: Cannot define functions in type mode"
        Just f  -> return (__cogent_abs_type_dir ++ "/abstract/" ++ f <.> __cogent_ext_of_h, [d])
      FuncMode -> let ext = if | takeExtension filename == __cogent_ext_of_ah -> __cogent_ext_of_h
                               | takeExtension filename == __cogent_ext_of_ac -> __cogent_ext_of_c
                               | otherwise -> __cogent_ext_of_c
                  in return [ (replaceExtension ((replaceBaseName filename (takeBaseName filename ++ __cogent_suffix_of_inferred))) ext
                            , L.map fst ds') ]

mkGlState :: [SF.TopLevel SF.RawType TC.TypedPatn TC.TypedExpr]
          -> TC.TcState
          -> Last (DS.Typedefs, DS.Constants, [CC.CoreConst CC.UntypedExpr])
          -> M.Map FunName CC.FunctionType
          -> (MN.FunMono, MN.TypeMono)
          -> CG.GenState
          -> GlState
mkGlState tced tcState (Last (Just (typedefs, constdefs, _))) ftypes (funMono, typeMono) genState =
  GlState { _tcDefs  = tced
          , _tcState = TcState { _tfuncs = view TC.knownFuns   tcState
                               , _ttypes = view TC.knownTypes  tcState
                               , _consts = view TC.knownConsts tcState
                               }
          , _dsState = DsState typedefs constdefs
          , _coreTcState = CoreTcState ftypes
          , _mnState = MnState funMono typeMono
          , _cgState = CgState { _cTypeDefs    = view CG.cTypeDefs    genState
                               , _cTypeDefMap  = view CG.cTypeDefMap  genState
                               , _typeSynonyms = view CG.typeSynonyms genState
                               , _typeCorres   = view CG.typeCorres   genState
                               , _absTypes     = view CG.absTypes     genState
                               , _custTypeGen  = view CG.custTypeGen  genState
                               , _funClasses   = view CG.funClasses   genState
                               , _localOracle  = view CG.localOracle  genState
                               , _globalOracle = view CG.globalOracle genState
                               }
          }
mkGlState _ _ _ _ _ _ = __impossible "mkGlState"


-- Misc.

tyVars :: SF.TopLevel SF.RawType pv e -> [(TyVarName, Kind)]
tyVars (SF.FunDef _ (SF.PT ts _) _) = ts
tyVars (SF.AbsDec _ (SF.PT ts _)  ) = ts
tyVars (SF.TypeDec    _ ts _) = L.zip ts $ repeat k2
tyVars (SF.AbsTypeDec _ ts _) = L.zip ts $ repeat k2
tyVars _ = __impossible "tyVars"


-- ////////////////////////////////////////////////////////////////////////////
--

collect :: GlState -> [TypeName] -> GlueMode -> [FilePath] -> ExceptT String IO (MN.FunMono, MN.TypeMono)
collect s typnames mode filenames = do
  ds <- liftA concat . forM filenames $ parseFile defaultExts typnames
  fmap (view (mnState.funMono) &&& view (mnState.typeMono)) (flip execStateT s $ collectAll ds)
      -- NOTE: Lens doesn't support Arrow. See http://www.reddit.com/r/haskell/comments/1nwetz/lenses_that_work_with_arrows/ / zilinc

collectAnti :: (Data a, Typeable b, Monoid r) => (b -> Gl r) -> a -> Gl r
collectAnti f a = everything (\a b -> mappend <$> a <*> b) (mkQ (pure mempty) f) a

collectFuncId :: CS.Definition -> Gl [(String, SrcLoc)]
-- collectFuncId (CS.FuncDef (CS.Func _ (CS.AntiId fn loc) _ _ bis _) _) = (fn, loc) : collectAnti collectFnCall bis
collectFuncId (CS.FuncDef (CS.Func _ (CS.Id _ _) _ _ bis _) _) = collectAnti collectFnCall bis  -- NOTE: we restrict entry points have to be C functions
collectFuncId d = return []

collectFnCall :: CS.Exp -> Gl [(String, SrcLoc)]
collectFnCall (CS.FnCall (CS.Var (CS.AntiId fn loc) _) args _) = return [(fn, loc)]
collectFnCall _ = return []

analyseFuncId :: [(String, SrcLoc)] -> GlDefn t [(FunName, MN.Instance)]
analyseFuncId ss = forM ss $ \(fn, loc) -> flip runReaderT (MonoState ([], Nothing)) $ do
  (CC.TE _ (CC.Fun fn' ts _)) <- monoExp =<< lift . coreTcExp =<< lift . desugarExp =<<
                                 lift . tcFnCall =<< (lift . lift) (parseFnCall fn loc)
  return (fn', ts)

collectOneFunc :: CS.Definition -> Gl ()
collectOneFunc d = do
  ss <- collectFuncId d
  fins <- flip runReaderT (FileState "") . flip runReaderT (DefnState Nil []) $ analyseFuncId ss
  forM_ fins $ \(fn, inst) -> do
    case inst of
      [] -> mnState.funMono %= (M.insert fn M.empty)
      ts -> mnState.funMono %= (M.insertWith (\_ m -> insertWith (flip const) ts (M.size m) m) fn (M.singleton ts 0))

collectOne :: CS.Definition -> Gl ()
collectOne d@(CS.FuncDef {}) = collectOneFunc d
collectOne _ = return ()

collectAll :: [CS.Definition] -> Gl ()
collectAll = mapM_ collectOne


-- /////////////////////////////////////////////////////////////////////////////
--
-- A simpler compilation process for the @--entry-funcs@ file.

readEntryFuncs :: [SF.TopLevel SF.RawType TC.TypedPatn TC.TypedExpr]
               -> TC.TcState
               -> Last (DS.Typedefs, DS.Constants, [CC.CoreConst CC.UntypedExpr])
               -> M.Map FunName CC.FunctionType
               -> [String]
               -> IO MN.FunMono
readEntryFuncs tced tcState dsState ftypes lns
  = foldM (\m ln -> readEntryFunc ln >>= \(fn,inst) -> return $ updateFunMono m fn inst) M.empty lns
  where
    updateFunMono m fn []   = M.insertWith (\_ entry -> entry) fn M.empty m
    updateFunMono m fn inst = M.insertWith (\_ entry -> M.insertWith (flip const) inst (M.size entry) entry) fn (M.singleton inst 0) m

    -- Each string is a line in the @--entry-funcs@ file.
    readEntryFunc :: String -> IO (FunName, MN.Instance)
    readEntryFunc ln = do
      er <- runExceptT $ flip evalStateT (mkGlState [] tcState dsState mempty (mempty, mempty) undefined) $
              flip runReaderT (FileState "--entry-funcs file") $ do
                (fnName, targs) <- genFuncId ln noLoc
                inst <- forM targs $ \mt ->
                          case mt of
                            Nothing -> throwError "No wildcard allowed."
                            Just t  -> flip runReaderT (DefnState Vec.Nil []) $
                                         flip runReaderT (MonoState ([], Nothing))
                                                         (lift . tcType >=> lift . desugarType >=> monoType $ t)
                return (fnName, inst)
      case er of Left s  -> putStrLn s >> return (ln, [])
                 Right r -> return r
