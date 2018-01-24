{-# LANGUAGE NamedFieldPuns #-}
--
-- Copyright 2017, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE FlexibleInstances, FlexibleContexts, LambdaCase, MultiWayIf, ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-missing-signatures #-}

module Cogent.PrettyPrint where
import qualified Cogent.Common.Syntax as S (associativity)
import Cogent.Common.Syntax hiding (associativity)
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Reorganizer (ReorganizeError(..), SourceObject(..))
import Cogent.Surface
-- import Cogent.TypeCheck --hiding (context)
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Subst

import Control.Arrow (second)
import qualified Data.Foldable as F
import Data.Function ((&))
import Data.IntMap as I (IntMap, toList, lookup)
import Data.List(nub)
import qualified Data.Map as M hiding (foldr)
#if __GLASGOW_HASKELL__ < 709
import Data.Monoid (mconcat)
import Prelude hiding (foldr)
#else
import Prelude hiding ((<$>), foldr)
#endif
import System.FilePath (takeFileName)
import Text.Parsec.Pos
import Text.PrettyPrint.ANSI.Leijen hiding (indent, tupled)


-- pretty-printing theme definition
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- meta-level constructs

position = string
err = red . string
errbd = bold . err
warn = dullyellow . string
comment = black . string
context = black . string

-- language ast

varname = string
letbangvar = dullgreen . string
primop = blue . string
keyword = bold . string
literal = dullcyan
typevar = blue . string
typename = blue . bold . string
typesymbol = cyan . string  -- type operators, e.g. !, ->, take
funname = green . string
funname' = underline . green . string
fieldname = magenta . string
tagname = dullmagenta . string
symbol = string
kindsig = red . string
typeargs x = encloseSep lbracket rbracket (comma <> space) x
record = encloseSep (lbrace <> space) (space <> rbrace) (comma <> space)
variant = encloseSep (langle <> space) rangle (symbol "|" <> space) . map (<> space)

-- combinators, helpers

indentation :: Int
indentation = 3

indent = nest indentation
indent' = (string (replicate indentation ' ') <>) . indent

-- FIXME: no spaces within parens where elements are on multiple lines / zilinc
tupled = __fixme . encloseSep lparen rparen (comma <> space)
-- non-unit tuples. put parens subject to arity
tupled1 [x] = x
tupled1 x = __fixme $ encloseSep lparen rparen (comma <> space) x

spaceList = encloseSep empty empty space
commaList = encloseSep empty empty (comma <> space)


-- associativity
-- ~~~~~~~~~~~~~~~~

level :: Associativity -> Int
level (LeftAssoc i) = i
level (RightAssoc i) = i
level (NoAssoc i) = i
level (Prefix) = 0

associativity :: String -> Associativity
associativity = S.associativity . symbolOp


-- type classes and instances for different constructs
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

class ExprType a where
  levelExpr :: a -> Int  -- associativity levels
  isVar :: a -> VarName -> Bool

instance ExprType (Expr t p ip e) where
  levelExpr (App {}) = 1
  levelExpr (PrimOp n _) = level (associativity n)
  levelExpr (Member {}) = 0
  levelExpr (Var {}) = 0
  levelExpr (IntLit {}) = 0
  levelExpr (BoolLit {}) = 0
  levelExpr (CharLit {}) = 0
  levelExpr (StringLit {}) = 0
  levelExpr (Tuple {}) = 0
  levelExpr (Unitel) = 0
  levelExpr (Con {}) = 1
  levelExpr (Annot {}) = 50
  levelExpr (UnboxedRecord {}) = 100
  levelExpr (Put {}) = 100
  levelExpr (TypeApp {}) = 100
  levelExpr (Upcast {}) = 100
  levelExpr (Seq {}) = 100
  levelExpr (Match {}) = 100
  levelExpr (If {}) = 100
  levelExpr (Let {}) = 100
  isVar (Var n) s = (n == s)
  isVar _ _ = False

instance ExprType RawExpr where
  levelExpr (RE e) = levelExpr e
  isVar (RE e) = isVar e

instance ExprType (TExpr t) where
  levelExpr (TE _ e _) = levelExpr e
  isVar (TE _ e _)     = isVar e

-- ------------------------------------

class PatnType a where
  isPVar :: a -> VarName -> Bool
  prettyIP :: a -> Doc
  prettyB :: (Pretty t, Pretty e, ExprType e) => (a, Maybe t, e) -> Bool -> Doc  -- binding

instance (PrettyName pv, PatnType ip, Pretty ip) => PatnType (IrrefutablePattern pv ip) where
  isPVar (PVar pv) = isName pv
  isPVar _ = const False

  prettyIP p@(PTake {}) = parens (pretty p)
  prettyIP p = pretty p

  prettyB (p, Just t, e) i
       = group (pretty p <+> symbol ":" <+> pretty t <+> symbol "=" <+> (if i then (pretty' 100) else pretty) e)
  prettyB (p, Nothing, e) i
       = group (pretty p <+> symbol "=" <+> (if i then (pretty' 100) else pretty) e)

instance PatnType RawIrrefPatn where
  isPVar   (RIP p) = isPVar p
  prettyIP (RIP p) = prettyIP p
  prettyB  (RIP p,mt,e) = prettyB (p,mt,e)

instance PatnType LocIrrefPatn where
  isPVar   (LocIrrefPatn _ p) = isPVar p
  prettyIP (LocIrrefPatn _ p) = prettyIP p
  prettyB  (LocIrrefPatn _ p,mt,e) = prettyB (p,mt,e)

instance (Pretty t) => PatnType (TIrrefPatn t) where
  isPVar   (TIP p _) = isPVar p
  prettyIP (TIP p _) = prettyIP p
  prettyB  (TIP p _,mt,e) = prettyB (p,mt,e)

-- ------------------------------------

class TypeType t where
  isCon :: t -> Bool
  isTakePut :: t -> Bool
  isFun :: t -> Bool
  isAtomic :: t -> Bool

instance TypeType (Type t) where
  isCon     (TCon {})  = True
  isCon     _          = False
  isFun     (TFun {})  = True
  isFun     _          = False
  isTakePut (TTake {}) = True
  isTakePut (TPut  {}) = True
  isTakePut _          = False
  isAtomic e | isFun e || isTakePut e = False
             | TCon _ (_:_) _ <- e = False
             | otherwise = True

instance TypeType RawType where
  isCon     (RT t) = isCon     t
  isTakePut (RT t) = isTakePut t
  isFun     (RT t) = isFun     t
  isAtomic  (RT t) = isAtomic  t

instance TypeType TCType where
  isCon     (T t) = isCon t
  isCon     _     = False
  isFun     (T t) = isFun t
  isFun     _     = False
  isTakePut (T t) = isTakePut t
  isTakePut _     = False
  isAtomic  (T t) = isAtomic t
  isAtomic  _     = False

-- ------------------------------------

class PrettyName a where
  prettyName :: a -> Doc
  isName :: a -> String -> Bool

instance PrettyName VarName where
  prettyName = varname
  isName s = (== s)

instance Pretty t => PrettyName (VarName, t) where
  prettyName (a, b) | __cogent_fshow_types_in_pretty = parens $ prettyName a <+> comment "::" <+> pretty b
                    | otherwise = prettyName a
  isName (a, b) x = a == x

-- ------------------------------------

-- class Pretty

instance Pretty Likelihood where
  pretty Likely   = symbol "=>"
  pretty Unlikely = symbol "~>"
  pretty Regular  = symbol "->"

instance (PrettyName pv, PatnType ip, Pretty ip) => Pretty (IrrefutablePattern pv ip) where
  pretty (PVar v) = prettyName v
  pretty (PTuple ps) = tupled (map pretty ps)
  pretty (PUnboxedRecord fs) = string "#" <> record (fmap handleTakeAssign fs)
  pretty (PUnderscore) = symbol "_"
  pretty (PUnitel) = string "()"
  pretty (PTake v fs) = prettyName v <+> record (fmap handleTakeAssign fs)

instance Pretty RawIrrefPatn where
  pretty (RIP ip) = pretty ip

instance Pretty LocIrrefPatn where
  pretty (LocIrrefPatn _ ip) = pretty ip

instance Pretty t => Pretty (TIrrefPatn t) where
  pretty (TIP ip _) = pretty ip

instance (PatnType ip, Pretty ip) => Pretty (Pattern ip) where
  pretty (PCon c [] )     = tagname c
  pretty (PCon c [p])     = tagname c <+> prettyIP p
  pretty (PCon c ps )     = tagname c <+> spaceList (map prettyIP ps)
  pretty (PIntLit i)      = literal (string $ show i)
  pretty (PBoolLit b)     = literal (string $ show b)
  pretty (PCharLit c)     = literal (string $ show c)
  pretty (PIrrefutable p) = pretty p

instance Pretty RawPatn where
  pretty (RP p) = pretty p

instance Pretty LocPatn where
  pretty (LocPatn _ p) = pretty p

instance Pretty t => Pretty (TPatn t) where
  pretty (TP p _) = pretty p

instance (Pretty t, PatnType ip, Pretty e, ExprType e) => Pretty (Binding t ip e) where
  pretty (Binding p t e []) = prettyB (p,t,e) False
  pretty (Binding p t e bs)
     = prettyB (p,t,e) True <+> hsep (map (letbangvar . ('!':)) bs)

instance (Pretty p, Pretty e) => Pretty (Alt p e) where
  pretty (Alt p arrow e) = symbol "|" <+> pretty p <+> group (pretty arrow <+> pretty e)

instance Pretty Inline where
  pretty Inline = keyword "inline" <+> empty
  pretty NoInline = empty

instance (ExprType e, Pretty t, Pretty p, PatnType ip, Pretty ip, Pretty e) => Pretty (Expr t p ip e) where
  pretty (Var x)             = varname x
  pretty (TypeApp x ts note) = pretty note <> varname x
                                 <> typeargs (map (\case Nothing -> symbol "_"; Just t -> pretty t) ts)
  pretty (Member x f)        = pretty' 1 x <> symbol "." <> fieldname f
  pretty (IntLit i)          = literal (string $ show i)
  pretty (BoolLit b)         = literal (string $ show b)
  pretty (CharLit c)         = literal (string $ show c)
  pretty (StringLit s)       = literal (string $ show s)
  pretty (Unitel)            = string "()"
  pretty (PrimOp n [a,b])
     | LeftAssoc  l <- associativity n = pretty' (l+1) a <+> primop n <+> pretty' l     b
     | RightAssoc l <- associativity n = pretty' l     a <+> primop n <+> pretty' (l+1) b
     | NoAssoc    l <- associativity n = pretty' l     a <+> primop n <+> pretty' l     b
  pretty (PrimOp n [e])      = primop n <+> pretty' 1 e
  pretty (PrimOp n es)       = primop n <+> tupled (map pretty es)
  -- pretty (Widen e)           = keyword "widen"  <+> pretty' 1 e
  pretty (Upcast e)          = keyword "upcast" <+> pretty' 1 e
  pretty (App a b)           = pretty' 2 a <+> pretty' 1 b
  pretty (Con n [] )         = tagname n
  pretty (Con n [e])         = tagname n <+> pretty' 1 e
  pretty (Con n es )         = tagname n <+> spaceList (map (pretty' 1) es)
  pretty (Tuple es)          = tupled (map pretty es)
  pretty (UnboxedRecord fs)  = string "#" <> record (map (handlePutAssign . Just) fs)
  pretty (If c vs t e)       = group (keyword "if" <+> handleBangedIf vs (pretty' 100 c)
                                                   <$> indent (keyword "then" </> pretty t)
                                                   <$> indent (keyword "else" </> pretty e))
    where handleBangedIf []  = id
          handleBangedIf vs  = (<+> hsep (map (letbangvar . ('!':)) vs))
  pretty (Match e bs alts)   = handleLetBangs bs (pretty' 100 e)
                               <> mconcat (map ((hardline <>) . indent . pretty) alts)
    where handleLetBangs []  = id
          handleLetBangs bs  = (<+> hsep (map (letbangvar . ('!':)) bs))
  pretty (Seq a b)           = pretty' 100 a <> symbol ";" <$> pretty b
  pretty (Let []     e)      = __impossible "pretty (in RawExpr)"
  pretty (Let (b:[]) e)      = keyword "let" <+> indent (pretty b)
                                             <$> keyword "in" <+> indent (pretty e)
  pretty (Let (b:bs) e)      = keyword "let" <+> indent (pretty b)
                                             <$> vsep (map ((keyword "and" <+>) . indent . pretty) bs)
                                             <$> keyword "in" <+> indent (pretty e)
  pretty (Put e fs)          = pretty' 1 e <+> record (map handlePutAssign fs)
  pretty (Annot e t)         = pretty' 50 e <+> symbol ":" <+> pretty t

instance Pretty RawExpr where
  pretty (RE e) = pretty e

instance Pretty t => Pretty (TExpr t) where
  pretty (TE t e _) | __cogent_fshow_types_in_pretty = parens $ pretty e <+> comment "::" <+> pretty t
                    | otherwise = pretty e

instance (Pretty t, TypeType t) => Pretty (Type t) where
  pretty (TCon n [] s) = ($ typename n) (if | s == ReadOnly -> (<> typesymbol "!")
                                            | s == Unboxed && (n `notElem` primTypeCons) -> (typesymbol "#" <>)
                                            | otherwise     -> id)
  pretty (TCon n as s) = (if | s == ReadOnly -> (<> typesymbol "!") . parens
                             | s == Unboxed  -> (typesymbol "#" <>)
                             | otherwise     -> id) $
                         typename n <+> hsep (map prettyT' as)
    where prettyT' e | not $ isAtomic e = parens (pretty e)
                     | otherwise        = pretty e
  pretty (TVar n b)  = typevar n <> (if b then typesymbol "!" else empty)
  pretty (TTuple ts) = tupled (map pretty ts)
  pretty (TUnit)     = typesymbol "()" & (if __cogent_fdisambiguate_pp then (<+> comment "{- unit -}") else id)
  pretty (TRecord ts s)
    | not . or $ map (snd . snd) ts = (if | s == Unboxed -> (typesymbol "#" <>)
                                          | s == ReadOnly -> (\x -> parens x <> typesymbol "!")
                                          | otherwise -> id) $
        record (map (\(a,(b,c)) -> fieldname a <+> symbol ":" <+> pretty b) ts)  -- all untaken
    | otherwise = pretty (TRecord (map (second . second $ const False) ts) s)
              <+> typesymbol "take" <+> tupled1 (map fieldname tk)
        where tk = map fst $ filter (snd . snd) ts
  pretty (TVariant ts) | any snd ts = let
     names = map fst $ filter (snd . snd) $ M.toList ts
   in pretty (TVariant $ fmap (second (const False)) ts) <+> typesymbol "take"
                                                         <+> tupled1 (map fieldname names)
  pretty (TVariant ts) = variant (map (\(a,bs) -> case bs of
                                          [] -> tagname a
                                          _  -> tagname a <+> spaceList (map prettyT' bs)) $ M.toList (fmap fst ts))
    where prettyT' e | not $ isAtomic e = parens (pretty e)
                     | otherwise        = pretty e
  pretty (TFun t t') = prettyT' t <+> typesymbol "->" <+> pretty t'
    where prettyT' e | isFun e   = parens (pretty e)
                     | otherwise = pretty e
  pretty (TUnbox t) = (typesymbol "#" <> prettyT' t) & (if __cogent_fdisambiguate_pp then (<+> comment "{- unbox -}") else id)
    where prettyT' e | not $ isAtomic e = parens (pretty e)
                     | otherwise        = pretty e
  pretty (TBang t) = (prettyT' t <> typesymbol "!") & (if __cogent_fdisambiguate_pp then (<+> comment "{- bang -}") else id)
    where prettyT' e | not $ isAtomic e = parens (pretty e)
                     | otherwise        = pretty e
  pretty (TTake fs x) = (prettyT' x <+> typesymbol "take"
                                    <+> case fs of Nothing  -> tupled (fieldname ".." : [])
                                                   Just fs' -> tupled1 (map fieldname fs'))
                        & (if __cogent_fdisambiguate_pp then (<+> comment "{- take -}") else id)
    where prettyT' e | not $ isAtomic e = parens (pretty e)
                     | otherwise        = pretty e
  pretty (TPut fs x) = (prettyT' x <+> typesymbol "put"
                                   <+> case fs of Nothing -> tupled (fieldname ".." : [])
                                                  Just fs' -> tupled1 (map fieldname fs'))
                       & (if __cogent_fdisambiguate_pp then (<+> comment "{- put -}") else id)
    where prettyT' e | not $ isAtomic e = parens (pretty e)
                     | otherwise        = pretty e

instance Pretty RawType where
  pretty (RT t) = pretty t

instance Pretty TCType where
  pretty (T t) = pretty t
  pretty (U v) = warn ("?" ++ show v)
--  pretty (RemoveCase a b) = pretty a <+> string "(without pattern" <+> pretty b <+> string ")"

instance Pretty LocType where
  pretty t = pretty (stripLocT t)

renderPolytypeHeader vs = keyword "all" <> tupled (map prettyKS vs) <> symbol "." 
    where prettyKS (v,K False False False) = typevar v
          prettyKS (v,k) = typevar v <+> symbol ":<" <+> pretty k

instance Pretty t => Pretty (Polytype t) where
  pretty (PT [] t) = pretty t
  pretty (PT vs t) = renderPolytypeHeader vs <+> pretty t

renderTypeDecHeader n vs = keyword "type" <+> typename n <> hcat (map ((space <>) . typevar) vs)
                                          <+> symbol "=" 

prettyFunDef :: (Pretty p, Pretty e, Pretty t) => Bool -> FunName -> Polytype t -> [Alt p e] -> Doc
prettyFunDef typeSigs v pt [Alt p Regular e] = (if typeSigs then (funname v <+> symbol ":" <+> pretty pt <$>) else id)
                                                 (funname v <+> pretty p <+> group (indent (symbol "=" <$> pretty e)))
prettyFunDef typeSigs v pt alts = (if typeSigs then (funname v <+> symbol ":" <+> pretty pt <$>) else id) $
                                       (indent (funname v <> mconcat (map ((hardline <>) . indent . pretty) alts)))

prettyConstDef typeSigs v t e  = (if typeSigs then (funname v <+> symbol ":" <+> pretty t <$>) else id) $
                                         (funname v <+> group (indent (symbol "=" <+> pretty e)))

instance (Pretty t, Pretty p, Pretty e) => Pretty (TopLevel t p e) where
  pretty (TypeDec n vs t) = keyword "type" <+> typename n <> hcat (map ((space <>) . typevar) vs)
                                           <+> indent (symbol "=" </> pretty t)
  pretty (FunDef v pt alts) = prettyFunDef True v pt alts
  pretty (AbsDec v pt) = funname v <+> symbol ":" <+> pretty pt
  pretty (Include s) = keyword "include" <+> literal (string $ show s)
  pretty (IncludeStd s) = keyword "include <" <+> literal (string $ show s)
  pretty (AbsTypeDec n vs) = keyword "type" <+> typename n  <> hcat (map ((space <>) . typevar) vs)
  pretty (ConstDef v t e) = prettyConstDef True v t e
  pretty (DocBlock _) = __fixme empty  -- FIXME: doesn't PP docs right now

instance Pretty Kind where
  pretty k = kindsig (stringFor k)
    where stringFor k = (if canDiscard k then "D" else "")
                     ++ (if canShare   k then "S" else "")
                     ++ (if canEscape  k then "E" else "")

instance Pretty SourcePos where
  pretty p | __cogent_ffull_src_path = position (show p)
           | otherwise = position $ show $ setSourceName p (takeFileName $ sourceName p)

instance Pretty Metadata where
  pretty (Constant {varName})                = err "the binding" <+> funname varName <$> err "is a global constant"
  pretty (Reused {varName, boundAt, usedAt}) = err "the variable" <+> varname varName
                                               <+> err "bound at" <+> pretty boundAt <> err ""
                                               <$> err "was already used at"
                                               <$> indent' (vsep $ map pretty $ F.toList usedAt)
  pretty (Unused {varName, boundAt}) = err "the variable" <+> varname varName
                                       <+> err "bound at" <+> pretty boundAt <> err ""
                                       <$> err "was never used."
  pretty (UnusedInOtherBranch {varName, boundAt, usedAt}) =
    err "the variable" <+> varname varName
    <+> err "bound at" <+> pretty boundAt <> err ""
    <$> err "was used in another branch of control at"
    <$> indent' (vsep $ map pretty $ F.toList usedAt)
    <$> err "but not this one."
  pretty (UnusedInThisBranch {varName, boundAt, usedAt}) =
    err "the variable" <+> varname varName
    <+> err "bound at" <+> pretty boundAt <> err ""
    <$> err "was used in this branch of control at"
    <$> indent' (vsep $ map pretty $ F.toList usedAt)
    <$> err "but not in all other branches."
  pretty Suppressed = err "a binder for a value of this type is being suppressed."
  pretty (UsedInMember {fieldName}) = err "the field" <+> fieldname fieldName
                                       <+> err "is being extracted without taking the field in a pattern."
  pretty UsedInLetBang = err "it is being returned from such a context."
  pretty (TypeParam {functionName, typeVarName }) = err "it is required by the type of" <+> funname functionName
                                                      <+> err "(type variable" <+> typevar typeVarName <+> err ")"
  pretty ImplicitlyTaken = err "it is implicitly taken via subtyping."

instance Pretty FuncOrVar where
  pretty MustFunc  = err "Function"
  pretty MustVar   = err "Variable"
  pretty FuncOrVar = err "Variable or function"

instance Pretty TypeError where
  pretty (DifferingNumberOfConArgs f n m) = err "Constructor" <+> tagname f 
                                        <+> err "invoked with differing number of arguments (" <> int n <> err " vs " <> int m <> err ")"
  pretty (DuplicateTypeVariable vs)      = err "Duplicate type variable(s)" <+> commaList (map typevar vs)
  pretty (DuplicateRecordFields fs)      = err "Duplicate record field(s)" <+> commaList (map fieldname fs)
  pretty (FunctionNotFound fn)           = err "Function" <+> funname fn <+> err "not found"
  pretty (TooManyTypeArguments fn pt)    = err "Too many type arguments to function"
                                           <+> funname fn  <+> err "of type" <+> pretty pt
  pretty (NotInScope fov vn)             = pretty fov <+> varname vn <+> err "not in scope"
  pretty (UnknownTypeVariable vn)        = err "Unknown type variable" <+> typevar vn
  pretty (UnknownTypeConstructor tn)     = err "Unknown type constructor" <+> typename tn
  pretty (TypeArgumentMismatch tn i1 i2) = typename tn <+> err "expects"
                                           <+> int i1 <+> err "arguments, but has been given" <+> int i2
  pretty (TypeMismatch t1 t2)            = err "Mismatch between" <$> indent' (pretty t1)
                                           <$> err "and" <$> indent' (pretty t2)
  pretty (RequiredTakenField f t)        = err "Field" <+> fieldname f <+> err "of type" <+> pretty t
                                           <+> err "is required, but has been taken"
  pretty (TypeNotShareable t m)          = err "Cannot share type" <+> pretty t
                                           <$> err "but this is needed as" <+> pretty m
  pretty (TypeNotEscapable t m)          = err "Cannot let type" <+> pretty t <+> err "escape from a !-ed context,"
  pretty (TypeNotDiscardable t m)        = err "Cannot discard type" <+> pretty t
                                           <+> err "but this is needed as" <+> pretty m
  pretty (PatternsNotExhaustive t tags)  = err "Patterns not exhaustive for type" <+> pretty t
                                           <$> err "cases not matched" <+> tupled1 (map tagname tags)
  pretty (UnsolvedConstraint c os)       = analyseLeftover c os
  pretty (RecordWildcardsNotSupported)   = err "Record wildcards are not supported"
  pretty (NotAFunctionType t)            = err "Type" <+> pretty t <+> err "is not a function type"
  pretty (DuplicateVariableInPattern vn) = err "Duplicate variable" <+> varname vn <+> err "in pattern"
  -- pretty (DuplicateVariableInPattern vn pat)       = err "Duplicate variable" <+> varname vn <+> err "in pattern:"
  --                                                    <$> pretty pat
  -- pretty (DuplicateVariableInIrrefPattern vn ipat) = err "Duplicate variable" <+> varname vn <+> err "in (irrefutable) pattern:"
  --                                                    <$> pretty ipat
  pretty (TakeFromNonRecordOrVariant fs t) = err "Cannot" <+> keyword "take" <+> err "fields"
                                             <+> (case fs of Nothing  -> tupled (fieldname ".." : [])
                                                             Just fs' -> tupled1 (map fieldname fs'))
                                             <+> err "from non record/variant type:"
                                             <$> indent' (pretty t)
  pretty (PutToNonRecordOrVariant fs t)    = err "Cannot" <+> keyword "put" <+> err "fields"
                                             <+> (case fs of Nothing  -> tupled (fieldname ".." : [])
                                                             Just fs' -> tupled1 (map fieldname fs'))
                                             <+> err "into non record/variant type:"
                                             <$> indent' (pretty t)
  pretty (TakeNonExistingField f t)      = err "Cannot" <+> keyword "take" <+> err "non-existing field"
                                           <+> fieldname f <+> err "from record/variant" <$> indent' (pretty t)
  pretty (PutNonExistingField f t)       = err "Cannot" <+> keyword "put" <+> err "non-existing field"
                                           <+> fieldname f <+> err "into record/variant" <$> indent' (pretty t)
  pretty (DiscardWithoutMatch t)         = err "Variant tag"<+> tagname t <+> err "cannot be discarded without matching on it."
  pretty (RequiredTakenTag t)            = err "Required variant" <+> tagname t <+> err "but it has already been matched."
  pretty (TypeWarningAsError w)          = pretty w

instance Pretty TypeWarning where
  pretty (UnusedLocalBind v) = warn "[--Wunused-local-binds]" <$$> indent' (warn "Defined but not used:" <+> pretty v)
  pretty (TakeTakenField f t) = warn "[--Wdodgy-take-put]" <$$> indent' (warn "Take a taken field" <+> fieldname f
                                  <+> warn "from type" <$> pretty t)
  pretty (PutUntakenField f t) = warn "[--Wdodgy-take-put]" <$$> indent' (warn "Put an untaken field" <+> fieldname f
                                  <+> warn "into type" <$> pretty t)

instance Pretty TypeEW where
  pretty = either ((err "Error:" <+>) . pretty) ((warn "Warning:" <+>) . pretty)

instance Pretty VarOrigin where
  pretty (ExpressionAt l) = warn ("the term at location " ++ show l)
  pretty (BoundOf a b d) = warn ("taking the " ++ show d ++ " of") <$> pretty a <$> warn "and" <$> pretty b

analyseLeftover :: Constraint -> I.IntMap VarOrigin -> Doc
analyseLeftover c@(F t :< F u) os
    | Just t' <- flexOf t
    , Just u' <- flexOf u
    = vcat $ err "A subtyping constraint" <+>  pretty c <+> err "can't be solved because both sides are unknown."
           : map (\i -> warn "• The unknown" <+> pretty (U i) <+> warn "originates from" <+> pretty (I.lookup i os))
                 (nub [t',u'])
    | Just t' <- flexOf t
    = vcat $ (case t of
        U _ -> err "Constraint" <+> pretty c <+> err "can't be solved as another constraint blocks it."
        _   -> err "A subtyping constraint" <+>  pretty c
           <+> err "can't be solved because the LHS is unknown and uses non-injective operators (like !).")
             : map (\i -> warn "• The unknown" <+> pretty (U i) <+> warn "originates from" <+> pretty (I.lookup i os)) ([t'])
    | Just u' <- flexOf u
    = vcat $ (case u of
        U _ -> err "Constraint" <+> pretty c <+> err "can't be solved as another constraint blocks it."
        _   -> err "A subtyping constraint" <+>  pretty c
           <+> err "can't be solved because the RHS is unknown and uses non-injective operators (like !).")
             : map (\i -> warn "• The unknown" <+> pretty (U i) <+> warn "originates from" <+> pretty (I.lookup i os)) ([u'])
analyseLeftover c os = case c of
    Share x m  | Just x' <- flexOf x -> msg x' m
    Drop x m   | Just x' <- flexOf x -> msg x' m
    Escape x m | Just x' <- flexOf x -> msg x' m
    _ -> err "Leftover constraint!" <$> pretty c
  where msg i m = err "Constraint" <+> pretty c <+> err "can't be solved as it constrains an unknown."
                <$$> indent' (vcat [ warn "• The unknown" <+> pretty (U i) <+> warn "originates from" <+> pretty (I.lookup i os)
                                   , err "The constraint was emitted as" <+> pretty m])

instance (Pretty a, TypeType a) => Pretty (TypeFragment a) where
  pretty (F t) = pretty t & (if __cogent_fdisambiguate_pp then (<+> comment "{- F -}") else id)
  pretty (FVariant ts) = typesymbol "?" <> pretty (TVariant ts)
  pretty (FRecord ts)
    | not . or $ map (snd . snd) ts = typesymbol "?" <>
        record (map (\(a,(b,c)) -> fieldname a <+> symbol ":" <+> pretty b) ts)  -- all untaken
    | otherwise = pretty (FRecord (map (second . second $ const False) ts))
              <+> typesymbol "take" <+> tupled1 (map fieldname tk)
        where tk = map fst $ filter (snd .snd) ts

instance Pretty Constraint where
  pretty (a :< b)         = pretty a </> warn ":<" </> pretty b
  pretty (a :& b)         = pretty a </> warn ":&" </> pretty b
  pretty (Upcastable a b) = pretty a </> warn "~>" </> pretty b
  pretty (Share  t m)     = warn "Share" <+> pretty t
  pretty (Drop   t m)     = warn "Drop" <+> pretty t
  pretty (Escape t m)     = warn "Escape" <+> pretty t
  pretty (Unsat e)        = err  "Unsat"
  pretty (SemiSat w)      = warn "SemiSat"
  pretty (Sat)            = warn "Sat"
  pretty (Exhaustive t p) = warn "Exhaustive" <+> pretty t <+> pretty p
  pretty (x :@ _)         = pretty x

-- a more verbose version of constraint pretty-printer which is mostly used for debugging
prettyC :: Constraint -> Doc
prettyC (Unsat e) = errbd "Unsat" <$> pretty e
prettyC (SemiSat w) = warn "SemiSat" -- <$> pretty w
prettyC (a :& b) = prettyC a </> warn ":&" <$> prettyC b
prettyC (c :@ e) = prettyC c & (if __cogent_ddump_tc_ctx then (</> prettyCtx e False) else (</> warn ":@ ..."))
prettyC c = pretty c

instance Pretty SourceObject where
  pretty (TypeName n) = typename n
  pretty (ValName  n) = varname n
  pretty (DocBlock' _) = __fixme empty  -- FIXME: not implemented

instance Pretty ReorganizeError where
  pretty CyclicDependency = err "cyclic dependency"
  pretty DuplicateTypeDefinition = err "duplicate type definition"
  pretty DuplicateValueDefinition = err "duplicate value definition"

instance Pretty Subst where
  pretty (Subst m) = pretty m

instance Pretty a => Pretty (I.IntMap a) where
  pretty = vcat . map (\(k,v) -> pretty k <+> text "|->" <+> pretty v) . I.toList

-- helper functions
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~

-- ctx -> indent -> doc
prettyCtx :: ErrorContext -> Bool -> Doc
prettyCtx (SolvingConstraint c) _ = context "from constraint" <+> indent (pretty c)
prettyCtx (ThenBranch) _ = context "in the" <+> keyword "then" <+> context "branch"
prettyCtx (ElseBranch) _ = context "in the" <+> keyword "else" <+> context "branch"
prettyCtx (InExpression e t) True = context "when checking that the expression at ("
                                      <> pretty (posOfE e) <> context ")"
                                      <$> (indent' (pretty (stripLocE e)))
                                      <$> context "has type" <$> (indent' (pretty t))
prettyCtx (InExpression e t) False = context "when checking the expression at ("
                                       <> pretty (posOfE e) <> context ")"
-- FIXME: more specific info for patterns
prettyCtx (InPattern p) True = context "when checking the pattern at ("
                                 <> pretty (posOfP p) <> context ")"
                                 <$> (indent' (pretty (stripLocP p)))
prettyCtx (InPattern p) False = context "when checking the pattern at ("
                                  <> pretty (posOfP p) <> context ")"
prettyCtx (InIrrefutablePattern ip) True = context "when checking the pattern at ("
                                             <> pretty (posOfIP ip) <> context ")"
                                             <$> (indent' (pretty (stripLocIP ip)))
prettyCtx (InIrrefutablePattern ip) False = context "when checking the pattern at ("
                                              <> pretty (posOfIP ip) <> context ")"
prettyCtx (NthAlternative n p) _ = context "in the" <+> nth n <+> context "alternative" <+> pretty p
  where  nth 1 = context "1st"
         nth 2 = context "2nd"
         nth 3 = context "3rd"
         nth n = context (show n ++ "th")
prettyCtx (InDefinition p tl) _ = context "in the definition at (" <> pretty p <> context ")"
                               <$> context "for the" <+> helper tl
  where helper (TypeDec n _ _) = context "type synonym" <+> typename n
        helper (AbsTypeDec n _) = context "abstract type" <+> typename n
        helper (AbsDec n _) = context "abstract function" <+> varname n
        helper (ConstDef v _ _) = context "constant" <+> varname v
        helper (FunDef v _ _) = context "function" <+> varname v
        helper _  = __impossible "helper"
prettyCtx (AntiquotedType t) i = (if i then (<$> indent' (pretty (stripLocT t))) else id)
                               (context "in the antiquoted type at (" <> pretty (posOfT t) <> context ")" )
prettyCtx (AntiquotedExpr e) i = (if i then (<$> indent' (pretty (stripLocE e))) else id)
                               (context "in the antiquoted expression at (" <> pretty (posOfE e) <> context ")" )


-- add parens and indents to expressions depending on level
pretty' :: (Pretty a, ExprType a) => Int -> a -> Doc
pretty' l x | levelExpr x < l = pretty x
            | otherwise       = parens (indent (pretty x))

handleTakeAssign :: (PatnType ip, Pretty ip) => Maybe (FieldName, ip) -> Doc
handleTakeAssign Nothing = fieldname ".."
handleTakeAssign (Just (s, e)) | isPVar e s = fieldname s
handleTakeAssign (Just (s, e)) = fieldname s <+> symbol "=" <+> pretty e

handlePutAssign :: (ExprType e, Pretty e) => Maybe (FieldName, e) -> Doc
handlePutAssign Nothing = fieldname ".."
handlePutAssign (Just (s, e)) | isVar e s = fieldname s
handlePutAssign (Just (s, e)) = fieldname s <+> symbol "=" <+> pretty e


-- top-level function
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~

-- typechecker errors/warnings
prettyTWE :: Int -> ContextualisedEW -> Doc
prettyTWE th (ectx, we) = pretty we <$> indent' (vcat (map (flip prettyCtx True ) (take th ectx)
                                                    ++ map (flip prettyCtx False) (drop th ectx)))

-- reorganiser errors
prettyRE :: (ReorganizeError, [(SourceObject, SourcePos)]) -> Doc
prettyRE (msg,ps) = pretty msg <$>
                    indent' (vcat (map (\(so,p) -> context "-" <+> pretty so
                                               <+> context "(" <> pretty p <> context ")") ps))

prettyPrint :: Pretty a => (Doc -> Doc) -> [a] -> SimpleDoc
prettyPrint f = renderSmart 1.0 120 . f . vcat . map pretty


