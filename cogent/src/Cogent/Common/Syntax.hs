-- @LICENSE(NICTA_CORE)

{-# LANGUAGE CPP #-}

module Cogent.Common.Syntax where

import Cogent.Compiler

#if __GLASGOW_HASKELL__ < 709
import Data.Monoid
#endif
import Data.Word
import Text.PrettyPrint.ANSI.Leijen

type RepName     = String
type FieldName   = String
type TagName     = String
type FunName     = String
type VarName     = String
type TyVarName   = String
type TypeName    = String

type FieldIndex = Int
type ArrayIndex = Word32
type ArraySize  = Word32

type Size = Integer -- Not sure why quickcheck tests infinite loop if Size = Word32.

type OpName = String

data Op
  = Plus | Minus | Times | Divide | Mod
  | Not | And | Or
  | Gt | Lt | Le | Ge | Eq | NEq
  | BitAnd | BitOr | BitXor | LShift | RShift | Complement
  deriving (Eq, Ord, Show)

data Pragma = InlinePragma FunName
            | CInlinePragma FunName
            | FnMacroPragma FunName
            | UnrecPragma String
            deriving (Eq, Show)

data Associativity = LeftAssoc Int
                   | RightAssoc Int
                   | NoAssoc Int
                   | Prefix
                   deriving Eq

associativity :: Op -> Associativity
associativity x | x `elem` [Times, Divide, Mod] = LeftAssoc 11
                | x `elem` [Plus, Minus] = LeftAssoc 12
                | x `elem` [Gt, Lt, Le, Ge, Eq, NEq] = NoAssoc 13
                | x `elem` [BitAnd] = LeftAssoc 14
                | x `elem` [BitXor] = LeftAssoc 15
                | x `elem` [BitOr]  = LeftAssoc 16
                | x `elem` [LShift, RShift] = LeftAssoc 17
                | x `elem` [And] = RightAssoc 18
                | x `elem` [Or]  = RightAssoc 19
                | otherwise = Prefix

symbolOp :: OpName -> Op
symbolOp "+"   = Plus
symbolOp "-"   = Minus
symbolOp "*"   = Times
symbolOp "/"   = Divide
symbolOp "%"   = Mod
symbolOp "not" = Not
symbolOp "&&"  = And
symbolOp "||"  = Or
symbolOp ">="  = Ge
symbolOp "<="  = Le
symbolOp "<"   = Lt
symbolOp ">"   = Gt
symbolOp "=="  = Eq
symbolOp "/="  = NEq
symbolOp ".&." = BitAnd
symbolOp ".|." = BitOr
symbolOp ".^." = BitXor
symbolOp ">>"  = RShift
symbolOp "<<"  = LShift
symbolOp "complement" = Complement
symbolOp x     = __impossible "symbolOp"

opSymbol :: Op -> String
opSymbol Plus  = "+"
opSymbol Minus = "-"
opSymbol Times = "*"
opSymbol Divide = "/"
opSymbol Mod = "%"
opSymbol Not = "not"
opSymbol And = "&&"
opSymbol Or = "||"
opSymbol Gt = ">"
opSymbol Lt = "<"
opSymbol Le = "<="
opSymbol Ge = ">="
opSymbol Eq = "=="
opSymbol NEq = "/="
opSymbol BitAnd = ".&."
opSymbol BitOr = ".|."
opSymbol BitXor = ".^."
opSymbol LShift = "<<"
opSymbol RShift = ">>"
opSymbol Complement = "complement"

instance Pretty Op where
  pretty = string . opSymbol

data Likelihood = Unlikely | Regular | Likely deriving (Show, Eq, Ord)

#if __GLASGOW_HASKELL__ < 803
instance Monoid Likelihood where
  mempty = Regular
  mappend Unlikely Likely   = Regular
  mappend Unlikely _        = Unlikely
  mappend Likely   Unlikely = Regular
  mappend Likely   _        = Likely
  mappend Regular  l        = l
#else 
instance Semigroup Likelihood where
  (<>) Unlikely Likely   = Regular
  (<>) Unlikely _        = Unlikely
  (<>) Likely   Unlikely = Regular
  (<>) Likely   _        = Likely
  (<>) Regular  l        = l
instance Monoid Likelihood where
  mempty = Regular
#endif

tagSuccess = "Success" :: TagName
tagFail    = "Fail"    :: TagName


-- ----------------------------------------------------------------------------
-- custTyGen

data CustTyGenInfo = CTGI  deriving (Show) -- TODO: info like field mapping, etc.

-- ex1 :: M.Map (Type 'Zero) (String, CustTypeGenInfo)
-- ex1 = M.singleton (TRecord [("f1", (TCon "A" [] Unboxed, False)), 
--                             ("f2", (TCon "B" [] Unboxed, False)),
--                             ("f3", (TCon "C" [] Writable, False))] Writable) ("T_c_t", CTGI)


