{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
module Cogent.DataLayout.TypeCheck where

import Data.Map (Map)
import qualified Data.Map as M

import Control.Monad (guard, foldM)

import Cogent.Common.Syntax (FieldName, TagName, DataLayoutName, Size)
import Cogent.Common.Types (Sigil)
import Cogent.DataLayout.Core
import Cogent.DataLayout.Surface
import Cogent.DataLayout.Desugar (desugarSize)
import Cogent.Compiler (__fixme)

import Text.Parsec.Pos (SourcePos)

{- IMPORTANT EXPORTED FUNCTIONS -}
typeCheckDataLayoutExpr
  :: NamedDataLayouts
  -> DataLayoutExpr
  -> ([DataLayoutTypeCheckError], Allocation)

typeCheckDataLayoutExpr env (RepRef n) =
  case M.lookup n env of 
    Just (_, allocation) -> mapPaths (InDecl n) $ return allocation
    Nothing              -> returnError $ UnknownDataLayout n PathEnd
        
typeCheckDataLayoutExpr _ (Prim size) =
  if bitSize == 0
    then return []
    else return [(bitRange, PathEnd)]
  where
    bitSize = desugarSize size
    bitRange = BitRange bitSize 0
  
typeCheckDataLayoutExpr env (Offset dataLayoutExpr offsetSize) =
  offset (evalSize offsetSize) <$> typeCheckDataLayoutExpr env dataLayoutExpr
    
typeCheckDataLayoutExpr env (Record fields) = foldM typeCheckField [] fields
  where
    typeCheckField
      :: Allocation -- The accumulated allocation from previous alternatives
      -> (FieldName, SourcePos, DataLayoutExpr)
      -> ([DataLayoutTypeCheckError], Allocation)
        
    typeCheckField accumAlloc (fieldName, pos, dataLayoutExpr) = do
      fieldsAlloc <- mapPaths (InField fieldName pos) (typeCheckDataLayoutExpr env dataLayoutExpr)
      accumAlloc /\ fieldsAlloc
          
typeCheckDataLayoutExpr env (Variant tagExpr alternatives) = do
  case primitiveBitRange tagExpr of
    Just tagBits  -> do altsAlloc <- fst <$> foldM (typeCheckAlternative tagBits) ([], M.empty) alternatives
                        [(tagBits, InTag PathEnd)] /\ altsAlloc
    Nothing       -> returnError $ TagNotSingleBlock (InTag PathEnd)
  where
    typeCheckAlternative
      :: BitRange -- Of the variant's tag
      -> (Allocation, Map Size TagName)  -- The accumulated (allocation, set of used tag values) from already evaluated alternatives
      -> (TagName, SourcePos, Size, DataLayoutExpr) -- The alternative to evaluate
      -> ([DataLayoutTypeCheckError], (Allocation, Map Size TagName))
      
    typeCheckAlternative range (accumAlloc, accumTagValues) (tagName, pos, tagValue, dataLayoutExpr) = do
      alloc     <- (accumAlloc ++) <$> mapPaths (InAlt tagName pos) (typeCheckDataLayoutExpr env dataLayoutExpr)
      tagValues <- checkedTagValues
      return $ (alloc, tagValues) 
      where
        checkedTagValues :: ([DataLayoutTypeCheckError], Map Size TagName)
        checkedTagValues
          | tagValue < 0 || tagValue >= 2^(bitSizeBR range) =
              returnError $ OversizedTagValue (InAlt tagName pos PathEnd) range tagName tagValue
          | Just conflictingTagName <- tagValue `M.lookup` accumTagValues =
              returnError $ SameTagValues (InAlt tagName pos PathEnd) conflictingTagName tagName tagValue
          | otherwise =
              return $ M.insert tagValue tagName accumTagValues

    primitiveBitRange :: DataLayoutExpr -> Maybe BitRange
    primitiveBitRange (Prim size)        = Just $ BitRange (desugarSize size) 0
    primitiveBitRange (Offset expr size) = offset (desugarSize size) <$> primitiveBitRange expr
    primitiveBitRange _                  = Nothing

-- Normalises the layout remove references to named layouts
normaliseDataLayoutExpr
  :: NamedDataLayouts
  -> DataLayoutExpr
  -> DataLayoutExpr
normaliseDataLayoutExpr _ expr = __fixme expr

{- IMPORTANT TYPES -}
type NamedDataLayouts = Map DataLayoutName (DataLayoutExpr, Allocation)
type DataLayoutTypeCheckError = DataLayoutTypeCheckErrorP DataLayoutPath

-- The type parameter p is the type of the path to the error (DataLayoutPath)
-- We parameterise by p so we can use the functor instance to map changes to the path
data DataLayoutTypeCheckErrorP p
  = OverlappingBlocks       (BitRange, p) (BitRange, p)
    -- Have declared two overlapping bit ranges which shouldn't overlap
    
  | UnknownDataLayout       DataLayoutName p
    -- Have referenced a data layout which hasn't been declared
    -- The path is the path to the use of that Rep in the RepExpr being checked
    
  | TagNotSingleBlock       p
  
  | SameTagValues           p TagName TagName Size
    -- Path to two tags in the same variant and their common value
    
  | OversizedTagValue       p BitRange TagName Size
    -- Used a tag value which is too large to fit in the variant's tag bit range
    -- Path to the variant, bits for its bit range, name of the alternative, it's tag value
    
  deriving (Eq, Show, Ord, Functor)

-- Allows errors messages to pinpoint the exact location where the error occurred in a DataLayoutExpr/Decl
data DataLayoutPath
  = InField FieldName SourcePos DataLayoutPath
  | InTag   DataLayoutPath
  | InAlt   TagName SourcePos DataLayoutPath
  | InDecl  DataLayoutName DataLayoutPath
  | PathEnd
  deriving (Eq, Show, Ord)




{- OTHER EXPORTED FUNCTIONS -}
typeCheckDataLayoutDecl
  :: NamedDataLayouts
  -> DataLayoutDecl
  -> ([DataLayoutTypeCheckError], Allocation)

typeCheckDataLayoutDecl _ _ = __fixme ([], [])

normaliseDataLayoutDecl
  :: NamedDataLayouts
  -> DataLayoutDecl
  -> DataLayoutDecl

normaliseDataLayoutDecl _ decl = __fixme decl

-- Normalises the layout in the sigil to remove references to named layouts
normaliseSigil
  :: NamedDataLayouts
  -> Sigil (Maybe DataLayoutExpr)
  -> Sigil (Maybe DataLayoutExpr)

normaliseSigil _ sigil = __fixme sigil

returnError :: Monoid a => DataLayoutTypeCheckError -> ([DataLayoutTypeCheckError], a)
returnError e = ([e], mempty)


{- OTHER FUNCTIONS -}
evalSize :: RepSize -> Size
evalSize (Bytes b) = b * 8
evalSize (Bits b)  = b
evalSize (Add a b) = evalSize a + evalSize b


{- ALLOCATIONS -}

-- A set of bit indices into a data type.
--
-- Represents the set which is the union of the sets represented by the `BitRange`s in the list.
type Allocation = [(BitRange, DataLayoutPath)]

-- Conjunction of allocations
--
-- Used when the two allocations could be used simultaneously, and so they must not overlap.
-- For example, if they are allocations for two fields of the same record.
-- An OverlappingBlocks DataLayoutTypeCheckError is returned if the two allocations overlap.
(/\) :: Allocation -> Allocation -> ([DataLayoutTypeCheckError], Allocation)
a1 /\ a2 =
  case allOverlappingBlocks a1 a2 of
    overlappingBlocks@(_ : _) -> (overlappingBlocks, [])
    []                          -> return (a1 ++ a2)
  where
    allOverlappingBlocks :: Allocation -> Allocation -> [DataLayoutTypeCheckError]
    allOverlappingBlocks a b = do
      pair1@(block1, _) <- a
      pair2@(block2, _) <- b
      guard $ overlaps block1 block2
      return $ OverlappingBlocks pair1 pair2
     
overlaps :: BitRange -> BitRange -> Bool
overlaps (BitRange s1 o1) (BitRange s2 o2) =
  s1 > 0 &&
  s2 > 0 &&
  ((o1 >= o2 && o1 < (o2 + s2)) || 
   (o2 >= o1 && o2 < (o1 + s1)))

mapOntoPaths
  :: (DataLayoutPath -> DataLayoutPath)
  -> Allocation
  -> Allocation
mapOntoPaths = fmap . fmap

mapPaths
  :: (DataLayoutPath -> DataLayoutPath)
  -> ([DataLayoutTypeCheckError], Allocation)
  -> ([DataLayoutTypeCheckError], Allocation)
mapPaths f (errors, alloc) = (fmap (fmap f) errors, mapOntoPaths f alloc)

-- When transforming (Offset repExpr offsetSize),
-- we want to add offset bits to all blocks inside the repExpr,
-- as well as the allocation corresponding to that repExpr.
class Offsettable a where
  offset :: Size -> a -> a
  
instance Offsettable BitRange where
  offset n range@(BitRange { bitOffsetBR }) = range { bitOffsetBR = bitOffsetBR + n}
  
instance Offsettable a => Offsettable (DataLayout a) where
  offset n = fmap (offset n)
  
instance Offsettable Allocation where
  offset n = fmap $ \(range, path) -> (offset n range, path)





