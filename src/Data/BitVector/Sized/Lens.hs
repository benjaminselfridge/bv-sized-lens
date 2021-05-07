{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module provides a convenient lens from a larger bitvector into a
-- smaller one:
--
-- >>> v = bvView @4 @'[3, 0, 1]
--
-- @v@ is the "view" into a @BV 4@ that you get by extracting the bits at
-- indices @3@, @0@, and @1@ (in order of most-significant to least-significant
-- bit). If
--
-- @
-- bv = 0bABCD
-- @
--
-- then the view @v@ defined above refers to the bits @0bADC@, a bitvector of
-- width 3. We can see this by creating a concrete bitvector, and using the view
-- to get and set bits:
--
-- >>> bv = BV.mkBV (knownNat @4) 0b1100
-- >>> printBV = putStrLn . BV.ppBin knownNat
-- >>> printBV $ bv ^. bvViewL v
-- 0b100:[3]
-- >>> printBV $ bv & bvViewL v .~ BV.mkBV knownNat 0b101
-- 0b1110:[4]
--
-- This is very useful for defining sub-fields of an instruction word. Consider
-- the encoding for the RISC-V instruction JAL:
--
-- @
-- [ imm[20] | imm[10:1] | imm[11] | imm[19:12] | rd[4:0] | opcode=1101111 ]
--          31          21        20           12         7                0
-- @
--
-- Notice how the 7-bit @opcode@ and 5-bit @rd@ are laid out consecutively in
-- the 32-bit instruction word, but the @imm@ field has its bits jumbled up
-- throughout the rest of the instruction. We can create a view of the three
-- fields like so:
--
-- >>> opcode = bvView @32 @(Slice 0 7)
-- >>> rd = bvView :: BVView 32 (Slice 7 5)
-- >>> imm = bvView :: BVView 32 ('[31] ++ Slice 12 8 ++ '[20] ++ Slice 21 10)
--
-- The @Slice@ and @++@ operators are useful for shortening the above
-- definitions. Expanded out, the types of the above definitions are:
--
-- >>> :t opcode
-- opcode :: BVView 32 '[6, 5, 4, 3, 2, 1, 0]
-- >>> :t rd
-- rd :: BVView 32 '[11, 10, 9, 8, 7]
-- >>> :t imm
-- imm
-- :: BVView
--      32
--      '[31, 19, 18, 17, 16, 15, 14, 13, 12, 20, 30, 29, 28, 27, 26, 25,
--        24, 23, 22, 21]
--
-- The type system prevents you from creating an invalid view (for instance,
-- where a bit index is repeated or out of range):
--
-- >>> v = bvView @32 @('[5] ++ Slice 3 4)
-- <interactive>:37:5: error:
--     • Invalid index list: '[5, 6, 5, 4, 3]
--       (repeated index 5)
--     • In the expression: bvView @32 @('[5] ++ Slice 3 4)
--       In an equation for ‘v’: v = bvView @32 @('[5] ++ Slice 3 4)
-- >>> v = bvView @32 @(Slice 30 4)
-- <interactive>:1:5: error:
--     • Invalid index 33 into BV 32
--       index must be strictly smaller than bitvector width
--     • In the expression: bvView @32 @(Slice 30 4)
--       In an equation for ‘v’: v = bvView @32 @(Slice 30 4)
-- <interactive>:1:5: error:
--     • Invalid index 32 into BV 32
--       index must be strictly smaller than bitvector width
--     • In the expression: bvView @32 @(Slice 30 4)
--       In an equation for ‘v’: v = bvView @32 @(Slice 30 4)
--
-- __WARNING__: Don't attempt to use this library unless all your type-level
-- indices are known at compile time. If you try abstracting over 'BVView',
-- you're gonna have a bad time.
module Data.BitVector.Sized.Lens
  ( -- * BVIx
    BVIx
  , bvIx
  , bvIxL
    -- * BVView
  , BVView
  , bvView
  , bvViewL
    -- * BVViews
  , BVViews
  , bvViews
  , bvViewsL
  -- * Type families on lists
  -- | Various type families that are useful for constructing types when using
  -- this library.
  , type (++)
  , type Slice
  , type Slice'
  , type Length
  , type Lengths
  -- * Lens validity constraints
  -- | These classes are used to ensure that the various lenses this library
  -- provides are well-formed.
  , ValidIx
  , ValidView
  , ValidViews
  ) where

import           Data.BitVector.Sized ( BV, pattern BV )
import qualified Data.BitVector.Sized as BV
import Data.Parameterized.Classes
import Data.Parameterized.List
import Data.Parameterized.NatRepr
import Data.Type.Bool
import Data.Type.Equality
import Control.Lens.Getter
import Control.Lens.Lens
import Control.Lens.Setter
import GHC.TypeLits
import Prelude hiding (concat)

type ValidIx' :: Nat -> Nat -> Bool
type family ValidIx' w ix where
  ValidIx' w ix = If (ix + 1 <=? w) 'True
    (TypeError
     (('Text "Invalid index " ':<>: 'ShowType ix ':<>:
       'Text " into BV " ':<>: 'ShowType w) ':$$:
      'Text "index must be strictly smaller than bitvector width"))

-- | Constrains @ix@ to be strictly less than @w@.
class ix + 1 <= w => ValidIx w ix
instance (ValidIx' w ix ~ 'True, ix + 1 <= w) => ValidIx w ix

catLens :: forall w wh wl .
           NatRepr wh
        -> NatRepr wl
        -> Lens' (BV w) (BV wh)
        -> Lens' (BV w) (BV wl)
        -> Lens' (BV w) (BV (wh + wl))
catLens wh wl hi lo = lens g s
  where g bv = BV.concat wh wl (bv ^. hi) (bv ^. lo)
        s :: BV w -> BV (wh + wl) -> BV w
        s bv bv'
          | LeqProof <- addPrefixIsLeq wh wl
          , Refl <- plusComm wh wl
          = let bvl :: BV wl
                bvl = BV.select (knownNat @0) wl bv'
                bvh :: BV wh
                bvh = BV.select wl wh bv'
            in bv & hi .~ bvh & lo .~ bvl

-- | Index of a single bit of a 'Data.BitVector.Sized.Internal.BV'.
data BVIx w ix where
  BVIx :: ValidIx w ix => NatRepr ix -> BVIx w ix

deriving instance Show (BVIx w ix)
instance ShowF (BVIx w)

instance TestEquality (BVIx w) where
  BVIx ix `testEquality` BVIx ix' = ix `testEquality` ix'

instance OrdF (BVIx w) where
  BVIx ix `compareF` BVIx ix' = ix `compareF` ix'

instance (KnownNat ix, ValidIx w ix) => KnownRepr (BVIx w) ix where
  knownRepr = BVIx knownNat

-- | Construct a 'BVIx' when the index is known at compile time.
--
-- >>> bvIx @32 @7
-- BVIx 7
-- >>> :type it
-- it :: BVIx 7
bvIx :: forall w ix . (KnownNat ix, ValidIx w ix) => BVIx w ix
bvIx = knownRepr

-- | Get a lens from a 'BVIx'.
bvIxL :: KnownNat w => BVIx w ix -> Lens' (BV w) (BV 1)
bvIxL (BVIx i) = bit knownNat i

-- | A lens into a single bit of a 'Data.BitVector.Sized.Internal.BV'.
bit :: ValidIx w ix => NatRepr w -> NatRepr ix -> Lens' (BV w) (BV 1)
bit w w' = lens (BV.select w' knownNat) s
  where s bv (BV 1) = BV.setBit w' bv
        s bv _      = BV.clearBit w w' bv

-- | Type-level list membership.
type family Elem (a :: k) (l :: [k]) :: Bool where
  Elem _ '[]    = 'False
  Elem a (k:ks) = a == k || Elem a ks

type family FindDuplicate (ks :: [k]) :: Maybe k where
  FindDuplicate '[] = 'Nothing
  FindDuplicate (k:ks) = If (Elem k ks) ('Just k) (FindDuplicate ks)

type family CheckFindDuplicateResult ixs mix where
  CheckFindDuplicateResult _ 'Nothing = 'True
  CheckFindDuplicateResult ixs ('Just ix) =
    TypeError ('Text "Invalid index list: " ':<>: 'ShowType ixs ':$$:
               'Text "(repeated index " ':<>: 'ShowType ix ':<>: 'Text ")")

type ValidView' ixs = CheckFindDuplicateResult ixs (FindDuplicate ixs)

-- | Constrains @ixs@ to have no repeated elements.
class ValidView' ixs ~ 'True => ValidView ixs
instance ValidView' ixs ~ 'True => ValidView ixs

-- | A list of 'BVIx' with no repeated elements. This essentially gives us a
-- reordering of some subset of the bits in a bitvector.
data BVView (w :: Nat) (ixs :: [Nat]) where
  BVView :: ValidView ixs => List (BVIx w) ixs -> BVView w ixs

listLength :: List f ixs -> NatRepr (Length ixs)
listLength Nil = knownNat
listLength (_ :< rst) = addNat (knownNat @1) (listLength rst)

deriving instance Show (BVView w pr)
instance ShowF (BVView w)

instance ( ValidView ixs
         , KnownRepr (List (BVIx w)) ixs
         ) => KnownRepr (BVView w) ixs where
  knownRepr = BVView knownRepr

-- | Construct a 'BVView' when the width and indices are known at compile time.
--
-- >>> bvView @32 @(Slice 9 3)
-- BVView (BVIx 11 :< BVIx 10 :< BVIx 9 :< Nil)
-- >>> :type it
-- it :: BVView 32 '[11, 10, 9]
-- >>> bvView @32 @'[5, 7, 5]
-- <interactive>:19:1: error:
--     • Invalid index list: '[5, 7, 5]
--       (repeated index 5)
--     • In the expression: bvView @32 @'[5, 7, 5]
--       In an equation for ‘it’: it = bvView @32 @'[5, 7, 5]
bvView :: forall w ixs . (KnownRepr (BVView w) ixs, ValidView ixs) => BVView w ixs
bvView = knownRepr

-- | Get a lens from a 'BVView'.
bvViewL :: forall w ixs . KnownNat w => BVView w ixs -> Lens' (BV w) (BV (Length ixs))
bvViewL (BVView l) = go l
  where go :: List (BVIx w) ixs' -> Lens' (BV w) (BV (Length ixs'))
        go = \case
          Nil -> lens (const (BV.zero knownNat)) const
          BVIx i :< rst ->
            catLens knownNat (listLength rst) (bit (knownNat @w) i) (go rst)

-- | Computes the intersection of two lists. The lists are assumed to already
-- have no duplicates. If the first argument does have duplicates that survive
-- the intersection operation, the result will have the same duplicates as well.
type Intersection :: [k] -> [k] -> [k]
type family Intersection ks ks' where
  Intersection '[] _ = '[]
  Intersection (k:ks) ks' =
    If (Elem k ks') (k ': Intersection ks ks') (Intersection ks ks')

-- | Two lists are disjoint.
type Disjoint :: [k] -> [k] -> Bool
type Disjoint ks ks' = Intersection ks ks' == '[]

type FindIntersecting' :: [k] -> [[k]] -> Maybe [k]
type family FindIntersecting' ks kss where
  FindIntersecting' _ '[] = 'Nothing
  FindIntersecting' ks (ks' ': kss') =
    If (Disjoint ks ks') (FindIntersecting' ks kss') ('Just ks')

type MergeFstMaybe :: k -> Maybe k -> Maybe (k, k)
type family MergeFstMaybe k mk where
  MergeFstMaybe _ 'Nothing = 'Nothing
  MergeFstMaybe k ('Just k') = 'Just '(k, k')

type (<>) :: Maybe k -> Maybe k -> Maybe k
type family mk <> mk' where
  'Nothing <> mk' = mk'
  'Just k <> _ = 'Just k

type FindIntersecting :: [[k]] -> Maybe ([k],[k])
type family FindIntersecting kss where
  FindIntersecting '[] = 'Nothing
  FindIntersecting (ks ': kss) =
    MergeFstMaybe ks (FindIntersecting' ks kss) <>
    FindIntersecting kss

type family CheckFindIntersectingResult kss m where
  CheckFindIntersectingResult _ 'Nothing = 'True
  CheckFindIntersectingResult kss ('Just '(ks, ks')) =
    TypeError (('Text "Invalid index lists " ':<>: 'ShowType kss) ':$$:
               ('Text "Lists " ':<>: 'ShowType ks ':<>:
                'Text " and " ':<>: 'ShowType ks' ':<>: 'Text " are not disjoint") ':$$:
               ('Text "(their intersection is " ':<>: 'ShowType (Intersection ks ks') ':<>:
                'Text ")"))

type ValidViews' kss = CheckFindIntersectingResult kss (FindIntersecting kss)

-- | Constraints @kss@ to ensure that all of the lists are disjoint.
class ValidViews' kss ~ 'True => ValidViews kss
instance (ValidViews' kss ~ 'True) => ValidViews kss

-- | A list of 'BVViews' where each 'BVView' is disjoint from the others. This
-- is basically a decomposition of a bitvector into disjoint fields.
data BVViews (w :: Nat) (ixss :: [[Nat]]) where
  BVViews :: ValidViews ixss => List (BVView w) ixss -> BVViews w ixss

deriving instance Show (BVViews w ixss)
instance ShowF (BVViews w)

instance ( ValidViews l
         , KnownRepr (List (BVView w)) l
         ) => KnownRepr (BVViews w) l where
  knownRepr = BVViews knownRepr

-- | Construct a 'BVViews' when the type is fully known at compile time.
--
-- >>> bvViews @32 @'[Slice 9 3, Slice' 14 2]
-- BVViews (BVView (BVIx 11 :< BVIx 10 :< BVIx 9 :< Nil) :< BVView (BVIx 14 :< BVIx 15 :< Nil) :< Nil)
-- >>> :type it
-- it :: BVViews 32 '[ '[11, 10, 9], '[14, 15]]
-- >>> bvViews @32 @'[Slice 0 3, Slice 2 2]
-- <interactive>:3:1: error:
--     • Invalid index lists '[ '[2, 1, 0], '[3, 2]]
--       Lists '[2, 1, 0] and '[3, 2] are not disjoint
--       (their intersection is '[2])
--     • In the expression: bvViews @32 @'[Slice 0 3, Slice 2 2]
--       In an equation for ‘it’: it = bvViews @32 @'[Slice 0 3, Slice 2 2]
bvViews :: forall w ixss . (KnownRepr (BVViews w) ixss, ValidViews ixss) => BVViews w ixss
bvViews = knownRepr

-- | 'Length' mapped over a list to produce a list of lengths.
type Lengths :: [[k]] -> [Nat]
type family Lengths (kss :: [[k]]) :: [Nat] where
  Lengths '[] = '[]
  Lengths (ks ': kss) = Length ks ': Lengths kss

-- | Get a lens from a 'BVViews'.
bvViewsL :: forall w ixss . KnownNat w
         => BVViews w ixss -> Lens' (BV w) (List BV (Lengths ixss))
bvViewsL (BVViews l) = lens (g l) (s l)
  where g :: List (BVView w) ixss' -> BV w -> List BV (Lengths ixss')
        g Nil _ = Nil
        g (v :< vs) bv = bv ^. bvViewL v :< g vs bv
        s :: List (BVView w) ixss' -> BV w -> List BV (Lengths ixss') -> BV w
        s Nil bv Nil = bv
        s (v :< vs) bv (bv' :< bvs') = s vs bv bvs' & bvViewL v .~ bv'

-- | Type-level list length.
type family Length (l :: [k]) :: Nat where
  Length '[] = 0
  Length (_:ks) = 1 + Length ks

-- | Type-level list append.
type family (++) (as :: [k]) (bs :: [k]) :: [k] where
  '[] ++ bs = bs
  (a ': as) ++ bs = a ': (as ++ bs)

-- | A "slice" of a bitvector. The first argument is the index of the least
-- significant bit of the slice, and the second argument is the width.
--
-- >>> :kind! Slice 7 4
-- Slice 7 4 :: [Nat]
-- = '[10, 9, 8, 7]
-- >>> v = bvView @8 @(Slice 4 2)
-- >>> printBV $ BV.mkBV knownNat 0b01101100 & bvViewL v .~ BV.mkBV knownNat 0b01
-- 0b1011100:[8]
type family Slice (i :: Nat) (w :: Nat) :: [Nat] where
  Slice i 0 = '[]
  Slice i w = i + w - 1 ': Slice i (w-1)

-- | A "reversed slice" of a bitvector. The first argument is the index of the
-- least significant bit of the slice, and the second argument is the width. The
-- resulting slice reverses the order of the bits.
--
-- >>> :kind! Slice' 7 4
-- Slice' 7 4 :: [Nat]
-- = '[7, 8, 9, 10]
-- >>> v = bvView @8 @(Slice' 4 2)
-- >>> printBV $ BV.mkBV knownNat 0b01101100 & bvViewL v .~ BV.mkBV knownNat 0b10
-- 0b1011100:[8]
type family Slice' (i :: Nat) (w :: Nat) :: [Nat] where
  Slice' i 0 = '[]
  Slice' i w = i ': Slice' (i+1) (w-1)
