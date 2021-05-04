{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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
-- >>> v = bvView :: BVView 4 '[3, 0, 1]
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
-- >>> opcode = bvView :: BVView 32 (Slice 0 7)
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
-- >>> v = bvView :: BVView 32 ('[5] ++ Slice 3 4)
-- <interactive>:1:5: error:
--     • Couldn't match type ‘'True’ with ‘'False’
--         arising from a use of ‘bvView’
--     • In the expression: bvView :: BVView 32 ('[5] ++ Slice 3 4)
--       In an equation for ‘v’: v = bvView :: BVView 32 ('[5] ++ Slice 3 4)
-- >>> v = bvView :: BVView 32 (Slice 30 4)
-- <interactive>:2:5: error:
--     • Couldn't match type ‘'False’ with ‘'True’
--         arising from a use of ‘bvView’
--     • In the expression: bvView :: BVView 32 (Slice 30 4)
--       In an equation for ‘v’: v = bvView :: BVView 32 (Slice 30 4)
--
-- This library is best used for applications where the types are fully known at
-- compile time. You don't want to write too many functions on these things, as
-- you'll have to figure out how to prove things like @Elem ix ixs ~ 'False@ a
-- lot.
module Data.BitVector.Sized.Lens
  ( -- * BVIx
    BVIx(..)
  , bvIx
  , bvIxL
    -- * BVView
  , BVView(..)
  , bvView
  , bvViewL
  , type Elem
  , type Length
  , type Slice
  , type Slice'
  , type (++)
    -- * BVViews
  , BVViews(..)
  , bvViews
  , bvViewsL
  , type Intersection
  , type Disjoint
  , type AllDisjoint
  , type Lengths
  ) where

import           Data.BitVector.Sized ( BV, pattern BV )
import qualified Data.BitVector.Sized as BV
import Data.Parameterized.Classes
import           Data.Parameterized.List (List)
import qualified Data.Parameterized.List as PL
import Data.Parameterized.NatRepr
import Data.Type.Bool
import Data.Type.Equality
import Control.Lens.Getter
import Control.Lens.Lens
import Control.Lens.Setter
import GHC.TypeNats
import Prelude hiding (concat)

-- | A lens into a single bit of a 'BV'.
bit :: (ix + 1 <= w) => NatRepr w -> NatRepr ix -> Lens' (BV w) (BV 1)
bit w w' = lens (BV.select w' knownNat) s
  where s bv (BV 1) = BV.setBit w' bv
        s bv _      = BV.clearBit w w' bv

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

-- | Index of a single bit of a 'BV'.
data BVIx w ix where
  BVIx :: ix + 1 <= w => NatRepr w -> NatRepr ix -> BVIx w ix

deriving instance Show (BVIx w ix)

instance TestEquality (BVIx w) where
  BVIx _ ix `testEquality` BVIx _ ix' = ix `testEquality` ix'

instance OrdF (BVIx w) where
  BVIx _ ix `compareF` BVIx _ ix' = ix `compareF` ix'

instance (KnownNat w, KnownNat ix, ix + 1 <= w) => KnownRepr (BVIx w) ix where
  knownRepr = BVIx knownNat knownNat

-- | Construct a 'BVIx' when the width and index are known at compile time.
--
-- >>> bvIx @32 @7
-- BVIx 32 7
-- >>> :type it
-- it :: BVIx 32 7
bvIx :: (KnownNat w, KnownNat ix, ix + 1 <= w) => BVIx w ix
bvIx = knownRepr

-- | Get a lens from a 'BVIx'.
bvIxL :: BVIx w ix -> Lens' (BV w) (BV 1)
bvIxL (BVIx w i) = bit w i

-- | Type-level list membership.
type family Elem (a :: k) (l :: [k]) :: Bool where
  Elem _ '[]    = 'False
  Elem a (k:ks) = a == k || Elem a ks

-- | Type-level list length.
type family Length (l :: [k]) :: Nat where
  Length '[] = 0
  Length (_:ks) = 1 + Length ks

-- | Type-level list append.
type family (++) (as :: [k]) (bs :: [k]) :: [k] where
  '[] ++ bs = bs
  (a ': as) ++ bs = a ': (as ++ bs)

-- | A "slice" of a bitvector. The first argument is the index, and the second
-- argument is the width.
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

-- | A "reversed slice" of a bitvector. The first argument is the index, and the
-- second argument is the width. The resulting slice reverses the order of the
-- bits.
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

-- | A list of 'BVIx' with no repeated elements. This essentially gives us a
-- reordering of some subset of the bits in a bitvector.
data BVView (w :: Nat) (ixs :: [Nat]) where
  Nil :: BVView w '[]
  (:-) :: Elem ix ixs ~ 'False
       => BVIx w ix
       -> BVView w ixs
       -> BVView w (ix ': ixs)

infixr 5 :-

bvViewLength :: BVView w ixs -> NatRepr (Length ixs)
bvViewLength Nil = knownNat
bvViewLength (_ :- rst) = addNat (knownNat @1) (bvViewLength rst)

instance KnownRepr (BVView w) '[] where
  knownRepr = Nil

instance ( ix + 1 <= w
         , Elem ix ixs ~ 'False
         , KnownRepr (BVView w) ixs
         , KnownNat w
         , KnownNat ix
         ) => KnownRepr (BVView w) (ix ': ixs) where
  knownRepr = knownRepr :- knownRepr

-- | Construct a 'BVView' when the width and indices are known at compile time.
--
-- >>> bvView @32 @(Slice 9 3)
-- BVIx 32 11 :- (BVIx 32 10 :- (BVIx 32 9 :- Nil))
-- >>> :type it
-- it :: BVView 32 '[11, 10, 9]
-- >>> bvView @32 @'[5, 7, 5]
-- <interactive>:12:1: error:
--     • Couldn't match type ‘'True’ with ‘'False’
--         arising from a use of ‘bvView’
--     • In the expression: bvView @32 @'[5, 7, 5]
--       In an equation for ‘it’: it = bvView @32 @'[5, 7, 5]

bvView :: KnownRepr (BVView w) ixs => BVView w ixs
bvView = knownRepr

deriving instance Show (BVView w pr)

-- | Get a lens from a 'BVView'.
bvViewL :: BVView w ixs -> Lens' (BV w) (BV (Length ixs))
bvViewL Nil = lens (const (BV.zero knownNat)) const
bvViewL (BVIx w i :- rst) =
  catLens knownNat (bvViewLength rst) (bit w i) (bvViewL rst)

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

-- | The first argument is disjoint from all the lists in the second argument.
type AllDisjoint :: [k] -> [[k]] -> Bool
type family AllDisjoint ks kss' where
  AllDisjoint _ '[] = 'True
  AllDisjoint ks (ks' ': kss') =
    Disjoint ks ks' && AllDisjoint ks kss'

-- | A list of 'BVViews' where each 'BVView' is disjoint from the others. This
-- is basically a decomposition of a bitvector into disjoint fields.
data BVViews (w :: Nat) (ixss :: [[Nat]]) where
  Nils :: BVViews w '[]
  (:+) :: AllDisjoint ixs ixss ~ 'True
       => BVView w ixs -> BVViews w ixss -> BVViews w (ixs ': ixss)

infixr 5 :+

deriving instance Show (BVViews w ixss)

instance KnownRepr (BVViews w) '[] where
  knownRepr = Nils

instance ( KnownRepr (BVView w) ixs
         , KnownRepr (BVViews w) ixss
         , AllDisjoint ixs ixss ~ 'True
         ) => KnownRepr (BVViews w) (ixs ': ixss) where
  knownRepr = knownRepr :+ knownRepr

-- | Construct a 'BVViews' when the type is fully known at compile time.
--
-- >>> bvViews @32 @'[Slice 9 3, Slice' 14 2]
-- (BVIx 32 11 :- (BVIx 32 10 :- (BVIx 32 9 :- Nil))) :+ ((BVIx 32 14 :- (BVIx 32 15 :- Nil)) :+ Nils)
-- >>> :type it
-- it :: BVViews 32 '[ '[11, 10, 9], '[14, 15]]
-- >>> bvViews @32 @'[Slice 0 3, Slice 2 2]
-- <interactive>:4:1: error:
--     • Couldn't match type ‘'False’ with ‘'True’
--         arising from a use of ‘bvViews’
--     • In the expression: bvViews @32 @'[Slice 0 3, Slice 2 2]
--       In an equation for ‘it’: it = bvViews @32 @'[Slice 0 3, Slice 2 2]
bvViews :: KnownRepr (BVViews w) ixss => BVViews w ixss
bvViews = knownRepr

-- | 'Length' mapped over a list to produce a list of lengths.
type Lengths :: [[k]] -> [Nat]
type family Lengths (kss :: [[k]]) :: [Nat] where
  Lengths '[] = '[]
  Lengths (ks ': kss) = Length ks ': Lengths kss

-- | Get a lens from a 'BVViews'.
bvViewsL :: BVViews w ixss -> Lens' (BV w) (List BV (Lengths ixss))
bvViewsL vs = lens (g vs) (s vs)
  where g :: BVViews w ixss' -> BV w -> List BV (Lengths ixss')
        g Nils _ = PL.Nil
        g (v :+ vs') bv = bv ^. bvViewL v PL.:< g vs' bv
        s :: BVViews w ixss' -> BV w -> List BV (Lengths ixss') -> BV w
        s Nils bv _ = bv
        s (v :+ vs') bv (bv' PL.:< bvs') =
          bv & bvViewsL vs' .~ bvs' & bvViewL v .~ bv'
