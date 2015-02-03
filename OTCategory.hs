{-# LANGUAGE KindSignatures, DataKinds, GADTs, StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, TypeOperators #-}
 
module OTCategory where

import Test.QuickCheck
import Control.Applicative ((<$>), (<*>))
 
data DocCtx = Tombstone DocCtx | Char DocCtx | Empty

-- Singletons
data SDocCtx :: DocCtx -> * where
  STombstone :: SDocCtx ctx -> SDocCtx ('Tombstone ctx)
  SChar :: SDocCtx ctx -> SDocCtx ('Char ctx)
  SEmpty :: SDocCtx 'Empty

class SingletonDocCtx ctx where
  sing :: SDocCtx ctx

instance SingletonDocCtx Empty where
  sing = SEmpty

instance SingletonDocCtx ctx => SingletonDocCtx (Tombstone ctx) where
  sing = STombstone sing

instance SingletonDocCtx ctx => SingletonDocCtx ('Char ctx) where
  sing = SChar sing
 
data Op :: DocCtx -> DocCtx -> * where
  Noop :: Op 'Empty Empty
  InsertChar :: Char -> Op a b -> Op a ('Char b)
  RetainChar :: Op a b -> Op ('Char a) ('Char b)
  DeleteChar :: Op a b -> Op ('Char a) ('Tombstone b)
  InsertTombstone :: Op a b -> Op a ('Tombstone b)
  RetainTombstone :: Op a b -> Op ('Tombstone a) ('Tombstone b)

identity' :: SDocCtx ctx -> Op ctx ctx
identity' SEmpty = Noop
identity' (STombstone s) = RetainTombstone (identity' s)
identity' (SChar s) = RetainChar (identity' s)

identity :: SingletonDocCtx ctx => Op ctx ctx
identity = identity' sing

deriving instance Show (Op a b)
deriving instance Eq (Op a b)

compose :: Op a b -> Op b c -> Op a c
compose a (InsertTombstone b) = InsertTombstone (compose a b)
compose a (InsertChar c b) = InsertChar c (compose a b)
compose (InsertChar c a) (DeleteChar b) = InsertTombstone (compose a b)
compose (InsertChar c a) (RetainChar b) = InsertChar c (compose a b)
compose (InsertTombstone a) (RetainTombstone b) = InsertTombstone (compose a b)
compose (RetainChar a) (RetainChar b) = RetainChar (compose a b)
compose (RetainChar a) (DeleteChar b) = DeleteChar (compose a b)
compose (DeleteChar a) (RetainTombstone b) = DeleteChar (compose a b)
compose (RetainTombstone a) (RetainTombstone b) = RetainTombstone (compose a b)
compose Noop Noop = Noop

data Diamond :: DocCtx -> DocCtx -> * where
  Diamond :: Op c d -> Op b d -> Diamond b c

deriving instance Show (Diamond b c)

instance Eq (Diamond b c) where
  a == b = show a == show b

transform :: Op a b -> Op a c -> Diamond b c
transform (InsertChar c x) y = case transform x y of
  Diamond x' y' -> Diamond (InsertChar c x') (RetainChar y')
transform (InsertTombstone x) y = case transform x y of
  Diamond x' y' -> Diamond (InsertTombstone x') (RetainTombstone y')
transform x (InsertChar c y) = case transform x y of
  Diamond x' y' -> Diamond (RetainChar x') (InsertChar c y')
transform x (InsertTombstone y) = case transform x y of
  Diamond x' y' -> Diamond (RetainTombstone x') (InsertTombstone y')
transform (RetainChar x) (RetainChar y) = case transform x y of
  Diamond x' y' -> Diamond (RetainChar x') (RetainChar y')
transform (RetainTombstone x) (RetainTombstone y) = case transform x y of
  Diamond x' y' -> Diamond (RetainTombstone x') (RetainTombstone y')
transform (RetainChar x) (DeleteChar y) = case transform x y of
  Diamond x' y' -> Diamond (RetainTombstone x') (DeleteChar y')
transform (DeleteChar x) (RetainChar y) = case transform x y of
  Diamond x' y' -> Diamond (DeleteChar x') (RetainTombstone y')
transform (DeleteChar x) (DeleteChar y) = case transform x y of
  Diamond x' y' -> Diamond (RetainTombstone x') (RetainTombstone y')
transform Noop Noop = Diamond Noop Noop

-- Half-unityped operation a.k.a. object in the slice category Op/a
data HUTOp :: DocCtx -> * where
  HUTOp :: SingletonDocCtx b => Op a b -> HUTOp a

hutNoop :: HUTOp Empty
hutNoop = HUTOp Noop

hutInsertChar :: Char -> HUTOp a -> HUTOp a
hutInsertChar c (HUTOp op) = HUTOp (InsertChar c op)

hutRetainChar :: HUTOp a -> HUTOp ('Char a)
hutRetainChar (HUTOp op) = HUTOp (RetainChar op)

hutDeleteChar :: HUTOp a -> HUTOp ('Char a)
hutDeleteChar (HUTOp op) = HUTOp (DeleteChar op)

hutInsertTombstone :: HUTOp a -> HUTOp a
hutInsertTombstone (HUTOp op) = HUTOp (InsertTombstone op)

hutRetainTombstone :: HUTOp a -> HUTOp (Tombstone a)
hutRetainTombstone (HUTOp op) = HUTOp (RetainTombstone op)

hutArbitrary :: SDocCtx ctx -> Gen (HUTOp ctx)
hutArbitrary SEmpty =
  oneof
  [ return hutNoop
  , hutInsertChar <$> arbitrary <*> hutArbitrary SEmpty
  , hutInsertTombstone <$> hutArbitrary SEmpty
  ]
hutArbitrary (STombstone s) =
  oneof
  [ hutRetainTombstone <$> hutArbitrary s
  , hutInsertChar <$> arbitrary <*> hutArbitrary (STombstone s)
  , hutInsertTombstone <$> hutArbitrary (STombstone s)
  ]
hutArbitrary (SChar s) =
  oneof
  [ hutRetainChar <$> hutArbitrary s
  , hutDeleteChar <$> hutArbitrary s
  , hutInsertChar <$> arbitrary <*> hutArbitrary (SChar s)
  , hutInsertTombstone <$> hutArbitrary (SChar s)
  ]

instance SingletonDocCtx ctx => Arbitrary (HUTOp ctx) where
  arbitrary = hutArbitrary sing

-- Unityped operation
data UTOp :: * where
  UTOp :: (SingletonDocCtx a, SingletonDocCtx b) => Op a b -> UTOp

deriving instance Show UTOp

utNoop :: UTOp
utNoop = UTOp Noop

utInsertChar :: Char -> UTOp -> UTOp
utInsertChar c (UTOp op) = UTOp (InsertChar c op)

utRetainChar :: UTOp -> UTOp
utRetainChar (UTOp op) = UTOp (RetainChar op)

utDeleteChar :: UTOp -> UTOp
utDeleteChar (UTOp op) = UTOp (DeleteChar op)

utInsertTombstone :: UTOp -> UTOp
utInsertTombstone (UTOp op) = UTOp (InsertTombstone op)

utRetainTombstone :: UTOp -> UTOp
utRetainTombstone (UTOp op) = UTOp (RetainTombstone op)

instance Arbitrary UTOp where
  arbitrary =
    oneof
    [ return utNoop
    , utRetainChar <$> arbitrary
    , utInsertChar <$> arbitrary <*> arbitrary
    , utDeleteChar <$> arbitrary
    , utInsertTombstone <$> arbitrary
    , utRetainTombstone <$> arbitrary
    ]

data Nat = Z | S Nat

data SNat :: Nat -> * where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

class SingletonNat n where
  singNat :: SNat n

instance SingletonNat 'Z where
  singNat = SZ

instance SingletonNat n => SingletonNat ('S n) where
  singNat = SS singNat

data OpSeq :: DocCtx -> Nat -> * where
  OSNil :: SingletonDocCtx a => OpSeq a 'Z
  OSCons :: SingletonDocCtx a => Op a b -> OpSeq b n -> OpSeq a ('S n)

deriving instance Show (OpSeq a n)

instance Eq (OpSeq a n) where
  a == b = show a == show b

opSeqArbitrary :: SingletonDocCtx a => SNat n -> Gen (OpSeq a n)
opSeqArbitrary SZ = return OSNil
opSeqArbitrary (SS n) = do
  HUTOp op <- arbitrary
  OSCons op <$> opSeqArbitrary n

instance (SingletonDocCtx a, SingletonNat n) => Arbitrary (OpSeq a n) where
  arbitrary = opSeqArbitrary singNat

data SNatList :: [Nat] -> * where
  SNil :: SNatList '[]
  SCons :: SNat n -> SNatList ns -> SNatList (n ': ns)

class SingletonNatList ns where
  singNatList :: SNatList ns

instance SingletonNatList '[] where
  singNatList = SNil

instance (SingletonNat n, SingletonNatList ns) => SingletonNatList (n ': ns) where
  singNatList = SCons singNat singNatList

data OpFan :: DocCtx -> [Nat] -> * where
  OFNil :: OpFan a '[]
  OFCons :: OpSeq a n -> OpFan a ns -> OpFan a (n ': ns)

deriving instance Show (OpFan a ns)

instance Eq (OpFan a ns) where
  a == b = show a == show b

opFanArbitrary :: SingletonDocCtx a => SNatList ns -> Gen (OpFan a ns)
opFanArbitrary SNil = return OFNil
opFanArbitrary (SCons n ns) = OFCons <$> opSeqArbitrary n <*> opFanArbitrary ns

instance (SingletonNatList ns, SingletonDocCtx a) => Arbitrary (OpFan a ns) where
  arbitrary = opFanArbitrary singNatList

-- Unityped OpFan
data UTOpFan :: [Nat] -> * where
  UTOpFan :: OpFan a ns -> UTOpFan ns

deriving instance Show (UTOpFan ns)

instance Eq (UTOpFan ns) where
  a == b = show a == show b

instance SingletonNatList ns => Arbitrary (UTOpFan ns) where
  arbitrary = do
    UTOp (op :: Op a b) <- arbitrary
    UTOpFan <$> (arbitrary :: Gen (OpFan a ns))

prop_composeAssociative :: UTOpFan '[S (S (S Z))] -> Bool
prop_composeAssociative (UTOpFan (OFCons (OSCons x (OSCons y (OSCons z _))) _)) =
  compose x (compose y z) == compose (compose x y) z

prop_composeIdentityLeft :: UTOp -> Bool
prop_composeIdentityLeft (UTOp op) = compose identity op == op

prop_composeIdentityRight :: UTOp -> Bool
prop_composeIdentityRight (UTOp op) = compose op identity == op

identityDiamondLeft :: SingletonDocCtx c => Op a c -> Diamond a c
identityDiamondLeft op = Diamond identity op

prop_transformIdentityLeft :: UTOp -> Bool
prop_transformIdentityLeft (UTOp op) = transform identity op == identityDiamondLeft op

identityDiamondRight :: SingletonDocCtx b => Op a b -> Diamond b a
identityDiamondRight op = Diamond op identity

prop_transformIdentityRight :: UTOp -> Bool
prop_transformIdentityRight (UTOp op) = transform op identity == identityDiamondRight op

prop_transformCommutative :: UTOpFan [S Z, S Z] -> Bool
prop_transformCommutative (UTOpFan (OFCons (OSCons x _) (OFCons (OSCons y _) _))) =
  case transform x y of
    Diamond x' y' -> compose x y' == compose y x'

composeThenTransformRight :: Op a b -> Op a c1 -> Op c1 c2 -> Diamond b c2
composeThenTransformRight x y1 y2 = transform x (compose y1 y2)

transformThenComposeRight :: Op a b -> Op a c1 -> Op c1 c2 -> Diamond b c2
transformThenComposeRight x y1 y2 =
  case transform x y1 of
    Diamond x' y1' -> case transform x' y2 of
      Diamond x'' y2' -> Diamond x'' (compose y1' y2')

prop_transformComposeCommutativeRight :: UTOpFan [S Z, S (S Z)] -> Bool
prop_transformComposeCommutativeRight (UTOpFan (OFCons (OSCons x _) (OFCons (OSCons y1 (OSCons y2 _)) _))) =
  composeThenTransformRight x y1 y2 == transformThenComposeRight x y1 y2

composeThenTransformLeft :: Op a b1 -> Op b1 b2 -> Op a c -> Diamond b2 c
composeThenTransformLeft x1 x2 y = transform (compose x1 x2) y

transformThenComposeLeft :: Op a b1 -> Op b1 b2 -> Op a c -> Diamond b2 c
transformThenComposeLeft x1 x2 y =
  case transform x1 y of
    Diamond x1' y' -> case transform x2 y' of
      Diamond x2' y'' -> Diamond (compose x1' x2') y''

prop_transformComposeCommutativeLeft :: UTOpFan [S (S Z), S Z] -> Bool
prop_transformComposeCommutativeLeft (UTOpFan (OFCons (OSCons x1 (OSCons x2 _)) (OFCons (OSCons y _) _))) =
  composeThenTransformLeft x1 x2 y == transformThenComposeLeft x1 x2 y

data DiamondThree :: DocCtx -> DocCtx -> DocCtx -> * where
  DiamondThree :: Op b e -> Op c e -> Op d e -> DiamondThree b c d

deriving instance Show (DiamondThree b c d)

instance Eq (DiamondThree b c d) where
  a == b = show a == show b

transformThreeAssocL :: Op a b -> Op a c -> Op a d -> DiamondThree b c d
transformThreeAssocL x1 y1 z1 =
  case transform x1 y1 of
    Diamond x1' y1' -> case transform (compose y1 x1') z1 of
      Diamond z2 z1' ->
        let x2 = compose y1' z1'
            y2 = compose x1' z1'
        in DiamondThree x2 y2 z2

transformThreeAssocR :: Op a b -> Op a c -> Op a d -> DiamondThree b c d
transformThreeAssocR x1 y1 z1 =
  case transform y1 z1 of
    Diamond y1' z1' -> case transform x1 (compose y1 z1') of
      Diamond x1' x2 ->
        let y2 = compose z1' x1'
            z2 = compose y1' x1'
        in DiamondThree x2 y2 z2

prop_transformAssociative :: UTOpFan [S Z, S Z, S Z] -> Bool
prop_transformAssociative (UTOpFan (OFCons (OSCons x1 _) (OFCons (OSCons y1 _) (OFCons (OSCons z1 _) _)))) =
  transformThreeAssocL x1 y1 z1 == transformThreeAssocR x1 y1 z1

quickCheckAllProperties :: IO ()
quickCheckAllProperties = do
  quickCheck prop_composeAssociative
  quickCheck prop_composeIdentityLeft
  quickCheck prop_composeIdentityRight
  quickCheck prop_transformIdentityLeft
  quickCheck prop_transformIdentityRight
  quickCheck prop_transformCommutative
  quickCheck prop_transformComposeCommutativeLeft
  quickCheck prop_transformComposeCommutativeRight
  quickCheck prop_transformAssociative
