# interpreter


{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE StandaloneDeriving        #-}

module Main where

import Control.Applicative ((<$>), (<*>), (<|>))
import Control.Monad (forever)
import Data.Attoparsec.Text
import Data.Monoid ((<>))
import Data.Ratio (numerator, denominator)
import Data.Text (Text)
import Numeric.Natural (Natural)
import System.IO (hSetBuffering, stdout, BufferMode (NoBuffering))
import Test.QuickCheck
import Test.QuickCheck.Arbitrary

import qualified Data.Text as W
import qualified Data.Text.IO as W

import Prelude hiding (Wyrazenie, exp)

-- struktura możliwych wyrażeń

data Wyrazenie a where
    Nat :: !Natural -> Wyrazenie Nat
    Neg :: CNeg x => !(Wyrazenie x) -> Wyrazenie Neg
    Bra :: CBra x => !(Wyrazenie x) -> Wyrazenie Bra
    Dodaj :: CDodaj x y => !(Wyrazenie x) -> !(Wyrazenie y) -> Wyrazenie Dodaj
    Odejmij :: CDodaj x y => !(Wyrazenie x) -> !(Wyrazenie y) -> Wyrazenie Dodaj
    Mnoz :: CMnoz x y => !(Wyrazenie x) -> !(Wyrazenie y) -> Wyrazenie Mnoz
    Dziel :: CMnoz x y => !(Wyrazenie x) -> !(Wyrazenie y) -> Wyrazenie Mnoz

class CNeg  a -- 'a' mozna zanegowac
class CBra  a -- 'a' moze byc zagniezdzony w nawiasach
class CDodajL a -- 'a' moze byc lewym operandem przy dodawaniu
class CDodajR a -- 'a' moze byc prawym operandem przy dodawaniu
class CMnozL a -- 'a' moze byc lewym operandem przy mnozeniu
class CMnozR a -- 'a' moze byc prawym operandem przy mnozeniu

type CDodaj a b = (CDodajL a, CDodajR b) -- 'a' and 'b' moze byc dodane razem
type CMnoz a b = (CMnozL a, CMnozR b) -- 'a' can 'b' moze byc pomnozone razem

data Nat; instance CNeg Nat;                  ; instance CDodajL Nat; instance CDodajR Nat; instance CMnozL Nat; instance CMnozR Nat
data Neg;                  ; instance CBra Neg; instance CDodajL Neg;                   ;                   ;
data Bra; instance CNeg Bra;                  ; instance CDodajL Bra; instance CDodajR Bra; instance CMnozL Bra; instance CMnozR Bra
data Dodaj;                  ; instance CBra Dodaj; instance CDodajL Dodaj;                   ;                   ;
data Mnoz;                  ; instance CBra Mnoz; instance CDodajL Mnoz; instance CDodajR Mnoz; instance CMnozL Mnoz;

data TWyrazenie = forall a . TWyrazenie (Wyrazenie a)
data DodajL = forall a . CDodajL a => DodajL (Wyrazenie a)
data DodajR = forall a . CDodajR a => DodajR (Wyrazenie a)
data MnozL = forall a . CMnozL a => MnozL (Wyrazenie a)
data MnozR = forall a . CMnozR a => MnozR (Wyrazenie a)

addAny (DodajL a) (DodajR b) = Dodaj a b
subAny (DodajL a) (DodajR b) = Odejmij a b
mulAny (MnozL a) (MnozR b) = Mnoz a b
divAny (MnozL a) (MnozR b) = Dziel a b

instance Eq (Wyrazenie a) where a == b = toUExp a == toUExp b
instance Eq TWyrazenie where (TWyrazenie a) == (TWyrazenie b) = toUExp a == toUExp b

deriving instance Show (Wyrazenie a)
instance Show TWyrazenie where show (TWyrazenie e) = show e

-- Nieokreślone wyrażeniem, czyli takie bez typu

data UExp
    = UNat !Natural
    | UNeg !UExp
    | UDodaj !UExp !UExp
    | UOdejmij !UExp !UExp
    | UMnoz !UExp !UExp
    | UDziel !UExp !UExp
    deriving (Eq, Show)

-- Konwertuje wyrażenie nieokreślone na typ określony zrozumiały przez interpreter.

toUExp :: Wyrazenie a -> UExp
toUExp = \case
    Nat a -> UNat a
    Neg a -> UNeg (toUExp a)
    Bra a -> toUExp a
    Dodaj a b -> UDodaj (toUExp a) (toUExp b)
    Odejmij a b -> UOdejmij (toUExp a) (toUExp b)
    Mnoz a b -> UMnoz (toUExp a) (toUExp b)
    Dziel a b -> UDziel (toUExp a) (toUExp b)

-- Konwertuje wyrażenie nieokreślone na typ określony zrozumiały przez interpreter.

toTExp :: UExp -> TWyrazenie
toTExp = \case
        UNat a   -> TWyrazenie $ Nat a
        UNeg a   -> TWyrazenie $ neg a
        UDodaj a b -> TWyrazenie $ add a b
        UOdejmij a b -> TWyrazenie $ sub a b
        UMnoz a b -> TWyrazenie $ mul a b
        UDziel a b -> TWyrazenie $ div a b
    where
        neg = \case
            UNat a   -> Neg $ Nat a
            UNeg a   -> Neg $ Bra $ neg a
            UDodaj a b -> Neg $ Bra $ add a b
            UOdejmij a b -> Neg $ Bra $ sub a b
            UMnoz a b -> Neg $ Bra $ mul a b
            UDziel a b -> Neg $ Bra $ div a b

        add a b = addAny (dodajL a) (dodajR b)
        sub a b = subAny (dodajL a) (dodajR b)
        mul a b = mulAny (mnozL a) (mnozR b)
        div a b = divAny (mnozL a) (mnozR b)

        dodajL = \case
            UNat a   -> DodajL $ Nat a
            UNeg a   -> DodajL $ neg a
            UDodaj a b -> DodajL $ add a b
            UOdejmij a b -> DodajL $ sub a b
            UMnoz a b -> DodajL $ mul a b
            UDziel a b -> DodajL $ div a b

        dodajR = \case
            UNat a   -> DodajR $ Nat a
            UNeg a   -> DodajR $ Bra $ neg a
            UDodaj a b -> DodajR $ Bra $ add a b
            UOdejmij a b -> DodajR $ Bra $ sub a b
            UMnoz a b -> DodajR $ mul a b
            UDziel a b -> DodajR $ div a b

        mnozL = \case
            UNat a   -> MnozL $ Nat a
            UNeg a   -> MnozL $ Bra $ neg a
            UDodaj a b -> MnozL $ Bra $ add a b
            UOdejmij a b -> MnozL $ Bra $ sub a b
            UMnoz a b -> MnozL $ mul a b
            UDziel a b -> MnozL $ div a b

        mnozR = \case
            UNat a   -> MnozR $ Nat a
            UNeg a   -> MnozR $ Bra $ neg a
            UDodaj a b -> MnozR $ Bra $ add a b
            UOdejmij a b -> MnozR $ Bra $ sub a b
            UMnoz a b -> MnozR $ Bra $ mul a b
            UDziel a b -> MnozR $ Bra $ div a b

-- Prosty generator arbitralnych wyrażeń

instance Arbitrary UExp where
    arbitrary = sized tree
        where
            tree 0 = UNat <$> arbitrary
            tree n = oneof
                    [ UNeg <$> x
                    , UDodaj <$> x <*> x
                    , UOdejmij <$> x <*> x
                    , UMnoz <$> x <*> x
                    , UDziel <$> x <*> x ]
                where
                    x = tree $ n * 3 `div` 4
    shrink = \case
            UNat n -> UNat <$> shrink n
            UNeg a -> a : (UNeg <$> shrink a)
            UDodaj a b -> s UDodaj a b
            UOdejmij a b -> s UOdejmij a b
            UMnoz a b -> s UMnoz a b
            UDziel a b -> s UDziel a b
        where
            s op a b =
                (a : ((a `op`) <$> shrink b)) <>
                (b : ((`op` b) <$> shrink a))

instance Arbitrary TWyrazenie where
    arbitrary = toTExp <$> arbitrary

-- Obliczanie wyrazenia

evalT :: TWyrazenie -> Rational
evalT (TWyrazenie e) = eval e

evalU :: UExp -> Rational
evalU = evalT . toTExp

eval :: Wyrazenie a -> Rational
eval = \case
    Nat a -> fromIntegral a
    Neg a -> negate $ eval a
    Bra a -> eval a
    Dodaj a b -> eval a + eval b
    Odejmij a b -> eval a - eval b
    Mnoz a b -> eval a * eval b
    Dziel a b -> eval a / eval b

-- Wyswietlanie wyniku w przejrzysty stylu

prettyU :: UExp -> Text
prettyU = prettyT . toTExp

prettyT :: TWyrazenie -> Text
prettyT (TWyrazenie e) = pretty e

pretty :: Wyrazenie a -> Text
pretty = \case
    Nat a -> W.pack $ show a
    Neg a -> textNeg <> pretty a
    Bra a -> textBra <> pretty a <> textKet
    Dodaj a b -> pretty a <> textAdd <> pretty b
    Odejmij a b -> pretty a <> textSub <> pretty b
    Mnoz a b -> pretty a <> textMul <> pretty b
    Dziel a b -> pretty a <> textDiv <> pretty b

prettyR :: Rational -> Text
prettyR r = if denominator r == 1 then n else n <> "/" <> d
    where
        n = W.pack $ show $   numerator r
        d = W.pack $ show $ denominator r

-- Stałe operatory arytmetyczne wykorzystywane do obliczeń wyrazenia


charMul = '*'; textMul = W.singleton charMul
charDiv = '/'; textDiv = W.singleton charDiv
charAdd = '+'; textAdd = W.singleton charAdd
charSub = '-'; textSub = W.singleton charSub
charBra = '('; textBra = W.singleton charBra
charKet = ')'; textKet = W.singleton charKet
charNeg = '-'; textNeg = W.singleton charNeg

-- Parsowanie wprowadzonego wyrazenia

uexp :: Parser UExp
uexp = choice [x <* endOfInput | x <- [add, mul, neg, nat]]
    where
        nat = UNat <$> decimal
        neg = UNeg <$> choice [char charNeg *> x | x <- [nat, bra]]
        bra = choice [char charBra *> x <* char charKet | x <- [add, mul, neg]]
        add = chainL (choice [mul, nat, neg, bra]) addOp (choice [mul, nat, bra])
        mul = chainL (choice [nat, bra]) mulOp (choice [nat, bra])
        addOp = choice [char charAdd *> pure UDodaj, char charSub *> pure UOdejmij]
        mulOp = choice [char charMul *> pure UMnoz, char charDiv *> pure UDziel]

chainL :: Parser b -> Parser (b -> a -> b) -> Parser a -> Parser b
chainL l o r = apply <$> l <*> o <*> r >>= rest
    where
        rest l = (apply l <$> o <*> r >>= rest) <|> return l
        apply l o r = l `o` r

-- Testowanie operatorow wyrazania

propPrintParseIdentity :: UExp -> Bool
propPrintParseIdentity e =
    case parseOnly uexp (prettyU e) of
        Left e -> False
        Right r -> e == r

propNoDoubleOperators :: TWyrazenie -> Bool
propNoDoubleOperators e = not $ or
    [x `W.isInfixOf` prettyT e | x <- doubleOperators]

singleOperators :: [Char]
singleOperators = [charNeg, charAdd, charSub, charMul, charDiv]

doubleOperators :: [Text]
doubleOperators = [W.pack [x, y] | x <- singleOperators, y <- singleOperators]

-- Interfejs wiersza poleceń kalkulatora
{-| Główna funkcja main odpowiedzialna za wprowadzenie dowolnego wyrażenia arytmetycznego -}
main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    putStrLn "Wprowadz wyrazenie arytmentyczne ktore ma zostac obliczone"
    forever $ do
        W.putStr "> "
        W.getLine >>= W.putStrLn . calculate . stripSpaces

stripSpaces :: Text -> Text
stripSpaces = W.filter (/= ' ')

{-| Parses the given expression, evaluates the resulting
    expression tree, and then pretty prints the result. -}
calculate :: Text -> Text
calculate e =
    case parseOnly uexp e of
        Left e -> "Bledne wyrazenie! Sprobuj ponownie"
        Right r -> prettyU r <> textEqu <> prettyR (evalU r)
