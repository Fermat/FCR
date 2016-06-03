{-# LANGUAGE RankNTypes, KindSignatures #-}

data El :: * -> *
data Dl  :: * -> *
data Bl   :: * -> *
data B :: * -> *
data C :: * -> *
data Cl :: * -> *
data X :: * -> *
data Y :: * -> *
data D :: * -> *
data Al :: * -> *
  
f :: forall p0 c b d y . (forall p x . p (B (Bl x)) -> p (Bl (B x))) ->
     (forall p x . p (B ( c (D x))) -> p (Bl ( c (Dl x)))) ->
     (forall p x . p (Dl (D x)) -> p (D (Dl x))) ->
     (forall p x . p (Al (Bl (Bl x))) -> p (Al (X x))) ->
     (forall p x . p (X (Bl x)) -> p (B (X x))) ->
     (forall p x . p (B ( b (Cl ( d (D x))))) -> p (Bl (Bl ( c (Dl (Dl x)))))) ->
     (forall p x . p (Dl (Y x)) -> p (Y (D x))) ->
     (forall p x . p (Dl (Dl (El x))) -> p (Y (El x))) ->
     (forall p x . p (X ( c (Y x))) -> p ( b (Cl ( d x)))) ->
     p0 (Al (Bl (Bl ( c (Dl (Dl (El y)))))))

f a1 a2 a3 a4 a5 b a7 a8 a6 = b (a6 (a5 (a7 (a4 (a8 (f a1 (\ c1 -> a2 (a1 (a3 c1))) a3 a4 a5 (\ c1 -> a2 (a1 (a3 (a1 (a3 (b c1)))))) a7 a8 (\ c1 -> a6 (a5 (a7 c1)))))))))
