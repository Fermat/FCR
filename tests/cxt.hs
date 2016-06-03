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

f = undefined

k8 :: forall p x . p (Dl (Dl (El x))) -> p (Y (El x))
k8 = undefined
k7 :: forall p x . p (Dl (Y x)) -> p (Y (D x))
k7 = undefined
k6 :: forall p x . p (X (Cl (Y x))) -> p (Bl (Cl (Dl x)))
k6 = undefined
k5 :: forall p x . p (X (Bl x)) -> p (B (X x))
k5 = undefined
k4 :: forall p x . p (Al (Bl (Bl x))) -> p (Al (X x))
k4 = undefined
k3 :: forall p x . p (Dl (D x)) -> p (D (Dl x))
k3 = undefined
k2 :: forall p x . p (B (Cl (D x))) -> p (Bl (Cl (Dl x)))
k2 = undefined
k1 :: forall p x . p (B (Bl x)) -> p (Bl (B x))
k1 = undefined

h :: (Al (Bl (Bl ( Cl (Dl (Dl (El y)))))))
h = f k1 k2 k3 k4 k5 (\ c -> k2 (k1 (k3 c))) k7 k8 k6
-- f a1 a2 a3 a4 a5 b a7 a8 a6 = b (a6 (a5 (a7 (a4 (a8 (f a1 (\ c1 -> a2 (a1 (a3 c1))) a3 a4 a5 (\ c1 -> a2 (a1 (a3 (a1 (a3 (b c1)))))) a7 a8 (\ c1 -> a6 (a5 (a7 c1)))))))))
