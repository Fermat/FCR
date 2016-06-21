K1 : Bl (B x) <= B (Bl x)
K2 : Bl (Cl (Dl x)) <= B (Cl (D x))
K3 : D (Dl x) <= Dl (D x)
K4 : Al (X x) <= Al (Bl (Bl x))
K5 : B (X x) <= X (Bl x)
K6 : Bl (Cl (Dl x)) <= X (Cl (Y x))
K7 : Y (D x) <= Dl (Y x)
K8 : Y (El x) <= Dl (Dl (El x))


f : forall p0 c b d y . (forall p x . p (B (Bl x)) => p (Bl (B x))) =>
    	      	      	(forall p x . p (B ( c (D x))) => p (Bl ( c (Dl x)))) =>
			(forall p x . p (Dl (D x)) => p (D (Dl x))) =>
			(forall p x . p (Al (Bl (Bl x))) => p (Al (X x))) =>
			(forall p x . p (X (Bl x)) => p (B (X x))) =>
			(forall p x . p (B ( b (Cl ( d (D x))))) => p (Bl (Bl ( c (Dl (Dl x)))))) =>
			(forall p x . p (Dl (Y x)) => p (Y (D x))) =>
			(forall p x . p (Dl (Dl (El x))) => p (Y (El x))) =>
			(forall p x . p (X ( c (Y x))) => p ( b (Cl ( d x)))) =>
			p0 (Al (Bl (Bl ( c (Dl (Dl (El y)))))))

f a1 a2 a3 a4 a5 b a7 a8 a6 = b (a6 (a5 (a7 (a4 (a8 (f a1 (\ c1 . a2 (a1 (a3 c1))) a3 a4 a5 (\ c1 . a2 (a1 (a3 (a1 (a3 (b c1)))))) a7 a8 (\ c1. a6 (a5 (a7 c1)))))))))

{-
f : forall p c b d y . (forall p x . p (B (Bl x)) => p (Bl (B x))) =>
    	      	      	(forall p x . p (B ( c (D x))) => p (Bl ( c (Dl x)))) =>
			(forall p x . p (Dl (D x)) => p (D (Dl x))) =>
			(forall p x . p (Al (Bl (Bl x))) => p (Al (X x))) =>
			(forall p x . p (X (Bl x)) => p (B (X x))) =>
                        (forall p x . p (X ( c (Y x))) => p ( b (Cl ( d x)))) =>
			(forall p x . p (Dl (Y x)) => p (Y (D x))) =>
			(forall p x . p (Dl (Dl (El x))) => p (Y (El x))) =>
			(forall p x . p (B ( b (Cl ( d (D x))))) => p (Bl (Bl ( c (Dl (Dl x)))))) =>
			p (Al (Bl (Bl ( c (Dl (Dl (El y)))))))

f a1 a2 a3 a4 a5 a6 a7 a8 b  = b (a6 (a5 (a7 (a4 (a8 (f a1 (\ c1 . a2 (a1 (a3 c1))) a3 a4 a5 (\ c1. a6 (a5 (a7 c1))) a7 a8 (\ c1 . a2 (a1 (a3 (a1 (a3 (b c1)))))) ))))))
-}
h : (Al (Bl (Bl ( Cl (Dl (Dl (El y)))))))
h = f K1 K2 K3 K4 K5 (\ c . K2 (K1 (K3 c))) K7 K8  K6

step h 9
step h 10
step h 10000