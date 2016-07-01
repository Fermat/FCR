K1 : A (L x) <= L (A x)
K2 : R (A x) <= A (R x)
K3 : B (L x) <= B (R x)
K4 : R (B x) <= L (A (B x))


f : forall p l r y . (forall p x . p (l (A x)) => p (A (l x))) =>
    	       	    (forall p x . p (B (r x)) => p (B (l x))) =>
                    (forall p x . p (A (r x)) => p (r (A x))) => 
		    (forall p x . p (l (A (B x))) => p (r (B x))) => p (B (l (B y)))

f a1 a3 a2 a4 = a3 (a4 (f (\ c . a1 c) (\ c . a3 (a2 c)) (\ c . a2 c) (\ c . a4 (a1 c))))

{-
f : forall p l r y . (forall p x . p (l (A x)) => p (A (l x))) =>
    	      
                    (forall p x . p (A (r x)) => p (r (A x))) => 
         	    (forall p x . p (B (r x)) => p (B (l x))) =>
		    (forall p x . p (l (A (B x))) => p (r (B x))) => p (B (l (B y)))

f a1 a2 a3 a4 = a3 (a4 (f (\ c . a1 c) (\ c . a2 c) (\ c . a3 (a2 c)) (\ c . a4 (a1 c))))
-}
h : B (L (B y))
h = f K1 (\ c . K3 c) K2 K4