K1 : Z (L x) <= L (Z x)
K2 : R (Z x) <= Z (R x)
K3 : Z (L (L x)) <= Z (L (R x))
K4 : R (R (Z x)) <= L (Z (R (Z x)))

f : forall p l r y . (forall p x . p (l (Z x)) => p (Z (l x))) =>
                    (forall p x . p (Z (r x)) => p (r (Z x))) =>
                    (forall p x . p (Z (L (r x))) => p (Z (L (l x)))) =>                    
         	    (forall p x . p (l (Z (R (Z x)))) => p (r (R (Z x)))) => p (Z (L (l (Z (Z (R (Z y)))))))

f a1 a2 a3 a4 = a3 (a2 (a2 (a4 (a1  (a1  (f (\ c . a1 c) (\ c . a2 c) (\ c . a3 (a2 c)) (\ c . a4 (a1 c)))))))) 

h : (Z (L (L (Z (Z (R (Z y)))))))
h = f K1 K2 (\ c . K3 c) K4