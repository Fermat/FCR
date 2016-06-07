K1 : A (A (L x)) <= L (A (A x))
K2 : R (A x) <= A (R x)
K3 : B (L x) <= B (R x)
K4 : R (B x) <= L (A (B x))
K5 : R (B x) <= A (L (B x))


f : forall p l r y . (forall p x . p (l (A (B x))) => p (r (B x))) => 
                     (forall p x . p (A (r x)) => p (r (A x))) =>
                     (forall p x . p (B (r x)) => p (B (l x))) =>
                     (forall p x . p (l (A (A x))) => p (A (A (l x)))) => 
                     (forall p x . p (A (l (B x))) => p (r (B x))) => p (B (r (B y)))

f a4 a2 a3 a1 a5 =
  a4 (a3 (a2 (a5 (a1 (a3 (a2 (a2 (f (\ c . a4 (a1 c)) 
                                    a2 
                                    (\ c . a3 (a2 (a2 c))) 
                                    a1 
                                    (\ c . a5 (a1 c))))))))))

h : B (R (B y))
h = f K4 K2 K3 K1 K5