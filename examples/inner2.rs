K1 : F x y <= F (S x) (G (H x Z))
K2 : H (S x) y <= H x (S y)
K3 : G (H x y) <= J y

g : forall p' f x z . (forall p x y . p (f (S x) (G (H x z))) => p (f x y)) => 
                          (forall p x y . p (H x (S y)) => p (H (S x) y)) => 
                              (forall p x y . p (J y) => p (G (H x y))) => 
                                   p' (f (S x) (G (H x z)))

g a1 a2 a3 = a3 (a1 (a2 (g (\ b1 . a1 (a2 b1)) a2 a3)))

h : F (S x) (G (H x Z))
h = g K1 K2 K3

