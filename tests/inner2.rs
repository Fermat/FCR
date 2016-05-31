K1 : F x y ~> F (S x) (G (H x Z))
K2 : H (S x) y ~> H x (S y)
K3 : G (H x y) ~> J y

lemma h : forall p' f x z . (forall p x y . p (f (S x) (G (H x z))) => p (f x y)) => 
                               (forall p x y . p (H x (S y)) => p (H (S x) y)) => 
                                  (forall p x y . p (J y) => p (G (H x y))) => 
                                      p' (f (S x) (G (H x z)))
proof
coind
intros a1 a2 a3
apply a3 (\ y . [p'0] ([f0] (S [x0]) y)) [x0] [z0]  -- f (S x) (J z)
apply a1 (\ y . [p'0] y) (S [x0]) (J [z0]) -- f (S (S x)) (G (H (S x) z))
apply a2 (\ y . [p'0] ([f0] (S (S [x0])) (G y))) [x0] [z0] -- f (S (S x)) (G (H x (S z)))
apply h [p'0] (\ x y . [f0] (S x) y) [x0] (S [z0]) -- 
intros b1 -- p (f (S x) y)
apply a1 [p17] (S [x17]) [y17] -- p (f (S (S x)) (G (H (S x) z)))
apply a2 (\ y . [p17] ([f0] (S (S [x17])) (G y))) [x17] [z0] -- p (f (S (S x)) (G (H x (S z))))
apply b1
use a2
use a3
qed

{-
h : forall p' f x z . (forall p x y . p (f (S x) (G (H x z))) => p (f x y)) => 
                          (forall p x y . p (H x (S y)) => p (H (S x) y)) => 
                              (forall p x y . p (J y) => p (G (H x y))) => 
                                   p' (f (S x) (G (H x z)))

h a1 a2 a3 = a3 (a1 (a2 (h (\ b1 . a1 (a2 b1)) a2 a3)))
-}
 