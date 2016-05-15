K1 : F x y ~> F (S x) (G (H x Z))
K2 : H (S x) y ~> H x (S y)
K3 : G (H x y) ~> J y

lemma h : forall f x z . (forall p x y . p (f (S x) (G (H x z))) => p (f x y)) => 
                         (forall p x y . p (H x (S y)) => p (H (S x) y)) => 
                         (forall p x y .p (J y) => p (G (H x y))) => f (S x) (G (H x z))
proof
coind h
intros f x z a1 a2 a3
apply a3 (\ y. f (S x) y) x z  -- f (S x) (J z)
apply a1 (\ y . y) (S x) (J z) -- f (S (S x)) (G (H (S x) z))
apply h (\ x y . f (S x) y) x (S z) -- 
use a1 with 
use a2 with 
qed
