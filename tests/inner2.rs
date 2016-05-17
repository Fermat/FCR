K1 : F x y ~> F (S x) (G (H x Z))
K2 : H (S x) y ~> H x (S y)
K3 : G (H x y) ~> J y

lemma h : forall f x z . (forall p x y . p (f (S x) (G (H x z))) => p (f x y)) => (forall p x y . p (H x (S y)) => p (H (S x) y)) => (forall p x y .p (J y) => p (G (H x y))) => f (S x) (G (H x z))
proof
coind
intros f x z a1 a2 a3
apply a3 (\ y. f (S x) y) x z  -- f (S x) (J z)
apply a1 (\ y . y) (S x) (J z) -- f (S (S x)) (G (H (S x) z))
apply a2 (\ y . f (S (S x)) (G y)) x z -- f (S (S x)) (G (H x (S z)))
apply h (\ x y . f (S x) y) x (S z) -- 
intros p x y b1 -- p (f (S x) y)
apply a1 p (S x) y -- p (f (S (S x)) (G (H (S x) z)))
apply a2 (\ y . p (f (S (S x)) (G y))) x z -- p (f (S (S x)) (G (H x (S z))))
apply b1
use a2
qed
