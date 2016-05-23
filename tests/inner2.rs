K1 : F x y ~> F (S x) (G (H x Z))
K2 : H (S x) y ~> H x (S y)
K3 : G (H x y) ~> J y

lemma h : forall p' f x z . (forall p x y . p (f (S x) (G (H x z))) => p (f x y)) => (forall p x y . p (H x (S y)) => p (H (S x) y)) => (forall p x y . p (J y) => p (G (H x y))) => p' (f (S x) (G (H x z)))
proof
coind
intros p' f x z a1 a2 a3
apply a3 (\ y . p' (f (S x) y)) x z  -- f (S x) (J z)
apply a1 (\ y . p' y) (S x) (J z) -- f (S (S x)) (G (H (S x) z))
apply a2 (\ y . p' (f (S (S x)) (G y))) x z -- f (S (S x)) (G (H x (S z)))
apply h p' (\ x y . f (S x) y) x (S z) -- 
intros p x y b1 -- p (f (S x) y)
apply a1 p (S x) y -- p (f (S (S x)) (G (H (S x) z)))
apply a2 (\ y . p (f (S (S x)) (G y))) x z -- p (f (S (S x)) (G (H x (S z))))
apply b1
use a2
use a3
qed
