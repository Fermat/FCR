A : D (S x) y ~> D x (S y)
B : D Z y ~> D (S y) Z

g : forall p d . (forall p x y . p (d x (S y)) => p (d (S x) y)) => 
               (forall p y . p (d (S y) Z) => p (d Z y)) => p (d Z Z)
g a1 a2 = a2 (a1 (g a1 (\ c1 . a2 (a1 c1))))

e : D Z Z
e = g A B

{-
g : forall d. (forall p x y . p (d x (S y)) => p (d (S x) y)) => 
              (forall p y . p (d (S y) Z) => p (d Z y)) => d Z Z
g a1 a2 = a2 (a1 (g a1 (\ c1 . a2 (a1 c1))))
-}
{-
lemma f : forall d. (forall p x y . p (d x (S y)) => p (d (S x) y)) => 
              (forall p y . p (d (S y) Z) => p (d Z y)) => d Z Z

proof
coind
intros a1 a2
applyh a2 -- (\ y. y) Z
applyh a1 -- (\ y . y) Z Z
applyh f -- (\ x y . [d0] x (S y))
intros b1
applyh a1 -- [p7] [x8] (S [y9])
applyh b1
intros c1
applyh a2 -- [p13] (S [y14]) 
applyh a1 -- [p13] (S [y14]) Z
applyh c1
qed
-}