A : D (S x) y ~> D x (S y)
B : D Z y ~> D (S y) Z


lemma f : forall d. (forall p x y . p (d x (S y)) => p (d (S x) y)) => 
              (forall p y . p (d (S y) Z) => p (d Z y)) => d Z Z

proof
coind
intros a1 a2
apply a2 (\ y. y) Z
apply a1 (\ y . y) Z Z
apply f (\ x y . d x (S y))
intros b1
apply a1 p x (S y)
apply b1
intros c1
apply a2 p (S y) 
apply a1 p (S y) Z
apply c1
qed
