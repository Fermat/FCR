A : forall p x y . p (D x (S y)) => p (D (S x) y)
B : forall p y . p (D (S y) Z) => p (D Z y)

g : forall d . 
     (forall p x y . p (d x (S y)) => p (d (S x) y)) => 
     (forall p y . p (d (S y) Z) => p (d Z y)) => 
     d Z Z

g a1 a2 = a2 (a1 (g (\ v . a1 v) (\ v . a2 (a1 v))))

e : D Z Z
e = g (\ v . A v) (\ v . B v)

step e 100
