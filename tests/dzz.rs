A : forall p x y . p (D x (S y)) => p (D (S x) y)
B : forall p y . p (D (S y) Z) => p (D Z y)
-- A : D (S x) y <= D x (S y)
-- B : D Z y <= D (S y) Z

-- B : forall p y . p (D (S y) Z) => p (D Z y)
-- A : forall p x y . p (D x (S y)) => p (D (S x) y)

-- comp : forall a b c . (b => c) => (a => b) => a => c
-- comp f l x = f (l x)

g : forall d . 
     (forall p x y . p (d x (S y)) => p (d (S x) y)) => 
     (forall p y . p (d (S y) Z) => p (d Z y)) => 
     d Z Z

-- g a1 a2 = a2 (a1 (g (\ v . a1 v) (\ v . a2 (a1 v))))
g a1 a2 = a2 (a1 (g (\ v . a1 v) (\ v . a2 (a1 v))))
e : D Z Z
e = g (\ v . A v) (\ v . B v)


-- g : forall p d . (forall p x y . p (d x (S y)) => p (d (S x) y)) => 
--                (forall p y .  p (d (S y) Z) => p (d Z y)) => p (d Z Z)
-- g a1 a2 =  a2 (a1 (g (\ c . a1 c) (\ c1 . a2 (a1 c1))))

-- e : D Z Z
-- e = g A B 

-- step e 10

-- step e 1
-- step e 2
-- step e 3
-- step e 4
-- step e 5
-- step e 100

{-
l : forall a . a => a
l x = x
-}
-- C : forall y . D (S y) Z => D Z y 
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