K : F Z (S x) y <= G (F Z x (S y)) (F x y (S (S Z)))

f : forall p qa qb f . (forall p x y . p (qa (f Z x (S y)) x y) => p (f Z (S x) y)) => 
                       (forall p y . p (qb (f Z y (S (S Z))) y) => p (f Z (S Z) y)) =>
                       p (f Z (S Z) (S Z)) 
f a1 a2 = a2 (f (\ c . a1 c) (\ c . (a2 (a1 c))))

-- h : F Z (S Z) (S Z)
-- h = K' (\ c . K c) (\ c . K c)
