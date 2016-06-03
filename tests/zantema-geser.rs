K : F Z (S x) y ~> G (F Z x (S y)) (F x y (S (S Z)))
-- G (F Z Z (S y)) (F Z y (S (S Z)))
{-
f : forall p qa qb f . (forall p x y . p (qa (f Z x (S y))) => p (f Z (S x) y)) => 
                       (forall p y . p (qb (f Z y (S (S Z)))) => p (f Z (S Z) y)) => p (f Z (S Z) (S Z)) 
f a1 a2 = a2 (f a1 (\ c . (a2 (a1 c))))
-}


f : forall p f g . (forall p x y . p (g (f Z x (S y)) (f x y (S (S Z)))) => p (f Z (S x) y)) => 
                       (forall p x y . p (g (f Z x (S y)) (f x y (S (S Z)))) => p (f Z (S x) y)) => p (f Z (S Z) (S Z)) 
f a1 a2 = a2 (f a1 (\ c . (a2 (a1 c))))


-- h : F Z (S Z) (S Z)
-- h = f K K