K : F Z (S x) y <= G (F Z x (S y)) (F x y (S (S Z)))
-- G (F Z Z (S y)) (F Z y (S (S Z)))

f : forall p qa qb f . (forall p x y . p (qa (f Z x (S y))) => p (f Z (S x) y)) => 
                       (forall p y . p (qb (f Z y (S (S Z)))) => p (f Z (S Z) y)) => p (f Z (S Z) (S Z)) 
f a1 a2 = a2 (f (\ c . a1 c) (\ c . (a2 (a1 c))))


-- f : forall p qa qb f . (forall p b . p (qb (f Z b (S (S Z))) Z b) => p (f Z (S Z) b)) =>
--                        (forall p a c . p (qa (f Z a (S c)) (F a c (S (S Z)))) => p (f Z (S a) c)) => 
--                         p (f Z (S Z) (S Z)) 
-- f a2 a1 = a2 (f (\ c . (a2 (a1 c))) a1)




h : F Z (S Z) (S Z)
h = f (\ c . K c) (\ c . K c)