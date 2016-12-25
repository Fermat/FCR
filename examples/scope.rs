K : forall p x y . p (G (F Z x (S y)) (F x y (S (S Z)))) => p (F Z (S x) y)
    
K2 : forall qa . 
       (forall p x y . p (qa (F Z x (S y))) => p (F Z (S x) y)) =>
       B

h : B
h = K2 (\ c . K c)
