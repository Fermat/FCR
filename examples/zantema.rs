A : F Z (S x) y <= F Z x (S y)
B : F Z (S x) y <= F x y (S (S Z))

f : forall p f . (forall p x y . p (f Z x (S y)) => p (f Z (S x) y)) =>
    	         (forall p y . p (f Z y (S (S Z))) => p (f Z (S Z) y)) => 
		 p (f Z (S Z) (S Z))
f a1 a2 = a2 (f (\ c . a1 c) (\ c . a2 (a1 c)))

h : F Z (S Z) (S Z)
h = f A (\ c . B c)

step h 7
