K1 : Eq (D x) <= G (Eq x) (Eq (D (D x)))
K2 : Eq Z <= Z

-- g : forall p x . ( forall p y . p y => p (Eq (D y))) => p (Eq (D x))
-- g a = K1 (g (\ c . a (a c)))

g : forall p x . p (Eq (D x))
g = K1 (K1 g)

h : forall p . p (Eq (D Z))
h = K1 (K2 (K1 h))