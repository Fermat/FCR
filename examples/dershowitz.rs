K : F (G x) <= G (G (F (F x)))

h : forall p x . p (F (F (G x)))
h = K (K h)

e : F (F (G x))
e = h 