K1 : G T T x (S y) <= G (N x) (N y) (S x) (D (S y))
K2 : N Z <= T
K3 : N (S x) <= N x
K4 : D Z <= Z
K5 : D (S x) <= S (S (D x))

f : forall p g n1 n2 s . 
    ((forall p x y . p (g (n1 x) (n2 y) (S x) (D (s y))) => 
                     p (g T T x (s y))) =>
    (forall p . p T => p (n1 Z)) =>
    (forall p . p T => p (n2 Z)) => 
    (forall p x . p (n1 x) => p (n1 (S x))) =>
    (forall p x . p (n2 x) => p (n2 (s x))) =>
    (forall p . p Z => p (D Z)) =>
    (forall p x . p (s (s (D x))) => p (D (s x))) => 
    p (g T T Z (s Z)))

f a1 a2 b2 a3 b3 a4 a5 = 
   a1 (a2 (b2 (a5 (a4 (f (\ c . a1 c) (\ c . a3 (a2 c)) 
                         (\ c . (b3 (b2 c))) 
                         (\ c . a3 c) 
                         (\ c . b3 (b3 c)) 
                         a4 
                         (\ c . a5 (a5 c)))))))

h : G T T Z (S Z)
h = f (\ c . K1 c) K2 K2 K3 K3 K4 K5