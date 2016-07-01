Ka : A x <= A (B x)
Kb : B x <= A x

g : forall a b x .
      (forall p y . p (a y) => p (b y)) => 
      (forall p y . p (a (b y)) => p (a y)) => b x
g b a = b (g (\ v . a v) (\ v . a (b v)))


h : B x 
h = g (\ v . Kb v) Ka

step h 21 
