Ka : A x <= A (B x)
Kb : B x <= A x

g : forall a b x .
      (forall p y . p (a (b y)) => p (a y)) =>
      (forall p y . p (a y) => p (b y)) => a x
       
g a b = a (g (\ v . a (b v)) (\ v . a v))


h : A x 
h = g (\ v . Ka v) Kb

step h 20
