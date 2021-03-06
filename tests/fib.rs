Ka : A x <= A (B x)
Kb : B x <= A x

g : forall a b x .
      (forall p y . p (a y) => p (b y)) => 
      (forall p y . p (a (b y)) => p (a y)) => b x
g b a = b (g (\ v . a v) (\ v . a (b v)))


h : B x 
h = g (\ v . Kb v) Ka

step h 21 
{- This is an example of wrong order.
  with existential var, the guideline is always put 
  (the sub-formula that doesn't contain ex-var in the head) first. 
g : forall a b x .
      (forall p y . p (a (b y)) => p (a y)) => 
      (forall p y . p (a y) => p (b y)) => b x
g a b = b (g (\ b1 . a (b b1)) a)
-} 