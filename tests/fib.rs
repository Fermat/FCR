Ka : A x <= A (B x)
Kb : B x <= A x

g : forall a b x .
      (forall p y . p (a y) => p (b y)) => 
      (forall p y . p (a (b y)) => p (a y)) => b x
g b a = b (g a (\ b1 . a (b b1)))


h : B x 
h = g Kb Ka

{- This is an example of wrong order.
  with existential var, the guideline is always put 
  (the sub-formula that doesn't contain ex-var in the head) first. 
g : forall a b x .
      (forall p y . p (a (b y)) => p (a y)) => 
      (forall p y . p (a y) => p (b y)) => b x
g a b = b (g (\ b1 . a (b b1)) a)
-} 