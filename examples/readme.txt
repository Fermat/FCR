Some notes:

1. "K : A <= B" means rule "K" is a rewrite rule for "A" rewrites to "B". It will
generate "K : forall p x . p B => p A". The benefit of using "K : A <= B"
is that one can experiment rewriting using command :inner, :outer and :full. 
And "K : forall p x . p B => p A" is considered as an axiom by FCR, but not as rewrite rule.
Both formats are accepted by FCR.

