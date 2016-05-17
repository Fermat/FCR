K1 : F x x ~> F O U
K2 : O ~> A
K3 : U ~> A

lemma a : forall x . F x x
proof
coind
intros x
apply K1 (\ y . y) x
apply K3 (\ y . F O y) 
apply K2 (\ y . F y A) 
apply a A
qed