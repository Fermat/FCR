K1 : forall x . Eq x => Eq (D (D x)) => Eq (D x)
K2 : Eq Int

e : forall x . Eq x => Eq (D x)
e x = K1 x (e e)

d : Eq (D Int)
d = e K2