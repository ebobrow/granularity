Require Import Lia.

Lemma basic_arith : forall x y z,
    x * (y + z) = (x * y) + (x * z).
Proof. lia. Qed.
Print basic_arith.

Lemma simpler_arith : forall x y,
    x + y = y + x.
Proof. lia. Qed.
Print simpler_arith.
