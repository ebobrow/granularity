Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Coq.Logic.FunctionalExtensionality.

Definition set {A : Set} := (A -> bool).

Definition setA (x : nat) :=
  match x with
    | 0 | 1 | 2 => true
    | _ => false
  end.

Definition setB (x : nat) :=
  match x with
    | 3 | 4 | 5 => true
    | _ => false
  end.

Definition union {A : Set} (set1 set2 : @set A) : @set A :=
  fun x => orb (set1 x) (set2 x).

Compute ((union setA setB) 4).

Definition subset {A} (set1 set2 : @set A) : Prop :=
  forall x, set1 x = true -> set2 x = true.

Theorem proof1 {A} :
  forall x y : @set A, subset x y -> forall z, subset (union x z) (union y z).
Proof.
  unfold subset. unfold union. intros. apply orb_true_iff. apply orb_prop in H0. destruct H0; auto.
Qed.

Theorem proof2 {A} :
  forall a b c : @set A, union (union a b) c = union a (union b c).
Proof.
  intros. unfold union. apply functional_extensionality. intros.
  destruct (a x); auto.
Qed.

Theorem proof3 {A} :
  forall (a b : @set A) x, a x = false /\ (union a b) x = true -> b x = true.
Proof.
  intros a b x [nAx ABx]. unfold union in ABx. rewrite nAx in ABx. auto.
Qed.

Theorem subset_trans {A} :
  forall (a b c : @set A), subset a b /\ subset b c -> subset a c.
Proof.
  unfold subset. intros a b c [Hab Hbc] x Ha.
  auto.
  (* apply Hab in Ha. apply Hbc in Ha. apply Ha. *)
Qed.

Theorem subset_trans3 {A} :
  forall (a b c d : @set A), subset a b ->
                        subset b c ->
                        subset c d ->
                        subset a d.
Proof.
  intros. eapply subset_trans. split.
  - apply H.
  - eapply subset_trans. split; eauto.
Qed.

Theorem trans_app {A} :
  forall (a b c x : @set A), subset a b ->
                        subset b c ->
                        subset (union a x) (union c x).
Proof.
  intros. assert (subset a c). { eapply subset_trans. split; eassumption. }
  apply proof1. assumption.
Restart.
  intros. assert (subset (union a x) (union b x)). { apply proof1. assumption. }
          assert (subset (union b x) (union c x)). { apply proof1. assumption. }
  eapply subset_trans. split; eassumption.
Qed.

Structure group :=
  {
    G :> Set;

    id : G;
    op : G -> G -> G;
    inv : G -> G;

    op_assoc : forall (x y z : G), op x (op y z) = op (op x y) z;
    op_inv_l : forall (x : G), id = op (inv x) x;
    op_inv_r : forall (x : G), id = op x (inv x);
    op_id_l : forall (x : G), x = op id x;
    op_id_r : forall (x : G), x = op x id;
  }.

Arguments id {g}.
Arguments op {g} _ _.
Arguments inv {g} _.

Hint Resolve op_assoc : groups.
Hint Resolve op_inv_l : groups.
Hint Resolve op_inv_r : groups.
Hint Resolve op_id_l : groups.
Hint Resolve op_id_r : groups.

Fixpoint exp (G : group) (x : G) (n : nat) : G :=
  match n with
    | O => id
    | S n' => op x (exp G x n')
  end.
Arguments exp {G} _ _.

Notation "x <.> y" := (op x y) (at level 50, left associativity).
Notation "x ** n" := (exp x n) (at level 50, left associativity).

Lemma right_mul :
  forall (G : group) (x y z : G),
    x = y ->
    x <.> z = y <.> z.
Proof. intros. auto. rewrite H. reflexivity. Qed.

Lemma left_mul :
  forall (G : group) (x y z : G),
    x = y ->
    z <.> x = z <.> y.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma right_mul' :
  forall (G : group) (x y z : G),
    x <.> z = y <.> z ->
    x = y.
Proof.
  intros.
  apply right_mul with (z := inv z) in H.
  repeat rewrite <- op_assoc in H.
  repeat rewrite <- op_inv_r in H.
  repeat rewrite <- op_id_r in H.
  apply H.
Qed.

Lemma left_mul' :
  forall (G : group) (x y z : G),
    z <.> x = z <.> y ->
    x = y.
Proof.
  intros. apply left_mul with (z := inv z) in H.
  repeat rewrite op_assoc in H.
  repeat rewrite <- op_inv_l in H.
  repeat rewrite <- op_id_l in H.
  apply H.
Qed.

Lemma ab_inv :
  forall (G : group) (a b : G), inv (a <.> b) = (inv b) <.> (inv a).
Proof.
  intros. apply right_mul' with (z := a).
  rewrite <- op_assoc. rewrite <- op_inv_l. rewrite <- op_id_r.
  apply right_mul' with (z := b). rewrite <- op_inv_l.
  rewrite <- op_assoc. rewrite <- op_inv_l. reflexivity.
Qed.

Lemma mul_exp_eq_add :
  forall (G : group) (x : G) (n m : nat),
    x ** (n + m) = (x ** n) <.> (x ** m).
Proof with auto with groups.
  intros. induction n.
  - simpl...
  - simpl. rewrite IHn...
Qed.

Lemma add_comm : forall a b, a + b = b + a.
Proof. intros. induction a.
       - trivial.
       - simpl. rewrite IHa. rewrite plus_n_Sm. reflexivity.
Qed.

Lemma exp_commute :
  forall (G : group) (x : G) (n m : nat),
    (x ** n) <.> (x ** m) = (x ** m) <.> (x ** n).
Proof.
  intros. rewrite <- mul_exp_eq_add.
  rewrite add_comm.
  rewrite mul_exp_eq_add. reflexivity.
Qed.

Lemma stack_exp_eq_mul :
  forall (G : group) (x : G) (n m : nat),
    (x ** n) ** m = x ** (n * m).
Proof.
  intros. induction m.
  - simpl. induction n.
    + simpl. reflexivity.
    + simpl. assumption.
  - simpl. rewrite IHm.
    rewrite <- mult_n_Sm. rewrite mul_exp_eq_add.
    rewrite exp_commute. reflexivity.
Qed.

Lemma id_exp_eq_id : forall (G : group) (n : nat), @id G ** n = id.
Proof.
  induction n.
  - trivial.
  - simpl. rewrite IHn. auto with groups.
Qed.

Lemma ord2_impl_inv :
  forall (G : group) (x : G), x <.> x = id ->
                         x = inv x.
Proof.
  intros. apply left_mul' with (z := x). rewrite <- op_inv_r.
  apply H.
Qed.

Lemma ord2_impl_abel :
  forall (G : group), (forall x : G, x <.> x = id) ->
                 (forall x y : G, x <.> y = y <.> x).
Proof.
  intros. set (Hactive := H).
  specialize Hactive with (x <.> y).
  apply ord2_impl_inv in Hactive.
  rewrite ab_inv in Hactive.
  set (Hx := H). specialize Hx with x. specialize H with y.
  apply ord2_impl_inv in H. apply ord2_impl_inv in Hx.
  rewrite <- H in Hactive. rewrite <- Hx in Hactive. apply Hactive.
  Show Proof.
Qed.
(* Restart. *)
(*   intros. specialize H with (x <.> y). move/ord2_impl_inv in H. *)
(*   intros. rewrite <- H with (x := x <.> y). (* TODO: learn ssreflect *) *)

Definition has_order (G : group) (x : G) (n : nat) : Prop :=
  x ** n = id /\ ~(exists m, 0 < m < n /\ x ** m = id).
Arguments has_order {G} _ _.

Lemma div : forall m n,
    m >= n ->
    (* m = n * (m / n) + (m mod n). *)
    (exists k r, m = n * k + r /\ 1 <= k /\ 0 <= r < n).
Proof.
Admitted.

Lemma m_l_n_gt : forall n m, ~(m < n) -> m >= n.
Admitted.

Lemma fin_ord_div : forall (G : group) (x : G) (n m : nat),
    m > 0 ->
    has_order x n -> x ** m = id -> (exists a, m = mul n a).
Proof.
  unfold has_order. intros G x n m Hmp [Hn Hnmin] Hm.
  assert (~(m < n)). {
    unfold not. intros. apply Hnmin. exists m. auto.
  }
  assert (m >= n). {
    apply m_l_n_gt. assumption.
  }
  apply div in H0. destruct H0 as [k [r [H0 [Hk Hr]]]]. rewrite H0 in Hm.
  rewrite mul_exp_eq_add in Hm. rewrite <- stack_exp_eq_mul in Hm.
  rewrite Hn in Hm. rewrite id_exp_eq_id in Hm.
  rewrite <- op_id_l in Hm.
  assert (~(r > 0)). {
    unfold not. intros. apply Hnmin. exists r. split.
    - split.
      + auto.
      + destruct Hr. assumption.
    - assumption.
  }
  assert (r = 0). {
    induction r.
    - reflexivity.
    - exfalso. apply H1. unfold gt. unfold lt. apply le_n_S. apply le_0_n.
  }
  rewrite H2 in H0. rewrite <- plus_n_O in H0. exists k. assumption.
  Show Proof.
Qed.
