Require Export Omega.
Require Export Peano_dec.

Section U_SETS.
  Variable U : Set.
  Definition U_set := U -> Prop.
  Axiom U_set_eq : forall E F : U_set, (forall x : U, E x = F x) -> E = F. (* functional extensionality *)

  Lemma U_eq_set : forall E F : U_set, E = F -> forall x : U, E x = F x.
  Proof.
    intros E F H x. rewrite H. reflexivity.
  Qed.

  Lemma U_set_commute : forall E F : U_set, E = F -> F = E.
  Proof. auto. Qed.

  Lemma U_set_diff_commute : forall E F : U_set, E <> F -> F <> E.
  Proof.
    intros E F. unfold not. intros H1 H2. apply H1.
    apply U_set_commute. trivial.
  Qed.

  Inductive Empty : U_set :=.
  Inductive Full : U_set :=
    In_full : forall x : U, Full x.
  Inductive Single (x : U) : U_set :=
    In_single : Single x x.

  Lemma single_equal : forall x y : U, Single x y -> x = y.
  Proof.
    intros x y H. inversion H. trivial.
  Qed.

  Lemma Single_equal_single : forall x y : U, Single x = Single y -> x = y.
  Proof.
    intros x y H. generalize  (U_eq_set _ _ H x).
    intros H1. symmetry. apply single_equal. rewrite <- H1.
    apply In_single.
  Qed.

  Lemma Empty_nothing : forall x : U, ~Empty x.
  Proof.
    unfold not. intros x H. inversion H.
  Qed.

  Lemma U_set_diff : forall E F : U_set, (exists x, E x /\ ~ F x) -> E <> F.
  Proof.
    unfold not. intros E F H1 H2. destruct H1. destruct H. apply H0.
    rewrite <- H2. trivial.
  Qed.

  Section INCLUSION.
    Definition Included (E F : U_set) : Prop :=
      forall x : U,  E x -> F x.

    Lemma Included_single :
      forall (E : U_set) (x : U), E x -> Included (Single x) E.
    Proof.
      unfold Included. intros E x H1 x0 H2. inversion H2.
      rewrite <- H. trivial.
    Qed.
  End INCLUSION.

  Section UNION.
    Inductive Union (E F : U_set) : U_set :=
    | In_left : forall x : U, E x -> Union E F x
    | In_right : forall x : U, F x -> Union E F x.

    Lemma Union_eq :
      forall E F E' F' : U_set, E = E' -> F = F' -> Union E F = Union E' F'.
    Proof.
      intros. rewrite H. rewrite H0. reflexivity.
    Qed.

    Lemma Union_neutral :
      forall e : U_set, Union Empty e = e.
    Proof.
      intros. apply U_set_eq. intros x.
      

  End UNION.
