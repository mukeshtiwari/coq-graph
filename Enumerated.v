Require Export Sets.
Require Export List.

Section ENUMERATION.

  Variable U : Set.
  Hypothesis U_seperable : forall x y : U, {x = y} + {x <> y}.
  Definition U_list := list U.

  Definition U_enumerable (E : U_set U) :=
    {ul : U_list | forall x : U, E x -> In x ul}.

  Inductive U_canon : U_list -> Prop :=
  | U_canon_nil : U_canon nil
  | U_canon_cons :
      forall (x : U) (ul : U_list), U_canon ul -> ~ In x ul -> U_canon (x :: ul).

  Lemma U_in_dec :
    forall (x : U) (ul : U_list), {In x ul} + {~ In x ul}.
  Proof.
    simple induction ul; intros.
    right; red; intros; inversion H.
    case (U_seperable x a); intros H0.
    left; simpl; info_auto.
    case H; intros H1.
    left; simpl; info_auto.
    right; red; intros H2; inversion H2.
    apply H0;auto.
    elim H1; auto.
  Qed.

  Variable f : U -> nat.

  Fixpoint U_sum (ul : U_list) : nat :=
    match ul with
    | nil => 0
    | x :: ul' => f x + U_sum ul'
    end.

  Lemma U_enumerable_sum : forall E : U_set U, U_enumerable E -> nat.
  Proof.
    intros. elim H; intros.
    apply (U_sum x).
  Defined.

  
End ENUMERATION.
