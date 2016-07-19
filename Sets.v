Require Export Omega.
Require Export Peano_dec.

Section U_SETS.
  Variable U : Set.
  Definition U_set := U -> Prop.
  Axiom U_set_eq : forall E F : U_set, (forall x : U, E x <-> F x) -> E = F. (* functional extensionality *)

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

   Lemma Union_neutral : forall e : U_set, Union Empty e = e.
   Proof.
     intros. apply U_set_eq. intros x. split.
     - intros H. destruct H. inversion H. assumption.
     - intros H. apply In_right. assumption.
   Qed.

   Lemma Union_commut : forall e1 e2 : U_set, Union e1 e2 = Union e2 e1.
   Proof.
     intros e1 e2; apply U_set_eq; split; intros.
     inversion H; [apply In_right | apply In_left]; trivial.
     inversion H; [apply In_right | apply In_left]; trivial.
   Qed.

   Lemma Union_assoc : forall (e1 e2 e3 : U_set), Union (Union e1 e2) e3 = Union e1 (Union e2 e3).
   Proof.
     intros e1 e2 e3; apply U_set_eq; split; intros.
     inversion H. inversion H0. apply In_left. trivial.
     apply In_right. apply In_left. trivial.
     apply In_right. apply In_right. trivial.
     inversion H.
     apply In_left. apply In_left. trivial.
     inversion H0.
     apply In_left. apply In_right. trivial.
     apply In_right. trivial.
   Qed.

 
   Lemma Not_union :
     forall (E1 E2 : U_set) (x : U), ~E1 x -> ~E2 x -> ~ (Union E1 E2 x).
   Proof.
     unfold not. intros. inversion H1. apply H. trivial.
     apply H0; trivial.
   Qed.

  

   Lemma Union_dec :
     forall (e1 e2 : U_set) (x : U),
       {e1 x} + {~ e1 x} -> {e2 x} + {~ e2 x} -> Union e1 e2 x -> {e1 x} + {e2 x}.
   Proof.
     intros; case H.
     left; trivial.

     intros; case H0; intros.
     right; trivial.

     absurd (Union e1 e2 x). apply Not_union; trivial.
     trivial.

   Qed.

   Lemma Included_union : forall E F : U_set, Included E (Union E F).
   Proof.
     unfold Included; intros.
     apply In_left; trivial.
   Qed.

   Lemma Union_absorb :
     forall E F : U_set, Included E F -> Union E F = F.
   Proof.
     intros; apply U_set_eq; split; intros.
     inversion H0; auto.

     apply In_right; trivial.

   Qed.

  End UNION.

  Section INTESECTION.

    Inductive Inter (E F : U_set) : U_set :=
      In_inter: forall x : U, E x -> F x -> Inter E F x.

    Lemma Inter_eq :
      forall E F E' F' : U_set, E = E' -> F = F' -> Inter E F = Inter E' F'.
    Proof.
      intros; apply U_set_eq; split; intros.
      rewrite <- H; rewrite <- H0; trivial.
      rewrite H; rewrite H0; trivial.
    Qed.

    Lemma  Inter_neutral:
      forall e : U_set, Inter Full e = e.
    Proof.
      intros; apply U_set_eq; split; intros.
      inversion H; trivial.
      apply In_inter.
      apply In_full; trivial.
      trivial.
    Qed.

    Lemma Inter_empty :
      forall e : U_set, Inter e Empty = Empty.
    Proof.
      intros; apply U_set_eq; split; intros.
      inversion H; trivial.
      inversion H.
    Qed.

    Lemma Inter_commute :
      forall e1 e2 : U_set, Inter e1 e2 = Inter e2 e1.
    Proof.
      intros; apply U_set_eq; split; intros.
      inversion H; constructor; trivial.
      inversion H; constructor; trivial.
    Qed.

    Lemma Inter_assoc: forall e1 e2 e3 : U_set,
        Inter e1 (Inter e2 e3) = Inter (Inter e1 e2) e3.
    Proof.
      intros; apply U_set_eq; split; intros.
      inversion H; inversion H1; apply In_inter. apply In_inter; trivial.
      trivial.
      inversion H; inversion H0; apply In_inter; trivial.
      apply In_inter; trivial.
    Qed.

    Lemma Not_inter : forall (E1 E2 : U_set) (x : U),
        ~ E1 x -> ~ Inter E1 E2 x.
    Proof.
      unfold not; intros.
      inversion H0; apply H; trivial.
    Qed.

    Lemma Included_inter : forall E F : U_set,
        Included (Inter E F) E.
    Proof.
      unfold Included; intros; inversion H; trivial.
    Qed.

    Lemma Inter_absorb : forall E F : U_set, Included E F -> Inter E F = E. 
    Proof.
      intros. apply U_set_eq; split; intros.
      inversion H0; trivial.
      apply In_inter; auto.
    Qed.
    
  End INTESECTION.

  Section DIFFERENCE.

    Inductive Differ (E F : U_set) : U_set :=
      In_differ : forall x : U, E x -> ~ F x -> Differ E F x.

    Lemma Differ_E_F :
      forall E : U_set, Differ E E = Empty.
    Proof.
      intros; apply U_set_eq; split; intros.
      inversion H; congruence.
      inversion H.
    Qed.

    Lemma Differ_empty : forall E : U_set, Differ E Empty = E.
    Proof.
      intros; apply U_set_eq; split; intros.
      inversion H; trivial.
      apply In_differ; trivial.
      unfold not; intros; inversion H0.
    Qed.

    Lemma Union_differ_inter :
      forall E F : U_set,
        (forall x : U, {F x} + {~F x}) -> Union (Differ E F) (Inter E F) = E.
    Proof.
      intros; apply U_set_eq; split; intros.
      inversion H0.
      inversion H1; trivial.
      inversion H1; trivial.

      case (H x); intros.
      apply In_right; apply In_inter; trivial.
      
      apply In_left; apply In_differ; trivial.
    Qed.
    
  End DIFFERENCE.

  Section MIXED_PROPERTIES.

    Lemma Distributivity_inter_union :
      forall E F G : U_set, Inter E (Union F G) = Union (Inter E F) (Inter E G).
    Proof.
      intros; apply U_set_eq; split; intros.
      inversion H; inversion H1.
      apply In_left; apply In_inter; auto.
      apply In_right; apply In_inter; auto.

      inversion H; inversion H0.
      apply In_inter; auto.
      apply In_left; auto.

      apply In_inter; auto.
      apply In_right; auto.
    Qed.

    Lemma Distributivity_union_inter :
      forall E F G : U_set, Union E (Inter F G) = Inter (Union E F) (Union E G).
    Proof.
      intros; apply U_set_eq; split; intros.
      inversion H.
      apply In_inter; apply In_left; auto.
      inversion H0; apply In_inter; apply In_right; auto.

      inversion H.
      inversion H0.

      apply In_left; auto.

      inversion H1.
      apply In_left; trivial.

      apply In_right; apply In_inter; trivial.
    Qed.

    Lemma Union_inversion :
      forall E F G : U_set,
        Inter E F = Empty -> Inter E G = Empty -> Union E F = Union E G -> F = G.
    Proof.
        intros; apply U_set_eq; split; intros.
        generalize (In_right E F x H2).
        rewrite H1; intros.
        inversion H3.
        absurd (Inter E F x).
        rewrite H; tauto.

        apply In_inter; auto.

        trivial.

        generalize (In_right E G x H2).
        rewrite <- H1; intros.
        inversion H3.
        absurd (Inter E G x).
        rewrite H0; tauto.

        apply In_inter; auto.

        trivial.
    Qed.

    Lemma Union_inversion2 :
      forall E F G H : U_set,
        Inter E F = Empty ->
        Inter E G = Empty ->
        Inter G H = Empty -> Union E F = Union G H -> F = Union G (Inter F H).
    Proof.
        intros; apply U_set_eq; split; intros.
        generalize (In_right E F x H4).
        rewrite H3; intros.
        inversion H5.
        apply In_left; trivial.

        apply In_right; apply In_inter; trivial.

        inversion H4.
        generalize (In_left G H x H5).
        rewrite <- H3; intros.
        inversion H7.
        absurd (Inter E G x).
        rewrite H1; tauto.

        apply In_inter; trivial.

        trivial.

        inversion H5; trivial.
    Qed.

    Lemma Single_disjoint :
      forall (x : U) (E : U_set), ~ E x -> Inter (Single x) E = Empty.
    Proof.
        intros; apply U_set_eq; split; intros.
        inversion H0.
        inversion H1; absurd (E x).
        trivial.

        rewrite H4; trivial.

        inversion H0.
    Qed.

    Lemma Single_single_disjoint :
      forall x y : U, x <> y -> Inter (Single x) (Single y) = Empty.
    Proof.
        intros; apply Single_disjoint.
        red; intros H0; elim H; inversion H0; trivial.
    Qed.

    Lemma Union_single_single :
      forall (e : U_set) (x y : U),
        x <> y ->
        ~ e y -> Union (Single x) (Single y) = Union (Single y) e -> e = Single x.
    Proof.
        intros; symmetry ; apply (Union_inversion (Single y)).
        apply Single_single_disjoint; auto.

        apply Single_disjoint; trivial.

        rewrite Union_commut; trivial.
    Qed.

  End MIXED_PROPERTIES.

End U_SETS.
