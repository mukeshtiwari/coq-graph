Require Export Enumerated.

Section VERTEX.

  Inductive Vertex : Set :=
    Index : nat -> Vertex.

  Lemma V_eq_dec :
    forall x y : Vertex, {x = y} + {x <> y}.
  Proof.
    simple destruct x; simple destruct y; intros.
    case (eq_nat_dec n n0); intros.
    left; apply f_equal; trivial.
    right; injection; trivial.
  Qed.

  Definition V_list := list Vertex.
  Definition V_nil := nil(A := Vertex).
  Definition V_In_dec := U_in_dec Vertex V_eq_dec.
  Definition V_canon := U_canon Vertex.
  Definition V_sum := U_sum Vertex.
  Definition V_set := U_set Vertex.
  Definition V_set_eq := U_set_eq Vertex.
  Definition V_set_diff := U_set_diff Vertex.
  Definition V_eq_set := U_eq_set Vertex.
  Definition V_set_eq_commut := U_set_eq_commute Vertex.
  Definition V_set_diff_commut := U_set_diff_commute Vertex.
  Definition V_empty := Empty Vertex.
  Definition V_empty_nothing := Empty_nothing Vertex.
  Definition V_single := Single Vertex.
  Definition V_in_single := In_single Vertex.
  Definition V_single_equal := single_equal Vertex.
  Definition V_single_equal_single := Single_equal_single Vertex.
  Definition V_included := Included Vertex.
  Definition V_included_single := Included_single Vertex.
  Definition V_enumerable := U_enumerable Vertex.
  Definition V_enumerable_sum := U_enumerable_sum Vertex.
  Definition V_union := Union Vertex.
  Definition V_in_left := In_left Vertex.
  Definition V_in_right := In_right Vertex.
  Definition V_union_eq := Union_eq Vertex.
  Definition V_union_neutral := Union_neutral Vertex.
  Definition V_union_commut := Union_commut Vertex.
  Definition V_union_assoc := Union_assoc Vertex.
  Definition V_not_union := Not_union Vertex.
  Definition V_union_dec := Union_dec Vertex.
  Definition V_included_union := Included_union Vertex.
  Definition V_union_absorb := Union_absorb Vertex.
  Definition V_inter := Inter Vertex.
  Definition V_in_inter := In_inter Vertex.
  Definition V_inter_eq := Inter_eq Vertex.
  Definition V_inter_neutral := Inter_neutral Vertex.
  Definition V_inter_empty := Inter_empty Vertex.
  Definition V_inter_commut := Inter_commute Vertex.
  Definition V_inter_assoc := Inter_assoc Vertex.
  Definition V_not_inter := Not_inter Vertex.
  Definition V_included_inter := Included_inter Vertex.
  Definition V_inter_absorb := Inter_absorb Vertex.
  Definition V_differ := Differ Vertex.
  Definition V_differ_E_E := Differ_E_E Vertex.
  Definition V_differ_empty := Differ_empty Vertex.
  Definition V_union_differ_inter := Union_differ_inter Vertex.
  Definition V_distributivity_inter_union := Distributivity_inter_union Vertex.
  Definition V_distributivity_union_inter := Distributivity_union_inter Vertex.
  Definition V_union_inversion := Union_inversion Vertex.
  Definition V_union_inversion2 := Union_inversion2 Vertex.
  Definition V_single_disjoint := Single_disjoint Vertex.
  Definition V_single_single_disjoint := Single_single_disjoint Vertex.
  Definition V_union_single_single := Union_single_single Vertex.

End VERTEX.
