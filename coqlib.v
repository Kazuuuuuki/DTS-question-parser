(* Basic types *)
Parameter Event : Type.

Implicit Arguments ex [].
Implicit Arguments sig [].
Inductive Entity : Type := | _John | _Susan | _Lucy.
Parameter pi : Type.
Parameter _student : Entity -> Prop.
Parameter _run : Entity -> Prop.
Axiom John_is_student: _student(_John).
Axiom Susan_is_student: _student(_Susan).
Axiom Lucy_is_not_student: (_student(_Lucy) -> False).
(*
Parameter _John : Type.
Parameter _Susan : Type.
Parameter _Lucy : Type.
Parameter _student : Entity -> Prop.
*)
(* Preliminary tactics *)

Ltac apply_ent :=
  match goal with
    | [x : Entity, H : forall x : Entity, _ |- _]
     => apply H; clear H
  end.

Ltac eqlem_sub :=
  match goal with
    | [ H1: ?A ?t, H2: forall x, @?D x -> @?C x |- _ ]
     => match D with context[ A ]
         => assert(C t); try (apply H2 with (x:= t)); clear H2
    end
  end.

Ltac exchange :=
  match goal with
    | [H1 : forall x, _, H2 : forall x, _ |- _]
     => generalize dependent H2
  end.

Ltac exchange_equality :=
  match goal with
    | [H1 : _ = _, H2: _ =  _ |- _]
     => generalize dependent H2
  end.

Ltac clear_pred :=
  match goal with
    | [H1 : ?F ?t, H2 : ?F ?u |- _ ]
     => clear H2
  end.

Ltac solve_false :=
  match goal with
    | [H : _ -> False |- False]
     => apply H
  end.


Ltac induction_entity_intransitive :=
  match goal with
    | [H0: _ , H1: _, x: Entity|- ?F _ \/  (?F _ -> False) ]
     => induction x
  end.

Ltac induction_entity_transitive :=
  match goal with
    | [H0: _ , H1: _, x: Entity|- ?F _ _ \/  (?F _ _ -> False) ]
     => induction x
  end.

Ltac induction_entity_intransitive_double_negation :=
  match goal with
    | [H0: _ , H1: _, x: Entity|- (?F _ -> False) \/  ((?F _ -> False) -> False) ]
     => induction x
  end.


Ltac solve_exh_left_intransitive :=
  match goal with
    | [ H : forall x : Entity, ?F x -> ?y = x, H1 : ?F ?y |- ?F ?y \/  (?F ?y -> False)]
    => try(left;trivial)
  end.


Ltac solve_exh_left_transitive :=
  match goal with
    | [ H : forall x : Entity, ?F x _ -> ?y = x, H1 : ?F ?y _ |- ?F ?y _ \/  (?F ?y _ -> False)]
    => try(left;trivial)
  end.

Ltac solve_exh_left_intransitive_double_negation :=
  match goal with
    | [ H : forall x : Entity, ?F x -> _ = x, H1 : ?F _ |- (?F ?y -> False) \/  ((?F ?y -> False)-> False)]
    => try(left; intro H2; apply H in H2; inversion H2)
  end.

Ltac solve_exh_left_intransitive_negation_to_double_negation :=
  match goal with
    | [ H : forall x : Entity, ((?F x) -> False) -> ?y = x, H1 : (?F ?y -> False) |- (?F ?y -> False) \/  ((?F ?y -> False)-> False)]
    => try(left; trivial)
  end.


Ltac solve_exh_right_intransitive :=
  match goal with
    | [ H : forall x : Entity, ?F x -> _ = x, H1 : ?F _ |- ?F _ \/  (?F _ -> False)]
    => try(right; intro H2; apply H in H2; inversion H2)
  end.

Ltac solve_exh_right_transitive :=
  match goal with
    | [ H : forall x : Entity, ?F x _ -> _ = x, H1 : ?F _ _ |- ?F _ _ \/  (?F _ _ -> False)]
    => try(right; intro H2; apply H in H2; inversion H2)
  end.

Ltac solve_exh_right_intransitive_double_negation :=
  match goal with
    | [ H : forall x : Entity, ?F x -> ?y = x, H1 : ?F ?y |- (?F ?y -> False) \/  ((?F ?y -> False)-> False)]
    => try(right;intro H2;apply H2 in H1; trivial)
  end.

Ltac solve_exh_right_intransitive_negation_to_double_negation :=
  match goal with
    | [ H0 : forall x : Entity, ((?F x) -> False) -> _ = x, H1 : ((?F _) -> False) |- (?F ?y -> False) \/  ((?F ?y -> False)-> False)]
    => try(right;intro H2; apply H0 in H2; inversion H2)
  end.

Ltac solve_exh_intransitive :=
  repeat ( try (solve_exh_left_intransitive);
           try (solve_exh_right_intransitive)).

Ltac solve_exh_transitive :=
  repeat ( try (solve_exh_left_transitive);
           try (solve_exh_right_transitive)).

Ltac solve_exh_intransitive_double_negation :=
  repeat ( try (solve_exh_right_intransitive_double_negation);
           try (solve_exh_left_intransitive_double_negation);
           try (solve_exh_left_intransitive_negation_to_double_negation);
           try (solve_exh_right_intransitive_negation_to_double_negation)).

Ltac solve_exh_john_is_student :=
  match goal with
    | [ H0 : forall x : Entity, _student x -> _  x |- (?F _John) \/ (?F _John -> False)]
    => try(specialize (H0 _John); specialize (H0 John_is_student); left; trivial)
  end.

Ltac solve_exh_susan_is_student :=
  match goal with
    | [ H0 : forall x : Entity, _student x -> _ x |- (?F _Susan) \/ (?F _Susan -> False)]
    => try(specialize (H0 _Susan); specialize (H0 Susan_is_student); left; trivial)
  end.

Ltac solve_exh_exists_student :=
  match goal with
    | [ H : forall x : Entity, _student x -> _ x |- exists y : Entity, _ y]
    => try(specialize (H _Susan); specialize (H Susan_is_student); exists _Susan; trivial)
  end.

(* Main tactics *)

Ltac nltac_init :=
  try(
      intuition;
      try solve_false;
      firstorder;
      repeat subst;
      firstorder
      ).

Ltac nltac_base :=
  try (eauto; eexists; firstorder);
  try (subst; eauto; firstorder; try congruence).

(*
Ltac nltac_axiom :=
 try first
   [solve_veridical_true |
    solve_antiveridical_false |
    solve_implicative_manage |
    solve_implicative_fail |
    solve_factive |
    solve_privative_former |
    solve_privative_fake
   ].
*)

Ltac nltac_set :=
          nltac_init;
          try (induction_entity_intransitive; solve_exh_intransitive; solve_exh_intransitive; solve_exh_intransitive);
          try (solve_exh_transitive; solve_exh_transitive; solve_exh_transitive);
          try (induction_entity_intransitive_double_negation; solve_exh_intransitive_double_negation; solve_exh_intransitive_double_negation; solve_exh_intransitive_double_negation);
          try (solve_exh_exists_student);
          try (solve_exh_john_is_student; solve_exh_susan_is_student);
          try exchange_equality;
          try eqlem_sub.

Ltac nltac_set_exch :=
          nltac_init;
          try apply_ent;
          try exchange;
          try eqlem_sub.

Ltac nltac_final :=
  try solve [repeat nltac_base | clear_pred; repeat nltac_base].

Ltac nltac :=
  try solve
    [nltac_set;  nltac_final].





