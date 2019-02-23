(* Basic types *)
Parameter Event : Type.

Implicit Arguments ex [].
Implicit Arguments sig [].
Inductive Entity : Type := | _John | _Susan | _Lucy.
Parameter pi : Type.

(*
Parameter _John : Type.
Parameter _Susan : Type.
Parameter _Lucy : Type.
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

Ltac solve_exh_intransitive :=
  repeat ( try (solve_exh_left_intransitive);
           try (solve_exh_right_intransitive)).

Ltac solve_exh_transitive :=
  repeat ( try (solve_exh_left_transitive);
           try (solve_exh_right_transitive)).

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
  repeat (nltac_init;
          try (nltac_init;induction_entity_intransitive; solve_exh_intransitive; solve_exh_intransitive; solve_exh_intransitive);
          try (solve_exh_transitive; solve_exh_transitive; solve_exh_transitive);
          try exchange_equality;
          try eqlem_sub).

Ltac nltac_set_exch :=
  repeat (nltac_init;
          try apply_ent;
          try exchange;
          try eqlem_sub).

Ltac nltac_final :=
  try solve [repeat nltac_base | clear_pred; repeat nltac_base].

Ltac nltac :=
  try solve
    [nltac_set;  nltac_final].

Parameter _like : Entity -> (Entity -> Prop).
Parameter _run : Entity -> Prop.
Theorem t1: (and (forall y:Entity,((_run y) -> (_John = y))) (_run _John)) -> (forall x:Entity,(or (_run x) (not (_run x)))). nltac. Qed.