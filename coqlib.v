(* Basic types *)
Parameter Entity : Type.
Parameter Event : Type.

Implicit Arguments ex [].
Implicit Arguments sig [].

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

(* Main tactics *)

Ltac nltac_init :=
  try(intuition;
      try solve_false;
      firstorder;
      repeat subst;
      firstorder).

Ltac nltac_base := 
  try nltac_init;
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
    [nltac_set; nltac_final].

