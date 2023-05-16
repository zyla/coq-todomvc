Require Import String.
Require Import DecimalString.
Require Import List.
Require Import PeanoNat.

Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Require Import Html.

Module App.

Definition Model := nat.

Module Model.
  Definition t := Model.
End Model.

Inductive Msg :=
  | Increment : Msg
  | Decrement : Msg.

Definition init (_ : unit) : Model.t := 0.

Definition update (m : Model.t) (msg : Msg) : Model.t :=
  match msg with
  | Increment => m + 1
  | Decrement => m - 1
  end.

Definition string_of_nat (n : nat) : string := NilZero.string_of_uint (Nat.to_uint n).

Definition view (m : Model.t) : html Msg :=
  el "div"
    []
    [ el "button"
         [ on "click" Decrement ]
         [ text "-" ]
    ; el "span"
         [ "class"=:"count" ]
         [ text (string_of_nat m) ]
    ; if m <? 10 then
        el "button"
          [ on "click" Increment ]
          [ text "+" ]
      else
        text "can't increment"
    ].

End App.

Module Proofs.

Import App.

Theorem can_increment_if_below_limit : forall m, m < 10 -> Html.msg_possible Increment (view m).
  intros m Hm.
  unfold view.
  try rewrite (proj2 (Nat.ltb_lt m 10) Hm).
  find_msg auto.
Qed.

Lemma not_any_empty : forall {A} (P : A -> Prop), any P [] -> False.
Proof.
  auto.
Qed.

Ltac msg_impossible :=
  match goal with
  | H : any ?P [] |- False => apply (not_any_empty P); assumption
  | H : any (msg_possible_from_prop _) _ |- False => inversion H; clear H
  | H : msg_possible _ _ |- False => inversion H; clear H
  | H : msg_possible_list _ _ |- False => inversion H; clear H
  | H : msg_possible_from_prop _ _ |- False => inversion H; clear H
  end.

Theorem cant_increment_if_at_limit : ~ Html.msg_possible Increment (view 10).
  intros Hpossible.
  repeat msg_impossible.
Qed.

Theorem can_go_to_5 : reachable (fun m => m = 5) (init tt) update view.
Proof.
  do 5 (apply (R_Step update view Increment); simpl; try (find_msg auto)).
  apply R_Here.
  reflexivity.
Qed.


Theorem always_le_10 : always (fun m => m <= 10) (init tt) update view.
Proof.
  constructor.
  apply Nat.le_0_l.

  intros m msg Hlt10 Hpossible.
  destruct msg.
  destruct (Nat.eq_decidable m 10).
  exfalso.
  rewrite H in *.
  apply (cant_increment_if_at_limit Hpossible).
  inversion Hlt10.
  exfalso. auto.
  unfold update.
  rewrite Nat.add_1_r.
  Search le S.
  apply le_n_S.
  assumption.

  simpl.
  rewrite Nat.le_sub_le_add_r.
  simpl.
  auto.
Qed.

Theorem cant_go_to_15 : ~ reachable (fun m => m = 15) (init tt) update view.
Proof.
  apply (not_reachable_if_invariant_violated (fun m => m <= 10)).
  apply always_le_10.

  intros m Hm15. rewrite Hm15 in *.
  apply (proj1 (Nat.leb_nle 15 10)).
  reflexivity.
Qed.

End Proofs.
