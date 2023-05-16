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
    ; el "button"
        [ on "click" Increment ]
        [ text "+" ]
    ].

End App.

Module Proofs.

Import App.

Theorem can_always_increment : forall m, Html.msg_possible Increment (view m).
  intros.
  find_msg auto.
Qed.

Theorem can_go_to_5 : reachable (fun m => m = 5) (init tt) update view.
Proof.
  do 5 (apply (R_Step update view Increment); simpl; try (find_msg auto)).
  apply R_Here.
  reflexivity.
Qed.

Theorem can_go_to_any_number : forall n, Html.reachable (fun m => m = n) (init tt) update view.
Proof.
  assert (can_go_from_k : forall n k, Html.reachable (fun m => m = n + k) k update view).
  intros n.
  induction n; intro k.

  apply R_Here. reflexivity.

  apply (R_Step update view Increment); try (find_msg auto). simpl.
  rewrite <- PeanoNat.Nat.add_succ_r.
  rewrite PeanoNat.Nat.add_1_r.
  apply (IHn (S k)).

  intro n.
  rewrite <- (Nat.add_0_r n).
  apply (can_go_from_k n 0).
Qed.

End Proofs.
