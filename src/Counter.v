Require Import String.
Require Import DecimalString.
Require Import List.

Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Require Import Html.

Module App.

Record Task := mkTask { description : string; completed : bool }.

Module Task.
  Definition toggle (t : Task) : Task :=
    match t with mkTask d completed => mkTask d (negb completed) end.
End Task.

Definition Model := nat.

Module Model.
  Definition t := Model.
End Model.

Inductive event :=
  | Increment : event
  | Decrement : event.

Definition init (_ : unit) : Model.t := 0.

Definition update (m : Model.t) (msg : event) : Model.t :=
  match msg with
  | Increment => m + 1
  | Decrement => m - 1
  end.

Definition string_of_nat (n : nat) : string := NilZero.string_of_uint (Nat.to_uint n).

Definition view (m : Model.t) : html event :=
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

Hint Unfold any el on on_with_opts Decoder.heq : core.

Ltac find_event t :=
  simpl; solve
    [ apply EP_Prop; simpl; t
    | apply EP_Here; find_event t
    | apply EP_Next; find_event t
    | apply EP_Children; find_event t ].

Theorem can_always_increment : forall m, Html.event_possible Increment (view m).
  intro m.
  find_event auto.
Qed.

Theorem can_go_to_5 : Html.reachable (fun m => m = 5) (init tt) update view.
Proof.
  do 5 (apply (R_Step update view Increment); simpl; try (find_event auto)).
  apply R_Here.
  reflexivity.
Qed.

Lemma can_go_to_any_number : forall n k, Html.reachable (fun m => m = n + k) k update view.
Proof.
  intros n.
  induction n; intro k.

  apply R_Here. reflexivity.

  apply (R_Step update view Increment); try (find_event auto). simpl.
  rewrite <- PeanoNat.Nat.add_succ_r.
  rewrite PeanoNat.Nat.add_1_r.
  apply (IHn (S k)).
Qed.
  

End Proofs.