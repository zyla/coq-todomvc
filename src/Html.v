Require Import String.
Require Import List.

Import ListNotations.

Definition tag_name := string.

Record event_opts :=
  mk_event_opts {
      stop_propagation: bool;
      prevent_default: bool
  }.

Definition default_options :=
  {| stop_propagation := false; prevent_default := false |}.

Definition prevent_default_opts :=
  {| stop_propagation := false; prevent_default := true |}.

Module Decoder.

Inductive t : Set -> Type :=
  | targetValue : t string
  | targetChecked : t bool
  | pure : forall {A : Set}, A -> t A
  | map : forall {A B : Set}, (A -> B) -> t A -> t B.

Definition heq {A B : Set} (p: A = B) (x: A) (y: B): Prop.
  rewrite p in *.
  exact (x = y).
Defined.

Print heq.

Fixpoint value_possible {A: Set} (x: A) (d: t A) : Prop :=
  match d in t T return A = T -> Prop with
  | targetValue => fun _ => True
  | targetChecked => fun _ => True
  | pure y => fun prf => heq prf x y
  | map f d2 => fun prf => forall y, value_possible y d2 /\ heq prf x (f y)
  end eq_refl .

End Decoder.

Definition decoder := Decoder.t.

Inductive hprop (A : Set) : Type :=
  | Attr : string -> string -> hprop A
  | RawProp : string -> string -> hprop A
  | Event : string -> bool -> bool -> decoder A -> hprop A.

Arguments Attr {_}.
Arguments Event {_}.

Inductive html (A : Set) : Type :=
| Elem : string -> list (hprop A) -> list (html A) -> html A
| Text : string -> html A.

Definition el : forall {A}, string -> list (hprop A) -> list (html A) -> html A
:= Elem.
Definition text : forall {A}, string -> html A := Text.
Definition el_ {A} : tag_name -> list (html A) -> html A := fun tag => el tag [].

Notation "k =: v" := (Attr k v) (at level 75).

Definition prop {A} := RawProp A.

Definition on_with_opts {A : Set} (ev : string) (opts : event_opts) : decoder A -> hprop A :=
  Event ev opts.(prevent_default) opts.(stop_propagation).

Definition on {A : Set} (ev  : string) (msg : A) : hprop A := on_with_opts ev default_options (Decoder.pure msg).

Search list.


(* Proof tools *)

Fixpoint any {A : Type} (p: A -> Prop) (xs: list A) : Prop :=
  match xs with
  | [] => False
  | x :: xs => p x \/ any p xs
  end.

Definition msg_possible_from_prop {A : Set} (x : A) (p: hprop A) : Prop :=
  match p with
  | Event _ _ _ decoder =>
      Decoder.value_possible x decoder
  | _ => False
  end.

Inductive msg_possible {A: Set} (x : A) : html A -> Prop :=
  | EP_Prop : forall tag props children,
      any (msg_possible_from_prop x) props -> msg_possible x (Elem A tag props children)
  | EP_Children : forall tag props children,
      msg_possible_list x children -> msg_possible x (Elem A tag props children)
with msg_possible_list {A: Set} (x : A) : list (html A) -> Prop :=
  | EP_Here : forall h rest, msg_possible x h -> msg_possible_list x (h :: rest)
  | EP_Next : forall h rest, msg_possible_list x rest -> msg_possible_list x (h :: rest).

Inductive reachable {M E : Set} (P : M -> Prop) (from : M) (update : M -> E -> M) (view : M -> html E) : Prop :=
  | R_Here : P from -> reachable P from update view
  | R_Step : forall event,
      msg_possible event (view from) ->
      reachable P (update from event) update view ->
      reachable P from update view.

Arguments R_Step {_ _ _ _}.

Hint Unfold any el on on_with_opts Decoder.heq : core.

Ltac find_msg t :=
  simpl; solve
    [ apply EP_Prop; simpl; t
    | apply EP_Here; t; find_msg t
    | apply EP_Next; t; find_msg t
    | apply EP_Children; t; find_msg t ].


Definition always {M E : Set} (P : M -> Prop) (from : M) (update : M -> E -> M) (view : M -> html E) : Prop :=
  P from /\ (forall m msg, P m -> msg_possible msg (view m) -> P (update m msg)).

Theorem not_reachable_if_invariant_violated {M E : Set} (P : M -> Prop) (from : M) (update : M -> E -> M) (view : M -> html E) (P2 : M -> Prop) :
  always P from update view -> (forall m, P2 m -> ~ P m) -> ~ reachable P2 from update view.
Proof.
  intros Halways Hno_invariant.
  destruct Halways as [Hinitial Hstep].
  intro H.
  induction H.

  apply (Hno_invariant from H).
  assumption.

  apply IHreachable; try assumption.
  apply (Hstep from event Hinitial H).
 Qed.