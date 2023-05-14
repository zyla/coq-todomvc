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

Definition el_attr : forall {A}, string -> list (hprop A) -> list (html A) -> html A
:= Elem.
Definition text : forall {A}, string -> html A := Text.
Definition el {A} : tag_name -> list (html A) -> html A :=
fun tag => el_attr tag [].
Definition el_ {A} : tag_name -> html A :=
fun tag => el_attr tag [] [].

Notation "k =: v" := (Attr k v) (at level 75).

Definition prop {A} := RawProp A.

Definition on_with_opts {A : Set} (ev : string) (opts : event_opts) : decoder A -> hprop A :=
  Event ev opts.(prevent_default) opts.(stop_propagation).

Definition on {A : Set} (ev  : string) (msg : A) : hprop A := on_with_opts ev default_options (Decoder.pure msg).

Search list.


(* Proof tools *)

Fixpoint any {A : Type} (p: A -> Prop) (xs: list A) : Prop :=
  match xs with
  | [] => True
  | x :: xs => p x \/ any p xs
  end.

Definition event_possible_from_prop {A : Set} (x : A) (p: hprop A) : Prop :=
  match p with
  | Event _ _ _ decoder =>
      Decoder.value_possible x decoder
  | _ => False
  end.

(*
Fixpoint event_possible {A: Set} (x : A) (h: html A) {struct h} : Prop :=
  match h with
  | Elem _ _ props children =>
    any (event_possible_from_prop x) props
    \/ event_possible_list x children
  | Text _ _ => False
  end
with event_possible_list {A: Set} (x : A) (hs: list (html A)) {struct hs} : Prop :=
  match hs with
  | [] => True
  | h :: rest => event_possible x h \/ event_possible_list x rest
  end.
*)

Inductive event_possible {A: Set} (x : A) : html A -> Prop :=
  | EP_Prop : forall tag props children,
      any (event_possible_from_prop x) props -> event_possible x (Elem A tag props children)
  | EP_Children : forall tag props children,
      event_possible_list x children -> event_possible x (Elem A tag props children)
with event_possible_list {A: Set} (x : A) : list (html A) -> Prop :=
  | EP_Here : forall h rest, event_possible x h -> event_possible_list x (h :: rest)
  | EP_Next : forall h rest, event_possible_list x rest -> event_possible_list x (h :: rest).