Require Import String.
Require Import List.

Import ListNotations.

Definition tag_name := string.

Inductive prop (A : Set) : Set :=
| Attr : string -> string -> prop A
| Event : string -> A -> prop A.

Arguments Attr {_}.

Inductive html (A : Set) : Set :=
| Elem : string -> list (prop A) -> list (html A) -> html A
| Text : string -> html A.

Definition el_attr : forall {A}, string -> list (prop A) -> list (html A) -> html A
:= Elem.
Definition text : forall {A}, string -> html A := Text.
Definition el {A} : tag_name -> list (html A) -> html A :=
fun tag => el_attr tag [].
Definition el_ {A} : tag_name -> html A :=
fun tag => el_attr tag [] [].

Notation "k =: v" := (Attr k v) (at level 75).

Definition on : forall {A : Set}, string -> A -> prop A := Event.
