Require Import String.
Require Import List.

Import ListNotations.

Definition tag_name := string.

Record event_opts :=
  mk_event_opts {
      stop_hpropagation: bool;
      prevent_default: bool
  }.

Definition default_options :=
  {| stop_hpropagation := false; prevent_default := false |}.

Definition prevent_default_opts :=
  {| stop_hpropagation := false; prevent_default := true |}.

Module Decoder.

Inductive t : Set -> Type :=
  | targetValue : t string
  | targetChecked : t bool
  | pure : forall {A : Set}, A -> t A
  | map : forall {A B : Set}, (A -> B) -> t A -> t B.

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
  Event ev opts.(prevent_default) opts.(stop_hpropagation).

Definition on {A : Set} (ev  : string) (msg : A) : hprop A := on_with_opts ev default_options (Decoder.pure msg).