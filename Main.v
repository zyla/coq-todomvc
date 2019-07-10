(* Web app writen in Coq *)
(* Compiled to JS via BuckleScript *)

Require Import String.
Require Import Extraction.
Require Import List.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Require Import Records.Records.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope record.


Module Html.
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

End Html.

(* App *)

Module App.

Import Html.

Definition _first_name := "first_name".
Definition _last_name := "last_name".

Definition model :=
  {@ _first_name %e string
   , _last_name %e string
   @}.
   
Inductive event :=
  | TweakName : event
  | Noop : event.

Definition init (_ : unit) : model :=
  {# _first_name :- "John"
   ; _last_name :- "Smith"
   #}.

Definition view (m : model) : html event :=
  el "div"
    [ el_attr "h2" [ "style"=:"color: red;" ] [ text "Hello world!!!!!" ]
    ; el_attr "p" [ "style"=:"font-size: 300%;" ] [ text ("Hello, " ++ (m !! _first_name) ++ "!") ]
    ; el "p" [ text ("Hello again, " ++ (m !! _last_name)) ]
    ; el "strong" [ text "lol" ]
    ; el "p"
      [ el_attr "button" [ on "click" TweakName ] [ text "Change" ] ]
    ].

Definition update (m : model) (msg : event) : model :=
  match msg with
  | TweakName =>
      let new_name := if string_dec (m !! _first_name) "John" then "Alice" else "John"
      in {# m with _first_name :- new_name #}
  | Noop => m
  end.

End App.

Extract Inductive Html.prop => "Vdom.property" [
  (* attr *)
  "(function (k, v) -> Vdom.Attribute ("""", Utils.camlstring_of_coqstring k, Utils.camlstring_of_coqstring v))"
  (* Event *)
  "(function (name, msg) -> Vdom.onMsg (Utils.camlstring_of_coqstring name) msg)"
].

Extract Inductive Html.html => "Vdom.t" [
  (* Elem *)
  "(fun (tag, attrs, children) -> Vdom.node
     (Utils.camlstring_of_coqstring tag)
     attrs
     children)"
  (* Text *)
  "(fun t -> Vdom.text (Utils.camlstring_of_coqstring t))"
  ].

Extraction "src/app.ml" App.
