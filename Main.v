(* Web app writen in Coq *)
(* Compiled to JS via BuckleScript *)

Require Import String List.
Require Import Extraction.
Import ListNotations.
Local Open Scope string_scope.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Module Html.
  Parameter html : Set -> Set.
  Parameter el : forall {A}, string -> list (html A) -> html A.
  Parameter text : forall {A}, string -> html A.
  Definition el_ {A} tag : html A := el tag nil.
End Html.

(* App *)

Module App.

Import Html.
Definition model := string.
Inductive event := Dummy1 : event | Dummy2 : event.

Definition init (_ : unit) : model := "John Smith".

Definition view (name : model) : html event :=
  el "div"
    [ el "h2" [ text "Hello world!!!!!" ]
    ; el "p" [ text ("Hello, " ++ name ++ "!") ]
    ; el "p" [ text ("Hello again, " ++ name) ]
    ; el "strong" [ text "lol" ]
    ].

Definition update (m : model) (msg : event) : model :=
  m.

End App.

Extract Constant Html.html "'a" => "'a Vdom.t".
Extract Constant Html.el => "(fun tag -> Vdom.node (Utils.camlstring_of_coqstring tag) [])".
Extract Constant Html.text => "(fun t -> Vdom.text (Utils.camlstring_of_coqstring t))".


Extraction "src/app.ml" App.



(*

Definition apply {A B} (f : A -> B) (x : A) : B := f x.
Notation "f $ x" := (apply f x) (at level 90, right associativity).

*)