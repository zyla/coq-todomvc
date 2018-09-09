(* Web app writen in Coq *)
(* Compiled to JS via BuckleScript *)

Require Import String List.
Require Import Extraction.
Import ListNotations.
Local Open Scope string_scope.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Module Html.
  Definition tag_name := string.
  Parameter html : Set -> Set.
  Parameter el_attr : forall {A}, string -> list (string * string) -> list (html A) -> html A.
  Parameter text : forall {A}, string -> html A.
  Definition el {A} : tag_name -> list (html A) -> html A :=
    fun tag => el_attr tag [].
  Definition el_ {A} : tag_name -> html A :=
    fun tag => el tag nil.
End Html.

(* App *)

Module App.

Import Html.
Definition model := string.
Inductive event := Dummy1 : event | Dummy2 : event.

Definition init (_ : unit) : model := "John Smith".

Definition view (name : model) : html event :=
  el "div"
    [ el_attr "h2" [ ("style", "color: red;") ] [ text "Hello world!!!!!" ]
    ; el_attr "p" [ ("style", "font-size: 300%;") ] [ text ("Hello, " ++ name ++ "!") ]
    ; el "p" [ text ("Hello again, " ++ name) ]
    ; el "strong" [ text "lol" ]
    ].

Definition update (m : model) (msg : event) : model :=
  m.

End App.

Extract Constant Html.html "'a" => "'a Vdom.t".
Extract Constant Html.el_attr =>
  "(fun tag attrs -> Vdom.node (Utils.camlstring_of_coqstring tag)
     (List.map
       (function (k, v) -> Vdom.Attribute ("""", Utils.camlstring_of_coqstring k, Utils.camlstring_of_coqstring v))
       attrs))".
Extract Constant Html.text => "(fun t -> Vdom.text (Utils.camlstring_of_coqstring t))".


Extraction "src/app.ml" App.



(*

Definition apply {A B} (f : A -> B) (x : A) : B := f x.
Notation "f $ x" := (apply f x) (at level 90, right associativity).

*)