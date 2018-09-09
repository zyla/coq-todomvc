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

  Inductive html (A : Set) : Set :=
    | Elem : string -> list (string * string) -> list (html A) -> html A
    | Text : string -> html A.

  Definition el_attr : forall {A}, string -> list (string * string) -> list (html A) -> html A
    := Elem.
  Definition text : forall {A}, string -> html A := Text.
  Definition el {A} : tag_name -> list (html A) -> html A :=
    fun tag => el_attr tag [].
  Definition el_ {A} : tag_name -> html A :=
    fun tag => el_attr tag [] [].
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
  | SetFirstName : string -> event.

Definition init (_ : unit) : model :=
  {# _first_name :- "John"
   ; _last_name :- "Smith"
   #}.

Definition view (m : model) : html event :=
  el "div"
    [ el_attr "h2" [ ("style", "color: red;") ] [ text "Hello world!!!!!" ]
    ; el_attr "p" [ ("style", "font-size: 300%;") ] [ text ("Hello, " ++ (m !! _first_name) ++ "!") ]
    ; el "p" [ text ("Hello again, " ++ (m !! _last_name)) ]
    ; el "strong" [ text "lol" ]
    ].

Definition update (m : model) (msg : event) : model :=
  match msg with
  | SetFirstName x => {# m with _first_name :- x #}
  end.

End App.

Extract Inductive Html.html => "Vdom.t" [
  (* Elem *)
  "(fun (tag, attrs, children) -> Vdom.node
     (Utils.camlstring_of_coqstring tag)
     (List.map
       (function (k, v) -> Vdom.Attribute ("""", Utils.camlstring_of_coqstring k, Utils.camlstring_of_coqstring v))
       attrs)
     children)"
  (* Text *)
  "(fun t -> Vdom.text (Utils.camlstring_of_coqstring t))"
  ].

Extraction "src/app.ml" App.
