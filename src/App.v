Require Import String.
Require Import List.
Require Import Records.Records.

Import ListNotations.
Open Scope string_scope.
Open Scope record.

Require Import Html.

Module App.

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
