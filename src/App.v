Require Import String.
Require Import List.

Import ListNotations.
Open Scope string_scope.

Require Import Html.

Module App.

Record Person := mkPerson { first_name : string; last_name : string }.

Definition model := Person.
   
Inductive event :=
  | TweakName : event
  | Noop : event.

Definition init (_ : unit) : model :=
  {| first_name := "John";
     last_name := "Smith"
  |}.

Definition view (m : model) : html event :=
  el "div"
    [ el_attr "h2" [ "style"=:"color: red;" ] [ text "Hello world!!!!!" ]
    ; el_attr "p" [ "style"=:"font-size: 300%;" ] [ text ("Hello, " ++ m.(first_name) ++ "!") ]
    ; el "p" [ text ("Hello again, " ++ m.(last_name)) ]
    ; el "strong" [ text "lol" ]
    ; el "p"
      [ el_attr "button" [ on "click" TweakName ] [ text "Change" ] ]
    ].

Notation "r '.{|' 'first_name' ':=' x '|}'" := (match r with mkPerson _ last_name => mkPerson x last_name end) (at level 50).

Definition update (m : model) (msg : event) : model :=
  match msg with
  | TweakName =>
      let new_name := if string_dec m.(first_name) "John" then "Alice" else "John"
      in m .{| first_name := new_name |}
  | Noop => m
  end.

End App.
