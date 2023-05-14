Require Import String.
Require Import DecimalString.
Require Import List.

Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Require Import Html.

Module App.

Record Task := mkTask { description : string; completed : bool }.

Module Task.
  Definition toggle (t : Task) : Task :=
    match t with mkTask d completed => mkTask d (negb completed) end.
End Task.

Definition Model := nat.

Module Model.
  Definition t := Model.
End Model.

Inductive event :=
  | Increment : event
  | Decrement : event.

Definition init (_ : unit) : Model.t := 0.


Definition update (m : Model.t) (msg : event) : Model.t :=
  match msg with
  | Increment => m + 1
  | Decrement => m - 1
  end.

Definition view (m : Model.t) : html event :=
  el_attr "div"
    []
    [ text "test"
    ].

End App.

