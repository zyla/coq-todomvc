Require Import String.
Require Import DecimalString.
Require Import List.

Import ListNotations.
Open Scope string_scope.

Require Import Html.

Module App.

Record Task := mkTask { description : string; completed : bool }.

Module Task.
  Definition toggle (t : Task) : Task :=
    match t with mkTask d completed => mkTask d (negb completed) end.
End Task.

Record Model := mkModel
  { tasks : list Task
  }.

Module Model.
  Definition t := Model.
  Definition over_tasks (f : list Task -> list Task) (r : t) : t :=
    match r with mkModel x => mkModel (f x) end.
End Model.

Inductive TaskAction :=
  | Toggle : TaskAction
  | Delete : TaskAction.

Inductive event :=
  | TaskAction_ : nat -> TaskAction -> event
  | ClearCompleted : event.

Definition init (_ : unit) : Model.t :=
  {| tasks :=
       [ {| description := "Prove this app";
            completed := false
         |}
       ; {| description := "Buy a unicorn";
            completed := true
         |}
       ]
  |}.

Definition string_of_nat (n : nat) : string := NilZero.string_of_uint (Nat.to_uint n).

Definition map_with_index {A B: Type} (f : nat -> A -> B) : list A -> list B :=
  let fix go i l :=
    match l with
    | [] => []
    | x :: xs => f i x :: go (1 + i) xs
    end
  in go 0.

Fixpoint update_at {A} (index : nat) (f : A -> A) (l : list A) : list A :=
  match index, l with
  | _, [] => []
  | 0, x :: xs => f x :: xs
  | S i, x :: xs => x :: update_at i f xs
  end.

Fixpoint delete_at {A} (index : nat) (l : list A) : list A :=
  match index, l with
  | _, [] => []
  | 0, x :: xs => xs
  | S i, x :: xs => x :: delete_at i xs
  end.

Definition num_incomplete m := length (filter (fun t => negb t.(completed)) m.(tasks)).

Definition update (m : Model.t) (msg : event) : Model.t :=
  match msg with
  | TaskAction_ index Toggle => Model.over_tasks (update_at index Task.toggle) m
  | TaskAction_ index Delete => Model.over_tasks (delete_at index) m
  | ClearCompleted => 
      Model.over_tasks (filter (fun t => negb t.(completed))) m
  end.

Definition pluralize (n : nat) (singular : string) (plural : string) :=
  match n with
  | 1 => singular
  | _ => plural
  end.

Definition view (m : Model.t) : html event :=
  el_attr "section"
    [ "class"=:"todoapp" ]
    [ el_attr "header"
        [ "class"=:"header" ]
        [ el "h1" [ text "todos" ]
        ; el_attr "input"
                  [ "class"=:"new-todo"
                  ; "placeholder"=:"What needs to be done?"
                  ; "autofocus" =: "" ]
                  []
        ]
    ; el_attr "section"
        [ "class"=:"main" ]
        [ el_attr "input"
            ["type"=:"checkbox"; "id"=:"toggle-all"; "class"=:"toggle-all" ] []
        ; el_attr "label" [ "for"=:"toggle-all" ]
            [ text "Mark all as complete" ]
        ; el_attr "ul" [ "class"=:"todo-list" ]
            (map_with_index
            (fun index task =>
                 el_attr "li"
                         (if task.(completed) then [ "class"=:"completed" ] else [])
                         [ el_attr "div" [ "class"=:"view" ]
                                   [ el_attr "input"
                                             ([ "type" =: "checkbox"
                                              ; "class"=:"toggle"
                                              ; on "change" (TaskAction_ index Toggle)
                                              ] ++
                                        (if task.(completed) then ["checked"=:""] else [])) []
                                   ; el "label" [ text task.(description) ]
                                   ; el_attr "button"
                                             [ "class"=:"destroy"
                                             ; on "click" (TaskAction_ index Delete) 
                                             ] []
                                   ]
                         ; el_attr "input" ["class"=:"edit"] []
                         ]
            )
            m.(tasks))
        ]
    ; el_attr "footer" [ "class"=:"footer" ]
        [ let n := num_incomplete m in
          el_attr "span" [ "class"=:"todo-count" ]
            [ el "strong" [ text (string_of_nat n) ]
            ; text (" " ++ pluralize n "item" "items" ++ " left")
            ]
          ; el_attr "button" [ "class"=:"clear-completed"; on "click" ClearCompleted ]
                    [ text "Clear completed" ]
        ]
    ].

(* TODO: implement filters

				<!-- Remove this if you don't implement routing -->
				<ul class="filters">
					<li>
						<a class="selected" href="#/">All</a>
					</li>
					<li>
						<a href="#/active">Active</a>
					</li>
					<li>
						<a href="#/completed">Completed</a>
					</li>
				</ul>
*)

End App.
