Require Import String.
Require Import List.

Import ListNotations.
Open Scope string_scope.

Require Import Html.

Module App.

Record Task := mkTask { description : string; completed : bool }.

Record model := mkModel
                  { tasks : list Task
                  }.
   
Inductive event :=
  | TweakName : event
  | Noop : event.

Definition init (_ : unit) : model :=
  {| tasks :=
       [ {| description := "Prove this app";
            completed := false
         |}
       ; {| description := "Buy a unicorn";
            completed := true
         |}
       ]
  |}.

(* TODO: implement this *)
Definition string_of_nat (n : nat) : string := "0".

Definition view (m : model) : html event :=
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
                        (map
                        (fun task =>
                             el_attr "li"
                                     (if task.(completed) then [ "class"=:"completed" ] else [])
                                     [ el_attr "div" [ "class"=:"view" ]
                                               [ el_attr "input"
                                                         ([ "type" =: "checkbox"; "class"=:"toggle" ] ++
                                                                                                      (if task.(completed) then ["checked"=:""] else [])) []
                                               ; el "label" [ text task.(description) ]
                                               ; el_attr "button" [ "class"=:"destroy" ] []
                                               ]
                                     ; el_attr "input" ["class"=:"edit"] []
                                     ]
                        )
                        m.(tasks))
              ]
    ; el_attr "footer" [ "class"=:"footer" ]
              [ el_attr "span" [ "class"=:"todo-count" ]
                        [ el "strong" [ text (string_of_nat (length m.(tasks))) ]
                        ; text " item left"
                        ]
                ; el_attr "button" [ "class"=:"clear-completed" ]
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

Definition update (m : model) (msg : event) : model :=
  match msg with
  | TweakName => m
  | Noop => m
  end.

End App.
