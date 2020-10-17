Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Require Html.

Extract Inductive Html.prop => "Vdom.property" [
  (* attr *)
  "Utils.vdom_attr"
  (* Event *)
  "Utils.vdom_event"
].

Extract Inductive Html.html => "Vdom.t" [
  (* Elem *)
  "Utils.vdom_elem"
  (* Text *)
  "Utils.vdom_text"
  ].
