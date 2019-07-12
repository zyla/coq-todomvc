Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Require Html.

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
