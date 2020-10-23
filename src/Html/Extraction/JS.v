Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Require Html.

Extract Inductive Html.Decoder.t => "Utils.decoder" [
  "Utils.targetValue"
  "Utils.targetChecked"
  "Tea_json.Decoder.succeed"
  "Utils.decoder_map"
].

Extract Inductive Html.hprop => "Vdom.property" [
  (* attr *)
  "Utils.vdom_attr"
  (* RawProp *)
  "Utils.vdom_prop"
  (* Event *)
  "Utils.vdom_event"
].

Extract Inductive Html.html => "Vdom.t" [
  (* Elem *)
  "Utils.vdom_elem"
  (* Text *)
  "Utils.vdom_text"
  ].
