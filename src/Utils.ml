let destruct_list nil cons l =
    match l with
    | [] -> nil ()
    | x :: xs -> cons x xs
    ;;

let camlstring_of_coqstring (s: char list) =
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)

let coqstring_of_camlstring s =
  let rec cstring accu pos =
    if pos < 0 then accu else cstring (s.[pos] :: accu) (pos - 1)
  in cstring [] (String.length s - 1)

let vdom_attr (k, v) = Vdom.Attribute ("", camlstring_of_coqstring k, camlstring_of_coqstring v)

let vdom_prop (k, v) = Vdom.RawProp (camlstring_of_coqstring k, camlstring_of_coqstring v)

let vdom_event (name, prevent_default, stop_propagation, decoder) =
  Tea_html.onWithOptions
    (camlstring_of_coqstring name)
    { stopPropagation = stop_propagation; preventDefault = prevent_default }
    decoder

let vdom_elem (tag, attrs, children) = Vdom.node
     (camlstring_of_coqstring tag)
     attrs
     children

let vdom_text t = Vdom.text (camlstring_of_coqstring t)

type 'a decoder = (unit, 'a) Tea_json.Decoder.t

let decoder_map (f, x) = Tea_json.Decoder.map f x

let targetValue = Tea_json.Decoder.map coqstring_of_camlstring Tea_html.targetValue
let targetChecked = Tea_html.targetChecked
