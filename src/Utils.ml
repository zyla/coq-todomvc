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
