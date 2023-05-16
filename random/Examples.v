
Definition key := nat.

Inductive map (V : Set) :=
  | Branch : key -> V -> map V -> map V -> map V
  | Leaf : map V.

Arguments Branch {_}.
Arguments Leaf {_}.

Definition is_empty {V} (m : map V) : bool :=
  match m with
  | Branch _ _ _ _ => false
  | Leaf => true
  end.

Fixpoint size {V} (m : map V) : nat :=
  match m with
  | Branch _ _ l r => 1 + size l + size r
  | Leaf => 0
  end.