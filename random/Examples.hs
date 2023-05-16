
type Key = Natural

data Map v
  = Branch Key v (Map v) (Map v)
  | Leaf

isEmpty :: Map v -> Bool
isEmpty m =
  case m of
    Branch _ _ _ _ -> False
    Leaf -> True

size :: Map v -> Natural
size m =
  case m of
    Branch _ _ l r -> 1 + size l + size r
    Leaf -> 0