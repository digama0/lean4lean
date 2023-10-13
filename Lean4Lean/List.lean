
@[specialize] def List.all2 (R : α → α → Bool) : List α → List α → Bool
  | a1 :: as1, a2 :: as2 => R a1 a2 && all2 R as1 as2
  | [], [] => true
  | _, _ => false
