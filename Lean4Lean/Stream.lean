
structure NatStream where i := 0 deriving Inhabited

instance : ToStream NatStream NatStream := ⟨id⟩
instance : Stream NatStream Nat := ⟨fun ⟨r⟩ => some (r, ⟨r + 1⟩)⟩
