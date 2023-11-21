
instance [Alternative m] : MonadLift Option m := ⟨fun | none => failure | some a => pure a⟩
