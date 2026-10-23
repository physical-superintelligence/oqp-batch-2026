module

public import CGLMPBounds.Defs.Circulation

@[expose] public section


/-! The scalar labels in the literal cut formula (E.1). -/

namespace CGLMPBounds.Circulation

/-- Label a until and including j₀, and label a−1 modulo four afterwards. -/
def fourthRootCutLabels {d : ℕ} (a : Fin 4) (j₀ : Fin d) (j : Fin d) : Fin 4 :=
  if j₀ < j then a + 3 else a

end CGLMPBounds.Circulation
