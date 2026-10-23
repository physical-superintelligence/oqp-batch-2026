module

public import CGLMPBounds.Defs.ScalarPartition
public import CGLMPBounds.Defs.Circulation

@[expose] public section


/-! Literal coefficient form L_w and forbidden mass F_d from (C.1)–(C.2). -/

namespace CGLMPBounds
noncomputable section

def scalarEdgeForm {d r : ℕ} (w : ℕ → ℝ) (V : Fin d → Circulation.Mat r) : ℝ :=
  ∑ i, ∑ j, if i < j then
    w (j.val - i.val) * (1 - (Circulation.corr (V i) (V j)).re) +
      w (d - (j.val - i.val)) * (Circulation.corr (V i) (V j)).im else 0

def scalarForbiddenTotal {d r : ℕ} (V : Fin d → Circulation.Mat r) : ℝ :=
  ∑ i, ∑ j, if i < j then Circulation.forbidden (V i) (V j) else 0

end
end CGLMPBounds
