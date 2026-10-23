module

public import CGLMPBounds.Defs.CircularPartition

@[expose] public section


/-! Literal upper-triangle source pair integrand. The diagonal and lower
half square are zero by definition; no integrability or Hardy identity
is included in this definition. -/

namespace CGLMPBounds.Partition
noncomputable section

def stepPairIntegrand {r : ℕ} (S : ℝ → Circulation.Mat r) (p : ℝ × ℝ) : ℝ :=
  if p.1 < p.2 then
    scalarSecant (p.2 - p.1) * (1 - (Circulation.corr (S p.1) (S p.2)).re) +
      scalarSecant (1 - p.2 + p.1) * (Circulation.corr (S p.1) (S p.2)).im
  else 0

end
end CGLMPBounds.Partition
