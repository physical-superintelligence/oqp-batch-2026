module

public import CGLMPBounds.Defs.HolomorphicPinching
public import CGLMPBounds.Defs.PartitionHardy

@[expose] public section


/-! The literal scalar potential used in C.14. It is constructed by two
actual straight-segment integrals of sec(πz/2), with the printed Catalan
constant. No differential identity, continuity or bound is a definition
field; each must be proved from these integrals. -/

namespace CGLMPBounds.Hardy
noncomputable section

def hardyStripSecant (z : ℂ) : ℂ := 1 / Complex.cos (Real.pi * z / 2)

/-- Integration along the straight segment from zero to z. -/
def segmentPrimitive (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * ∫ u : ℝ in (0 : ℝ)..1, g ((u : ℂ) * z)

def hardyStripCenterConstant : ℝ :=
  8 * Partition.sourceCatalanConstant / Real.pi ^ 2

def hardyStripPotential (z : ℂ) : ℂ :=
  (hardyStripCenterConstant : ℂ) - segmentPrimitive (segmentPrimitive hardyStripSecant) z

def hardyStripRealPotential (x y : ℝ) : ℝ :=
  (hardyStripPotential ((x : ℂ) + Complex.I * y)).re

end
end CGLMPBounds.Hardy
