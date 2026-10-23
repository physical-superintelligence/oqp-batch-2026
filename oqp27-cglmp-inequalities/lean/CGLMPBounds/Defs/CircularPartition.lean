module

public import CGLMPBounds.Defs.PartitionHardy
public import CGLMPBounds.Defs.PartitionCoefficient

@[expose] public section


/-! Actual circular assignments of the source fourth-root tuple.
Crossing d labels multiplies V by -i, exactly as in D.2. The circular
boundary points are actual product-space coordinates; sorting is encoded
by counting boundaries before t. Expected Hardy forms remain literal
integrals, with no coefficient identity or positivity embedded. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix
noncomputable section

def circularAssignmentStep {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (a : Fin d) (T : Fin d → ℝ) (t : ℝ) :
    Circulation.Mat r :=
  let k := a.val + boundaryArcCount d 0 t T
  (-Complex.I) ^ (k / d) • V ⟨k % d, Nat.mod_lt _ hd⟩

def circularAssignmentBranch {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (a : Fin d) (T : Fin d → ℝ) (t : ℝ) :
    Circulation.Mat r :=
  Complex.exp (((-Real.pi * t / 2 : ℝ) : ℂ) * Complex.I) •
    (circularAssignmentStep hd V a T t)ᴴ

def circularPartitionHardyAverage {d r : ℕ} (hd : 0 < d)
    (V : Fin d → Circulation.Mat r) (T : Fin d → ℝ) : ℝ :=
  (1 / (d : ℝ)) * ∑ a : Fin d,
    (matrixNegativeFourierEnergy (circularAssignmentBranch hd V a T) -
      sourceFourthRootHardyConstant)

def averagedCircularHardyForm {d r : ℕ} (hd : 0 < d)
    (μ : Measure (Fin d → ℝ)) (V : Fin d → Circulation.Mat r) : ℝ :=
  ∫ T, circularPartitionHardyAverage hd V T ∂μ

end
end CGLMPBounds.Partition
