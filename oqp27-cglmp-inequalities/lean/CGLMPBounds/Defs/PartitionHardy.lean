module

public import CGLMPBounds.Defs.ScalarForm

@[expose] public section


/-! Literal interval partitions and matrix Fourier energy for D.2.
Lebesgue integration over [0,1] represents normalized Haar integration on
the unit circle. The negative coefficient convention is exp(+2πint).
All sums, traces and constants are explicit; no analytic identity or
positivity statement is a field of these definitions. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise
noncomputable section

/-- Consecutive intervals, allowing zero lengths. The geometry alone is stored. -/
structure ConsecutivePartition (d : ℕ) where
  boundary : Fin (d + 1) → ℝ
  monotone_boundary : Monotone boundary
  boundary_zero : boundary 0 = 0
  boundary_one : boundary (Fin.last d) = 1

def ConsecutivePartition.cell {d : ℕ} (ℓ : ConsecutivePartition d) (j : Fin d) : Set ℝ :=
  Ico (ℓ.boundary j.castSucc) (ℓ.boundary j.succ)

def consecutivePartitionStep {d r : ℕ} (ℓ : ConsecutivePartition d)
    (V : Fin d → Circulation.Mat r) (t : ℝ) : Circulation.Mat r :=
  ∑ j, (ℓ.cell j).indicator (fun _ => V j) t

def consecutivePartitionBranch {d r : ℕ} (ℓ : ConsecutivePartition d)
    (V : Fin d → Circulation.Mat r) (t : ℝ) : Circulation.Mat r :=
  Complex.exp (((-Real.pi * t / 2 : ℝ) : ℂ) * Complex.I) •
    (consecutivePartitionStep ℓ V t)ᴴ

/-- The strictly negative coefficient at frequency -(n+1). -/
def matrixNegativeFourierCoefficient {r : ℕ} (U : ℝ → Circulation.Mat r) (n : ℕ) :
    Circulation.Mat r :=
  ∫ t in (0 : ℝ)..1,
    Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) • U t

/-- Parseval coefficient expression for the squared negative Hardy norm.
Its identification with an L² projection and its convergence are theorem obligations. -/
def matrixNegativeFourierEnergy {r : ℕ} (U : ℝ → Circulation.Mat r) : ℝ :=
  ∑' n : ℕ, Circulation.hsSq (matrixNegativeFourierCoefficient U n)

def sourceCatalanConstant : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2

def sourceFourthRootHardyConstant : ℝ :=
  1 / 2 - 4 * sourceCatalanConstant / Real.pi ^ 2

def consecutivePartitionHardyGap {d r : ℕ} (ℓ : ConsecutivePartition d)
    (V : Fin d → Circulation.Mat r) : ℝ :=
  matrixNegativeFourierEnergy (consecutivePartitionBranch ℓ V) -
    sourceFourthRootHardyConstant

/-- The literal double integral on the right of D.2, normalized by 1/2. -/
def consecutivePartitionPairForm {d r : ℕ} (ℓ : ConsecutivePartition d)
    (V : Fin d → Circulation.Mat r) : ℝ :=
  (1 / 2 : ℝ) * ∑ j : Fin d, ∑ k : Fin d, if j < k then
    ∫ s in (ℓ.boundary j.castSucc)..(ℓ.boundary j.succ),
      ∫ t in (ℓ.boundary k.castSucc)..(ℓ.boundary k.succ),
        scalarSecant (t - s) * (1 - (Circulation.corr (V j) (V k)).re) +
          scalarSecant (1 - t + s) * (Circulation.corr (V j) (V k)).im
    else 0

end
end CGLMPBounds.Partition
