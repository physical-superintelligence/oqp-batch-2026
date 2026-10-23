module

public import CGLMPBounds.Defs.PositivePinching
public import CGLMPBounds.Defs.TwoNodeResidue

@[expose] public section


/-! Literal matrix index cycles for C.13. A path recursively multiplies actual
matrix entries; closing its last edge at its first index gives an ordered
cycle, with every starting index and repeated index retained. -/

namespace CGLMPBounds.Hardy
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The n internal indices of an n+1-edge matrix path from i to j. -/
def matrixIndexPathWeight (Y : Matrix ι ι ℂ) (i j : ι) :
    (n : ℕ) → (Fin n → ι) → ℂ
  | 0, _ => Y i j
  | n + 1, v => Y i (v 0) * matrixIndexPathWeight Y (v 0) j n (fun k => v k.succ)

/-- An ordered cycle of length n+1, including its closing edge. -/
def matrixIndexCycleWeight (Y : Matrix ι ι ℂ) (n : ℕ) (v : Fin (n + 1) → ι) : ℂ :=
  matrixIndexPathWeight Y (v 0) (v 0) n (fun k => v k.succ)

def involutionFromSigns (σ : ι → Bool) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => if σ i then (1 : ℂ) else -1)

def cyclePositiveCount (σ : ι → Bool) {n : ℕ} (v : Fin n → ι) : ℕ :=
  (Finset.univ.filter (fun k => σ (v k) = true)).card

/-- The literal right side of C.13 for degree m+2; p is the number of +1
indices and q=m+2-p. Only mixed cycles contribute. -/
def pinchingCycleMoment (σ : ι → Bool) (Y : Matrix ι ι ℂ) (m : ℕ) (x : ℝ) : ℂ :=
  (1 / ((Fintype.card ι : ℂ) * ((m + 2 : ℕ) : ℂ) * 2 ^ (m + 1))) *
    ∑ v : Fin (m + 2) → ι,
      let p := cyclePositiveCount σ v
      let q := m + 2 - p
      if 1 ≤ p ∧ p < m + 2 then
        (m.choose (p - 1) : ℂ) * (1 - (x : ℂ)) ^ (p - 1) *
          (1 + (x : ℂ)) ^ (q - 1) * matrixIndexCycleWeight Y (m + 1) v
      else 0

end
end CGLMPBounds.Hardy
