module

public import ThreeCopyQutritWerner.ThinPencilFactors
public import ThreeCopyQutritWerner.TwoSiteJointFactorFlatten

@[expose] public section


/-!
# The physical source in the fixed-row pencil branch

The fixed row of a local flattening is the actual remaining-site/logical
matrix. It is not a fixed local output direction. Reassembling the two
original source blocks keeps an arbitrary vector on the inactive pair.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

def thinTensorSource {a b c n : Type*} (κ : a × b → ℂ) (R : Matrix c n ℂ) :
    Matrix (a × b × c) n ℂ := fun p j => κ (p.1, p.2.1) * R p.2.2 j

theorem thinTensorSource_rank_le
    {a b c n : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype n]
    [DecidableEq c] (κ : a × b → ℂ) (R : Matrix c n ℂ) :
    (thinTensorSource κ R).rank ≤ R.rank := by
  let L : Matrix (a × b × c) c ℂ :=
    fun p s => if p.2.2 = s then κ (p.1, p.2.1) else 0
  have he : thinTensorSource κ R = L * R := by
    ext p j
    change κ (p.1, p.2.1) * R p.2.2 j =
      ∑ s, (if p.2.2 = s then κ (p.1, p.2.1) else 0) * R s j
    simp [ite_mul]
  rw [he]
  exact Matrix.rank_mul_le_right _ _

theorem firstSite_fixed_row_source
    (X : Matrix QutritSites (Fin 2) ℂ)
    (u v : Fin 3 → ℂ) (r : Fin 3 × Fin 2 → ℂ)
    (h0 : twoSiteFactorFlatten (firstSiteFactorBlock X 0) = Matrix.vecMulVec u r)
    (h1 : twoSiteFactorFlatten (firstSiteFactorBlock X 1) = Matrix.vecMulVec v r)
    (h2 : firstSiteFactorBlock X 2 = 0) :
    X = thinTensorSource (fun p => ![u, v, 0] p.1 p.2) (fun i j => r (i, j)) := by
  ext ⟨i, b, c⟩ j
  fin_cases i
  · exact congrFun (congrFun h0 b) (c, j)
  · exact congrFun (congrFun h1 b) (c, j)
  · simpa [thinTensorSource, firstSiteFactorBlock] using congrFun (congrFun h2 (b, c)) j

theorem thinTensorSource_rank_two_remaining_factor
    (κ : Fin 3 × Fin 3 → ℂ) (R : Matrix (Fin 3) (Fin 2) ℂ)
    (h : (thinTensorSource κ R).rank = 2) : R.rank = 2 ∧ κ ≠ 0 := by
  have hle := thinTensorSource_rank_le κ R
  have hup : R.rank ≤ 2 := by simpa using Matrix.rank_le_card_width R
  refine ⟨by omega, ?_⟩
  intro hz
  have he : thinTensorSource κ R = 0 := by ext p j; simp [thinTensorSource, hz]
  simp [he] at h

end ThreeCopyQutritWerner
