module

public import ThreeCopyQutritWerner.TwoCutFactorCarrier
public import ThreeCopyQutritWerner.CoherentGramSupport

@[expose] public section


/-!
# Literal local joint minors of the actual cut-zero factors

Both source and corange factors use the same constructed physical binary
carrier. Their local columns can therefore be concatenated through one
actual two-column local matrix, giving rank at most two and zero minors.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

def twoSiteFactorFlatten {a b n : Type*} (X : Matrix (a × b) n ℂ) :
    Matrix a (b × n) ℂ := fun i p => X (i, p.1) p.2

def twoSiteJointFactorFlatten {a b n p : Type*}
    (X : Matrix (a × b) n ℂ) (Y : Matrix (a × b) p ℂ) :
    Matrix a ((b × n) ⊕ (b × p)) ℂ :=
  fun i q => Sum.elim (twoSiteFactorFlatten X i) (twoSiteFactorFlatten Y i) q

/-- A common physical tensor carrier gives the same local two-column
factor to both actual families. No isometry premise is needed for this bound. -/
theorem twoSiteJointFactorFlatten_carrier_rank_le_two
    {n p : Type*} [Fintype n] [Fintype p]
    (J₁ J₂ : Matrix (Fin 3) (Fin 2) ℂ)
    (R : Matrix (Fin 2 × Fin 2) n ℂ) (S : Matrix (Fin 2 × Fin 2) p ℂ) :
    (twoSiteJointFactorFlatten ((J₁ ⊗ₖ J₂) * R) ((J₁ ⊗ₖ J₂) * S)).rank ≤ 2 := by
  let T : Matrix (Fin 2) ((Fin 3 × n) ⊕ (Fin 3 × p)) ℂ := fun i q =>
    Sum.elim (fun q => ∑ j, J₂ q.1 j * R (i, j) q.2)
      (fun q => ∑ j, J₂ q.1 j * S (i, j) q.2) q
  have he : twoSiteJointFactorFlatten ((J₁ ⊗ₖ J₂) * R) ((J₁ ⊗ₖ J₂) * S) = J₁ * T := by
    ext i q
    cases q with
    | inl q =>
      change (∑ j, (J₁ ⊗ₖ J₂) (i, q.1) j * R j q.2) =
        ∑ k, J₁ i k * ∑ j, J₂ q.1 j * R (k, j) q.2
      simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
        Finset.mul_sum, mul_assoc]
    | inr q =>
      change (∑ j, (J₁ ⊗ₖ J₂) (i, q.1) j * S j q.2) =
        ∑ k, J₁ i k * ∑ j, J₂ q.1 j * S (k, j) q.2
      simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
        Finset.mul_sum, mul_assoc]
  rw [he]
  exact (Matrix.rank_mul_le_left J₁ T).trans (by simpa using Matrix.rank_le_card_width J₁)

/-- A cut zero with actual full two-column source and corange has joint
local rank at most two. The common carrier is constructed inside the proof. -/
theorem twoSiteJointFactorFlatten_rank_le_two_of_cut_zero
    (X Y : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ)
    (hX : X.rank = 2) (hY : Y.rank = 2) (hq : cutForm (X * Yᴴ) = 0) :
    (twoSiteJointFactorFlatten X Y).rank ≤ 2 := by
  obtain ⟨J₁, J₂, R, S, hJ₁, hJ₂, hR, hS⟩ :=
    cutForm_zero_full_factors_common_carrier X Y hX hY hq
  rw [hR, hS]
  exact twoSiteJointFactorFlatten_carrier_rank_le_two J₁ J₂ R S

/-- Every original three-column joint minor vanishes, with source and
corange columns kept in distinct sum-type summands. -/
theorem twoSiteJointFactorFlatten_minors_zero_of_cut_zero
    (X Y : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ)
    (hX : X.rank = 2) (hY : Y.rank = 2) (hq : cutForm (X * Yᴴ) = 0)
    (cols : Fin 3 → ((Fin 3 × Fin 2) ⊕ (Fin 3 × Fin 2))) :
    ((twoSiteJointFactorFlatten X Y).submatrix id cols).det = 0 :=
  all_three_minors_zero_of_rank_le_two _
    (twoSiteJointFactorFlatten_rank_le_two_of_cut_zero X Y hX hY hq) cols

end ThreeCopyQutritWerner
