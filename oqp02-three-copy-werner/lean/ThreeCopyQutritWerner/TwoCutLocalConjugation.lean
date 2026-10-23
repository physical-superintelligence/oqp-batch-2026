module

public import ThreeCopyQutritWerner.TwoCutOutputCollapse
public import ThreeCopyQutritWerner.ProductRayUnitary

@[expose] public section


/-!
# Physical local changes for the two-site alignment argument

The original cut form, rank and norm are preserved by local isometries.
A constructed single output direction can therefore be moved to one actual
coordinate by unitary conjugation, retaining the original input action.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- The existing two-site energy invariance is exactly invariance of cutForm. -/
theorem cutForm_local_conj
    {L R L' R' : Type*} [Fintype L] [Fintype R] [Fintype L'] [Fintype R']
    [DecidableEq L] [DecidableEq R]
    (U : Matrix L' L ℂ) (V : Matrix R' R ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (C : Matrix (L × R) (L × R) ℂ) :
    cutForm ((U ⊗ₖ V) * C * (U ⊗ₖ V)ᴴ) = cutForm C := by
  have h := twoSiteEndpoint_conj U V hU hV C
  unfold twoSiteEndpoint at h
  unfold cutForm
  linarith

/-- A physical local isometry preserves all three original data simultaneously. -/
theorem twoCut_local_conj_data
    {L R L' R' : Type*} [Fintype L] [Fintype R] [Fintype L'] [Fintype R']
    [DecidableEq L] [DecidableEq R]
    (U : Matrix L' L ℂ) (V : Matrix R' R ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (C : Matrix (L × R) (L × R) ℂ) :
    ((U ⊗ₖ V) * C * (U ⊗ₖ V)ᴴ).rank = C.rank ∧
      frobSq ((U ⊗ₖ V) * C * (U ⊗ₖ V)ᴴ) = frobSq C ∧
      cutForm ((U ⊗ₖ V) * C * (U ⊗ₖ V)ᴴ) = cutForm C :=
  ⟨productRay_rank_conj_isometry _ (kron_isometry U V hU hV) C,
    frobSq_conj_isometry _ (kron_isometry U V hU hV) C,
    cutForm_local_conj U V hU hV C⟩

/-- The inverse conjugation recovers the original operator exactly. -/
theorem twoCut_unitary_conj_recover {n : Type*} [Fintype n] [DecidableEq n]
    (U C : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    Uᴴ * (U * C * Uᴴ) * U = C := by
  calc
    _ = (Uᴴ * U) * C * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
    _ = C := by rw [hU, Matrix.one_mul, Matrix.mul_one]

/-- A literal first-site output factor supplies actual unitary coordinates
with only output coordinate zero allowed. No input-coordinate premise is used. -/
theorem twoCut_single_output_exists_unitary_coordinate
    {d : Type*} [Fintype d] [DecidableEq d]
    (C : Matrix (Fin 3 × d) (Fin 3 × d) ℂ) (i₀ : Fin 3) (x : Fin 3 → ℂ)
    (hx : x i₀ = 1) (hfactor : ∀ i r q, C (i, r) q = x i * C (i₀, r) q) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ, Uᴴ * U = 1 ∧
      ∀ i, i ≠ 0 → ∀ r q,
        ((U ⊗ₖ (1 : Matrix d d ℂ)) * C * (U ⊗ₖ (1 : Matrix d d ℂ))ᴴ) (i, r) q = 0 := by
  have hx0 : x ≠ 0 := by
    intro h
    have he := congrFun h i₀
    rw [hx] at he
    exact one_ne_zero he
  obtain ⟨U, z, hU, hz, hUx⟩ := productRay_exists_local_unitary x hx0
  refine ⟨U, hU, ?_⟩
  intro i hi r q
  have hleft (p : Fin 3 × d) :
      ((U ⊗ₖ (1 : Matrix d d ℂ)) * C) (i, r) p = 0 := by
    have he : ((U ⊗ₖ (1 : Matrix d d ℂ)) * C) (i, r) p =
        (U *ᵥ x) i * C (i₀, r) p := by
      calc
        _ = ∑ j, U i j * C (j, r) p := by
          simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
            Matrix.one_apply, mul_ite, ite_mul]
        _ = ∑ j, (U i j * x j) * C (i₀, r) p := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hfactor j r p]
          ring
        _ = (U *ᵥ x) i * C (i₀, r) p := by
          simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    rw [he, hUx]
    simp [hi]
  rw [Matrix.mul_apply]
  simp only [hleft, zero_mul, Finset.sum_const_zero]

end ThreeCopyQutritWerner
