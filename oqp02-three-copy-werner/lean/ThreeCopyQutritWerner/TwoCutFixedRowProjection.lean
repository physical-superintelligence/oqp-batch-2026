module

public import ThreeCopyQutritWerner.TwoCutSingleFactor
public import ThreeCopyQutritWerner.TwoCutTensorProjectionSource
public import ThreeCopyQutritWerner.QutritThinFrame
public import ThreeCopyQutritWerner.ThinPencilFactors

@[expose] public section


/-!
# A common projection from the actual fixed row of a local pencil

The remaining physical/logical factor determines one orthogonal plane.
Every cut-zero partner of any nonzero local ray has scalar projection
blocks on that same plane. No alignment of the partner is assumed.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

def twoSiteVectorSource {a b n : Type*} (u : a → ℂ) (R : Matrix b n ℂ) :
    Matrix (a × b) n ℂ := fun p j => u p.1 * R p.2 j

theorem twoSiteVectorSource_product_block
    (u : Fin 3 → ℂ) (R : Matrix (Fin 3) (Fin 2) ℂ)
    (Y : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ) (i j : Fin 3) :
    firstSiteBlock (twoSiteVectorSource u R * Yᴴ) i j =
      u i • (R * (firstSiteFactorBlock Y j)ᴴ) := by
  ext r s
  simp only [firstSiteBlock, Matrix.submatrix_apply, Matrix.mul_apply,
    twoSiteVectorSource, Matrix.conjTranspose_apply, firstSiteFactorBlock,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem cutForm_zero_fixed_row_projection_blocks
    (P : Matrix (Fin 3) (Fin 3) ℂ) (hP : P.IsHermitian)
    (hPP : P * P = P) (hPr : P.rank = 2)
    (R : Matrix (Fin 3) (Fin 2) ℂ) (hPR : P * R = R)
    (u : Fin 3 → ℂ) (hu : u ≠ 0) (Y : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ)
    (hq : cutForm (twoSiteVectorSource u R * Yᴴ) = 0) :
    ∀ j : Fin 3, ∃ α : ℂ, R * (firstSiteFactorBlock Y j)ᴴ = α • P := by
  classical
  let C := twoSiteVectorSource u R * Yᴴ
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hu (funext hn)
  have hblock := twoSiteVectorSource_product_block u R Y
  by_cases hz : C = 0
  · intro j
    refine ⟨0, ?_⟩
    ext r s
    have he := congrFun (congrFun (hblock i j) r) s
    change C (i, r) (j, s) = u i * (R * (firstSiteFactorBlock Y j)ᴴ) r s at he
    rw [hz] at he
    simpa only [zero_smul, Matrix.zero_apply] using
      (mul_eq_zero.mp he.symm).resolve_left hi
  have hr : C.rank ≤ 2 := (Matrix.rank_mul_le_left _ _).trans
    (by simpa using Matrix.rank_le_card_width (twoSiteVectorSource u R))
  have hs : ∀ l r q, C (l, r) q = (u l / u i) * C (i, r) q := by
    intro l r q
    have hl := congrFun (congrFun (hblock l q.1) r) q.2
    have hi' := congrFun (congrFun (hblock i q.1) r) q.2
    change C (l, r) (q.1, q.2) = u l * _ at hl
    change C (i, r) (q.1, q.2) = u i * _ at hi'
    rw [show q = (q.1, q.2) from rfl, hl, hi']
    field_simp [hi]
  obtain ⟨x, y, Q, _, _, hQ, hQQ, hQr, hC⟩ :=
    cutForm_zero_single_output_factor C hr hq hz i (fun l => u l / u i)
      (div_self hi) hs
  have hfix : ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ P) * twoSiteVectorSource u R =
      twoSiteVectorSource u R := by
    ext ⟨l, r⟩ j
    have he := congrFun (congrFun hPR r) j
    simp only [Matrix.mul_apply] at he
    simp [Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply,
      twoSiteVectorSource, Fintype.sum_prod_type, ite_mul]
    calc
      ∑ s, P r s * (u l * R s j) = u l * ∑ s, P r s * R s j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = u l * R r j := by rw [he]
  have hfixC : ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ P) * C = C := by
    change _ * (twoSiteVectorSource u R * Yᴴ) = _
    rw [← Matrix.mul_assoc, hfix]
  have hK : ketBra x y ≠ 0 := by
    intro hk
    apply hz
    rw [hC, hk]
    ext p q
    simp [Matrix.kroneckerMap_apply]
  obtain ⟨k, l, hkl⟩ : ∃ k l, ketBra x y k l ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hK (Matrix.ext hn)
  rw [hC, ← Matrix.mul_kronecker_mul, Matrix.one_mul] at hfixC
  have hPQ : P * Q = Q := by
    ext r s
    have he := congrFun (congrFun hfixC (k, r)) (l, s)
    exact mul_left_cancel₀ hkl he
  have hQP : LinearMap.range Q.mulVecLin ≤ LinearMap.range P.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine ⟨Q *ᵥ v, ?_⟩
    change P *ᵥ (Q *ᵥ v) = Q *ᵥ v
    rw [Matrix.mulVec_mulVec, hPQ]
  have heQP : Q = P := matrix_hermitian_idempotent_eq_of_range_le_rank_le
    Q P hQ hP hQQ hPP hQP (by omega)
  intro j
  refine ⟨(x i * star (y j)) / u i, ?_⟩
  ext r s
  have he := congrFun (congrFun (hblock i j) r) s
  change C (i, r) (j, s) = u i * (R * (firstSiteFactorBlock Y j)ᴴ) r s at he
  rw [hC, heQP] at he
  simp only [Matrix.kroneckerMap_apply, ketBra] at he
  change (R * (firstSiteFactorBlock Y j)ᴴ) r s = ((x i * star (y j)) / u i) * P r s
  rw [div_mul_eq_mul_div₀]
  apply (eq_div_iff hi).mpr
  simpa only [mul_comm, starRingEnd_apply] using he.symm

end ThreeCopyQutritWerner
