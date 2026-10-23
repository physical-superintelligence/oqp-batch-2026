module

public import ThreeCopyQutritWerner.TwoCutFixedSourceTrace
public import ThreeCopyQutritWerner.BinaryCutRangeLine
public import ThreeCopyQutritWerner.TwoCutNonzeroRank

@[expose] public section


/-!
# The scalar line on a nondegenerate fixed cut-zero source

The same literal local coordinate inclusions compress both original
operators. Actual range inclusion descends to their compressed matrices.
The constructed trace-zero skew forms then give scalar-line rigidity.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- An actual common isometric carrier transports range inclusion to the
compressed matrices; compatible right factors are constructed internally. -/
theorem matrix_isometric_carrier_range_le
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : Wᴴ * W = 1)
    (A B : Matrix m m ℂ) (K L : Matrix n n ℂ)
    (hA : A = W * K * Wᴴ) (hB : B = W * L * Wᴴ)
    (hBA : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin) :
    LinearMap.range L.mulVecLin ≤ LinearMap.range K.mulVecLin := by
  obtain ⟨R, hR⟩ := matrix_exists_right_factor_of_range_le B A hBA
  have hL : L = K * (Wᴴ * R * W) := by
    calc
      L = Wᴴ * B * W := by
        rw [hB]
        calc
          L = (Wᴴ * W) * L * (Wᴴ * W) := by rw [hW, Matrix.one_mul, Matrix.mul_one]
          _ = _ := by simp only [Matrix.mul_assoc]
      _ = Wᴴ * (A * R) * W := by rw [hR]
      _ = K * (Wᴴ * R * W) := by
        rw [hA]
        simp only [← Matrix.mul_assoc, hW, Matrix.one_mul]
  rw [hL]
  rintro _ ⟨v, rfl⟩
  refine ⟨(Wᴴ * R * W) *ᵥ v, ?_⟩
  change K *ᵥ ((Wᴴ * R * W) *ᵥ v) = (K * (Wᴴ * R * W)) *ᵥ v
  exact Matrix.mulVec_mulVec v _ _

/-- Outside the two explicit local single-output branches, all cut zeros
with the same actual source and the anchor's two missing output coordinates
lie on one complex scalar line. No common input plane is assumed. -/
theorem twoCut_fixed_source_eq_smul
    (A B : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hA : A.rank ≤ 2) (hqA : cutForm A = 0)
    (hB : B.rank ≤ 2) (hqB : cutForm B = 0)
    (hR : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin)
    (a b : Fin 3) (hrow : ∀ i j q, i = a ∨ j = b → A (i, j) q = 0)
    (hfirst : ¬ HasSingleFirstOutput A) (hsecond : ¬ HasSingleFirstOutput (twoCutSwap A)) :
    ∃ z : ℂ, B = z • A := by
  by_cases hzero : A = 0
  · obtain ⟨R, hBR⟩ := matrix_exists_right_factor_of_range_le B A hR.symm.le
    exact ⟨0, by simp [hBR, hzero]⟩
  have hrA : A.rank = 2 := rank_two_of_nonzero_cutForm_zero A hA hqA hzero
  have htA := cutForm_zero_fixed_source_trace_zero A A hA hqA le_rfl hfirst hsecond
  have htB := cutForm_zero_fixed_source_trace_zero A B hB hqB hR.le hfirst hsecond
  obtain ⟨K, hK⟩ := twoCut_fixed_source_common_coordinate_carrier
    A A hA hqA rfl a b hrow hfirst hsecond
  obtain ⟨L, hL⟩ := twoCut_fixed_source_common_coordinate_carrier
    A B hB hqB hR a b hrow hfirst hsecond
  let W := qutritPlaneInclusion a ⊗ₖ qutritPlaneInclusion b
  have hW : Wᴴ * W = 1 := kron_isometry _ _
    (qutritPlaneInclusion_isometry a) (qutritPlaneInclusion_isometry b)
  have hdK := twoCut_local_conj_data _ _
    (qutritPlaneInclusion_isometry a) (qutritPlaneInclusion_isometry b) K
  have hdL := twoCut_local_conj_data _ _
    (qutritPlaneInclusion_isometry a) (qutritPlaneInclusion_isometry b) L
  have hKr : K.rank = 2 := hdK.1.symm.trans (hK ▸ hrA)
  have hKq : cutForm K = 0 := hdK.2.2.symm.trans (hK ▸ hqA)
  have hLq : cutForm L = 0 := hdL.2.2.symm.trans (hL ▸ hqB)
  have hKt : K.trace = 0 := by
    rw [hK, trace_conj_isometry _ hW] at htA
    exact htA
  have hLt : L.trace = 0 := by
    rw [hL, trace_conj_isometry _ hW] at htB
    exact htB
  obtain ⟨z, hz⟩ := binaryCut_trace_zero_eq_smul_of_range_le K L hKq hLq hKt hLt hKr
    (matrix_isometric_carrier_range_le W hW A B K L hK hL hR.symm.le)
  refine ⟨z, ?_⟩
  rw [hL, hz, Matrix.mul_smul, Matrix.smul_mul, ← hK]

end ThreeCopyQutritWerner
