module

public import ThreeCopyQutritWerner.SingularNuclearTrace
public import ThreeCopyQutritWerner.ZeroReserveAlgebra
public import ThreeCopyQutritWerner.RankOne

@[expose] public section


/-!
# Equality in the nuclear trace factor estimate

The actual singular family supplies an attained unitary trace test. Equality
in the factor bound then gives an exact scalar multiple of a unitary image,
and hence equal kernels when both factors have positive Frobenius norm.
Applying this to the exterior factors retains the equality information needed
to recover source ranges from reduced transitions.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Rectangular Hilbert--Schmidt pairing with the actual column-space trace. -/
theorem nuclearTrace_hsInner_eq_trace {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) : hsInner A B = (Aᴴ * B).trace := by
  simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.star_def]
  exact Finset.sum_comm

/-- The actual variational trace norm has a unitary test whose trace is real
and nonnegative, with no supplied decomposition premise. -/
theorem nuclearTrace_exists_attaining_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ (Uᴴ * X).trace = (nuclearTrace X : ℂ) := by
  classical
  obtain ⟨U, hU, hmap⟩ := orthonormalFamilies_exists_unitary
    (singularLeft X) (singularRight X) (singularLeft_braket X) (singularRight_braket X)
  refine ⟨U, hU, ?_⟩
  rw [nuclearTrace_eq_sum_singularWeight,
    singular_trace_expansion X U (singularWeight X) (singularLeft X) (singularRight X)
      (singularFamily_reconstruct X)]
  simp only [hmap, singularLeft_braket, if_true, mul_one, Complex.ofReal_sum]

/-- Equality in the Frobenius factor estimate fixes the two rectangular factors
up to an actual left unitary and a nonnegative real scalar. -/
theorem nuclearTrace_factor_equality {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq n]
    (A B : Matrix n k ℂ) (hB : 0 < frobSq B)
    (heq : nuclearTrace (A * Bᴴ) = Real.sqrt (frobSq A * frobSq B)) :
    ∃ (U : Matrix n n ℂ) (c : ℝ), Uᴴ * U = 1 ∧ 0 ≤ c ∧
      c ^ 2 * frobSq B = frobSq A ∧ A = (c : ℂ) • (U * B) := by
  obtain ⟨U, hU, htrace⟩ := nuclearTrace_exists_attaining_unitary (A * Bᴴ)
  let q := Real.sqrt (frobSq A * frobSq B)
  let c := q / frobSq B
  have hq : q ^ 2 = frobSq A * frobSq B :=
    Real.sq_sqrt (mul_nonneg (frobSq_nonneg A) hB.le)
  have hc : 0 ≤ c := div_nonneg (Real.sqrt_nonneg _) hB.le
  have hcb : c * frobSq B = q := div_mul_cancel₀ q (ne_of_gt hB)
  have hc2 : c ^ 2 * frobSq B = frobSq A := by
    apply (mul_right_cancel₀ (ne_of_gt hB))
    calc
      c ^ 2 * frobSq B * frobSq B = (c * frobSq B) ^ 2 := by ring
      _ = q ^ 2 := by rw [hcb]
      _ = frobSq A * frobSq B := hq
  have hpair : hsInner (U * B) A = (q : ℂ) := by
    rw [nuclearTrace_hsInner_eq_trace, Matrix.conjTranspose_mul]
    calc
      (Bᴴ * Uᴴ * A).trace = (Bᴴ * (Uᴴ * A)).trace := by rw [Matrix.mul_assoc]
      _ = (Uᴴ * A * Bᴴ).trace := Matrix.trace_mul_comm _ _
      _ = (Uᴴ * (A * Bᴴ)).trace := by rw [Matrix.mul_assoc]
      _ = (q : ℂ) := by rw [htrace, heq]
  have hcross : (hsInner A ((c : ℂ) • (U * B))).re = c * q := by
    have hs := zeroReserve_hsInner_smul A (U * B) 1 (c : ℂ)
    simp only [one_smul, map_one, one_mul] at hs
    rw [hs]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [hsInner_re_comm, hpair, Complex.ofReal_re]
  have hz : frobSq (A - (c : ℂ) • (U * B)) = 0 := by
    rw [frobSq_sub, frobSq_smul, Complex.normSq_ofReal,
      nuclearTrace_frobSq_isometry_mul U B hU, hcross]
    rw [← hcb]
    nlinarith [hc2]
  exact ⟨U, c, hU, hc, hc2,
    sub_eq_zero.mp (matrix_eq_zero_of_frobSq_eq_zero _ hz)⟩

/-- Positive factors in a saturated nuclear estimate have proportional original
Gram matrices, with a strictly positive proportionality scalar. -/
theorem nuclearTrace_factor_equality_gram {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq n]
    (A B : Matrix n k ℂ) (hA : 0 < frobSq A) (hB : 0 < frobSq B)
    (heq : nuclearTrace (A * Bᴴ) = Real.sqrt (frobSq A * frobSq B)) :
    ∃ c : ℝ, 0 < c ∧ Aᴴ * A = ((c ^ 2 : ℝ) : ℂ) • (Bᴴ * B) := by
  obtain ⟨U, c, hU, hc, hc2, hfactor⟩ := nuclearTrace_factor_equality A B hB heq
  have hcp : 0 < c := by
    by_contra hn
    have hz : c = 0 := le_antisymm (le_of_not_gt hn) hc
    rw [hz] at hc2
    norm_num at hc2
    linarith
  refine ⟨c, hcp, ?_⟩
  rw [hfactor, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.conjTranspose_mul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U B, hU, Matrix.one_mul]
  simp only [Complex.ofReal_pow, pow_two, Complex.ofReal_mul]

/-- Positive factors saturating the nuclear factor bound have exactly the same
original column kernel, not merely equal ranks. -/
theorem nuclearTrace_factor_equality_kernel {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq n]
    (A B : Matrix n k ℂ) (hA : 0 < frobSq A) (hB : 0 < frobSq B)
    (heq : nuclearTrace (A * Bᴴ) = Real.sqrt (frobSq A * frobSq B))
    (v : k → ℂ) : A *ᵥ v = 0 ↔ B *ᵥ v = 0 := by
  obtain ⟨U, c, hU, hc, hc2, hfactor⟩ := nuclearTrace_factor_equality A B hB heq
  have hcne : c ≠ 0 := by
    intro hz
    rw [hz] at hc2
    norm_num at hc2
    linarith
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hcne
  rw [hfactor, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have hz : U *ᵥ (B *ᵥ v) = 0 := (smul_eq_zero.mp h).resolve_left hcC
    have hh := congrArg (fun w => Uᴴ *ᵥ w) hz
    rw [Matrix.mulVec_zero] at hh
    rw [Matrix.mulVec_mulVec (B *ᵥ v) Uᴴ U, hU, Matrix.one_mulVec] at hh
    exact hh
  · intro h
    rw [h, Matrix.mulVec_zero, smul_zero]

/-- Saturation of the exterior transition estimate saturates its actual
compound nuclear factor bound. -/
theorem nuclearTrace_transition_equality_compound {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq n]
    (A B : Matrix n k ℂ)
    (heq : nuclearTrace (A * Bᴴ) ^ 2 - frobSq (A * Bᴴ) =
      Real.sqrt ((frobSq A ^ 2 - frobSq (Aᴴ * A)) *
        (frobSq B ^ 2 - frobSq (Bᴴ * B)))) :
    nuclearTrace (zeroReserveCompound A * (zeroReserveCompound B)ᴴ) =
      Real.sqrt (frobSq (zeroReserveCompound A) * frobSq (zeroReserveCompound B)) := by
  have h1 := nuclearTrace_sq_sub_frobSq_le_compound (A * Bᴴ)
  have h2 := nuclearTrace_compound_mul_conjTranspose_le A B
  have hroot : Real.sqrt ((frobSq A ^ 2 - frobSq (Aᴴ * A)) *
      (frobSq B ^ 2 - frobSq (Bᴴ * B))) =
      2 * Real.sqrt (frobSq (zeroReserveCompound A) * frobSq (zeroReserveCompound B)) := by
    rw [← zeroReserveCompound_frobSq A, ← zeroReserveCompound_frobSq B]
    rw [show (2 * frobSq (zeroReserveCompound A)) *
        (2 * frobSq (zeroReserveCompound B)) =
          4 * (frobSq (zeroReserveCompound A) * frobSq (zeroReserveCompound B)) by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show Real.sqrt (4 : ℝ) = 2 from
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)]
  rw [heq, hroot] at h1
  rw [zeroReserveCompound_mul, zeroReserveCompound_conjTranspose] at h1 h2
  linarith

/-- At a positive-entropy saturated transition the two actual exterior maps
have identical kernels on all ordered-pair coefficient vectors. -/
theorem nuclearTrace_transition_equality_exterior_kernel {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq n]
    (A B : Matrix n k ℂ)
    (hA : 0 < frobSq (zeroReserveCompound A))
    (hB : 0 < frobSq (zeroReserveCompound B))
    (heq : nuclearTrace (A * Bᴴ) ^ 2 - frobSq (A * Bᴴ) =
      Real.sqrt ((frobSq A ^ 2 - frobSq (Aᴴ * A)) *
        (frobSq B ^ 2 - frobSq (Bᴴ * B))))
    (v : k × k → ℂ) :
    zeroReserveCompound A *ᵥ v = 0 ↔ zeroReserveCompound B *ᵥ v = 0 :=
  nuclearTrace_factor_equality_kernel _ _ hA hB
    (nuclearTrace_transition_equality_compound A B heq) v

end ThreeCopyQutritWerner
