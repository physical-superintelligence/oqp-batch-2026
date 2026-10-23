module

public import CGLMPBounds.CGLMP.DimensionDeficitRankForcing
public import CGLMPBounds.Quantum.General
public import CGLMPBounds.CGLMP.DimensionDeficitRounding
public import CGLMPBounds.CGLMP.DimensionDeficitRankRepair

@[expose] public section


/-! Spectral trace variation for a Hermitian operator measured by an actual
PVM. This proves the trace-norm ingredient of F.18 without assuming a trace
norm inequality or a rank bound. All norms below are explicit eigenvalue sums. -/

namespace CGLMPBounds
noncomputable section
open Matrix
open scoped ComplexOrder
variable {n : ℕ}

lemma matrix_rank_sub_le (P Q : Matrix (Fin n) (Fin n) ℂ) :
    (P - Q).rank ≤ P.rank + Q.rank := by
  have hr : LinearMap.range (P - Q).mulVecLin ≤
      LinearMap.range P.mulVecLin ⊔ LinearMap.range Q.mulVecLin := by
    rintro y ⟨x, rfl⟩
    change (P - Q) *ᵥ x ∈ _
    rw [Matrix.sub_mulVec]
    apply Submodule.sub_mem
    · exact Submodule.mem_sup_left (LinearMap.mem_range_self P.mulVecLin x)
    · exact Submodule.mem_sup_right (LinearMap.mem_range_self Q.mulVecLin x)
  exact (Submodule.finrank_mono hr).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma hermitian_rank_eq_eigenvalue_support {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.IsHermitian) :
    X.rank = (Finset.univ.filter (fun i => hX.eigenvalues i ≠ 0)).card := by
  classical
  have hU : IsUnit (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := Unitary.isUnit_coe
  have hUdet := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hUstar := (Matrix.isUnit_iff_isUnit_det _).mp hU.star
  conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUstar,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hUdet, Matrix.rank_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_ne_zero, Fintype.card_subtype]

lemma hermitian_gram_trace_eq_eigenvalue_sq {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.IsHermitian) :
    (Matrix.trace (Xᴴ * X)).re = ∑ i, (hX.eigenvalues i)^2 := by
  rw [hX.eq]
  have he : X * X = Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ)
      hX.eigenvectorUnitary (Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) *
        Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues)) := by
    rw [map_mul, ← hX.spectral_theorem]
  rw [he, trace_unitary_conj_matrix, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_mul, Complex.ofReal_re, pow_two]

lemma hermitian_eigenvalue_abs_sum_sq {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.IsHermitian) :
    (∑ i, |hX.eigenvalues i|)^2 ≤
      (X.rank : ℝ) * (Matrix.trace (Xᴴ * X)).re := by
  classical
  let w := hX.eigenvalues
  have hp (i : Fin n) : (if w i = 0 then (0 : ℝ) else 1) * |w i| = |w i| := by
    by_cases h : w i = 0 <;> simp [h]
  have hcount : (∑ i : Fin n, (if w i = 0 then (0 : ℝ) else 1)^2) = (X.rank : ℝ) := by
    rw [hermitian_rank_eq_eigenvalue_support hX]
    simp only [ite_pow, zero_pow (by omega : (2 : ℕ) ≠ 0), one_pow]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : hX.eigenvalues i = 0 <;> simp [w, hi]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => if w i = 0 then (0 : ℝ) else 1) (fun i => |w i|)
  simp only [hp, sq_abs, hcount] at h
  rw [hermitian_gram_trace_eq_eigenvalue_sq hX]
  exact h

lemma re_trace_mul_in_eigenbasis {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.IsHermitian) (R : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.trace (X * R)).re = ∑ i, hX.eigenvalues i *
      (((hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ * R *
        (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) i i).re := by
  let U : Matrix (Fin n) (Fin n) ℂ := hX.eigenvectorUnitary
  conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
  have he : Matrix.trace
      (((U * Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues)) * Uᴴ) * R) =
      Matrix.trace (Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) * (Uᴴ * R * U)) := by
    calc
      _ = Matrix.trace (U * (Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) * Uᴴ * R)) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) * Uᴴ * R) * U) :=
        Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  change (Matrix.trace (((U * Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues)) * Uᴴ) * R)).re = _
  rw [he]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Complex.re_sum,
    Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, U]

/-- The total variation of the actual PVM trace functional is bounded by
its explicit spectral absolute-value sum, including nonfaithful projections. -/
lemma sum_abs_re_trace_mul_pvm_le_eigenvalue_abs {β : Type*}
    [Fintype β] (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian)
    (R : β → Matrix (Fin n) (Fin n) ℂ) (hR : IsPVM R) :
    (∑ b, |(Matrix.trace (X * R b)).re|) ≤ ∑ i, |hX.eigenvalues i| := by
  let U : Matrix (Fin n) (Fin n) ℂ := hX.eigenvectorUnitary
  let w : β → Fin n → ℝ := fun b i => ((Uᴴ * R b * U) i i).re
  have hw (b : β) (i : Fin n) : 0 ≤ w b i := by
    have hp := (posSemidef_of_hermitian_idempotent (hR.isHermitian b) (hR.mul_self b)).conjTranspose_mul_mul_same U
    exact (Complex.nonneg_iff.mp (hp.diag_nonneg (i := i))).1
  have hsum (i : Fin n) : ∑ b, w b i = 1 := by
    have hs : (∑ b, Uᴴ * R b * U) = 1 := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hR.sum_eq_one, Matrix.mul_one]
      exact hX.eigenvectorUnitary.property.1
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => (A i i).re) hs
    simpa only [Matrix.sum_apply, Complex.re_sum, Matrix.one_apply_eq, Complex.one_re] using h
  calc
    _ ≤ ∑ b, ∑ i, |hX.eigenvalues i| * w b i := by
      apply Finset.sum_le_sum
      intro b _
      rw [re_trace_mul_in_eigenbasis hX]
      apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (hw b i)]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum, hsum, mul_one]

lemma sum_abs_re_trace_mul_pvm_sq_le {β : Type*} [Fintype β]
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian)
    (R : β → Matrix (Fin n) (Fin n) ℂ) (hR : IsPVM R) :
    (∑ b, |(Matrix.trace (X * R b)).re|)^2 ≤
      (X.rank : ℝ) * (Matrix.trace (Xᴴ * X)).re := by
  apply (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (sum_abs_re_trace_mul_pvm_le_eigenvalue_abs X hX R hR) 2).trans
  exact hermitian_eigenvalue_abs_sum_sq hX

end
end CGLMPBounds
