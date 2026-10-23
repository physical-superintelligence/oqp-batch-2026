module

public import Mathlib

@[expose] public section


/-!
# Fractional trace obstruction for positive contractions

Appendix E, proof of Theorem A.2: a positive contraction of trace `k + f`, with
integer `k` and `0 ≤ f < 1`, satisfies `Tr(X - X²) ≥ f(1-f)`. This file proves the
scalar finite-spectrum inequality and lifts it to Hermitian matrices using Mathlib's
spectral theorem. It is a self-contained dependency of the lower arithmetic bound;
the remaining companion-strategy and stability estimates are not assumed or asserted here.
-/

open Matrix
open scoped ComplexOrder

namespace CGLMPBounds

noncomputable section

/-- The quadratic fractional-part defect is subadditive. -/
theorem fractional_defect_add_le (x y : ℝ) :
    Int.fract (x + y) * (1 - Int.fract (x + y))
      ≤ Int.fract x * (1 - Int.fract x) + Int.fract y * (1 - Int.fract y) := by
  obtain ⟨z, hz⟩ := Int.fract_add x y
  have hz₀ : z ≤ 0 := by
    have h : (z : ℝ) ≤ 0 := by linarith [Int.fract_add_le x y]
    exact_mod_cast h
  have hz₁ : -1 ≤ z := by
    have h : (-1 : ℝ) ≤ z := by linarith [Int.fract_add_fract_le x y]
    exact_mod_cast h
  have hz_cases : z = -1 ∨ z = 0 := by omega
  rcases hz_cases with rfl | rfl
  · norm_num at hz
    have heq : Int.fract (x + y) = Int.fract x + Int.fract y - 1 := by linarith
    rw [heq]
    have h := mul_nonneg (sub_nonneg.mpr (Int.fract_lt_one x).le)
      (sub_nonneg.mpr (Int.fract_lt_one y).le)
    nlinarith
  · norm_num at hz
    have heq : Int.fract (x + y) = Int.fract x + Int.fract y := by linarith
    rw [heq]
    have h := mul_nonneg (Int.fract_nonneg x) (Int.fract_nonneg y)
    nlinarith

theorem fractional_defect_sum_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) :
    Int.fract (∑ i ∈ s, w i) * (1 - Int.fract (∑ i ∈ s, w i))
      ≤ ∑ i ∈ s, Int.fract (w i) * (1 - Int.fract (w i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (fractional_defect_add_le (w i) (∑ j ∈ s, w j)).trans (add_le_add le_rfl ih)

/-- The scalar eigenvalue form of the positive-contraction obstruction. -/
theorem sum_contraction_defect_ge_fract {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, w i ∈ Set.Icc (0 : ℝ) 1) :
    Int.fract (∑ i ∈ s, w i) * (1 - Int.fract (∑ i ∈ s, w i))
      ≤ ∑ i ∈ s, w i * (1 - w i) := by
  have heq : ∀ i ∈ s, Int.fract (w i) * (1 - Int.fract (w i)) = w i * (1 - w i) := by
    intro i hi
    rcases lt_or_eq_of_le (hw i hi).2 with hlt | heq
    · rw [Int.fract_eq_self.mpr ⟨(hw i hi).1, hlt⟩]
    · simp [heq]
  simpa only [Finset.sum_congr rfl heq] using fractional_defect_sum_le s w

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positive_contraction_eigenvalues_le_one {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) (hC : (1 - M).PosSemidef) (i : ι) :
    hM.1.eigenvalues i ≤ 1 := by
  have hdiag := hM.1.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at hdiag
  have hU : star (hM.1.eigenvectorUnitary : Matrix ι ι ℂ)
      * (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := Unitary.coe_star_mul_self _
  have hpos := hC.conjTranspose_mul_mul_same (hM.1.eigenvectorUnitary : Matrix ι ι ℂ)
  rw [← Matrix.star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    hU, hdiag] at hpos
  have h := (Complex.nonneg_iff.mp (hpos.diag_nonneg (i := i))).1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
    Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, Complex.sub_re,
    Complex.one_re, Complex.ofReal_re] at h
  linarith

theorem re_trace_contraction_defect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    (Matrix.trace (M - M * M)).re
      = ∑ i, hM.eigenvalues i * (1 - hM.eigenvalues i) := by
  have hdef : M - M * M
      = Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hM.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)
            - Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)
              * Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)) := by
    rw [map_sub, map_mul, ← hM.spectral_theorem]
  rw [hdef, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_sub, Matrix.trace_diagonal,
    Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply, RCLike.ofReal_eq_complex_ofReal,
    Complex.sub_re, Complex.ofReal_re, ← Complex.ofReal_mul]
  ring

/-- A positive contraction has at least the fractional-part defect of its trace. -/
theorem positive_contraction_fractional_trace_bound {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) (hC : (1 - M).PosSemidef) :
    Int.fract (Matrix.trace M).re * (1 - Int.fract (Matrix.trace M).re)
      ≤ (Matrix.trace (M - M * M)).re := by
  have ht : (Matrix.trace M).re = ∑ i, hM.1.eigenvalues i := by
    simpa only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using
      congrArg Complex.re hM.1.trace_eq_sum_eigenvalues
  rw [ht, re_trace_contraction_defect hM.1]
  exact sum_contraction_defect_ge_fract Finset.univ _ (fun i _ =>
    ⟨hM.eigenvalues_nonneg i, positive_contraction_eigenvalues_le_one hM hC i⟩)

/-- The explicit fractional trace estimate used with `Tr(Λ̄) = n/d` in Appendix E. -/
theorem positive_contraction_rational_trace_bound {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) (hC : (1 - M).PosSemidef) (n d : ℕ)
    (ht : (Matrix.trace M).re = (n : ℝ) / d) :
    ((n % d : ℕ) : ℝ) / d * (1 - ((n % d : ℕ) : ℝ) / d)
      ≤ (Matrix.trace (M - M * M)).re := by
  have h := positive_contraction_fractional_trace_bound hM hC
  rwa [ht, Int.fract_div_natCast_eq_div_natCast_mod] at h

end

end CGLMPBounds
