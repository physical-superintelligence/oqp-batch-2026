module

public import ThreeCopyQutritWerner.CoherentPencilMinors
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section


/-! An explicit infinite family of actual unit complex phases. -/

noncomputable section

namespace ThreeCopyQutritWerner

/-- The real Cayley parameterization, avoiding any selected finite phase set. -/
def coherentUnitPhase (t : ℝ) : ℂ :=
  (1 + (t : ℂ) * Complex.I) / (1 - (t : ℂ) * Complex.I)

/-- The actual denominator never vanishes on the real parameter line. -/
theorem coherentUnitPhase_denominator_ne_zero (t : ℝ) :
    1 - (t : ℂ) * Complex.I ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr

/-- Every parameter gives an actual phase of norm squared one. -/
theorem coherentUnitPhase_normSq (t : ℝ) : Complex.normSq (coherentUnitPhase t) = 1 := by
  have hn : Complex.normSq (1 + (t : ℂ) * Complex.I) = 1 + t ^ 2 := by
    simp [Complex.normSq_apply, pow_two]
  have hd : Complex.normSq (1 - (t : ℂ) * Complex.I) = 1 + t ^ 2 := by
    simp [Complex.normSq_apply, pow_two]
  rw [coherentUnitPhase, Complex.normSq_div, hn, hd]
  exact div_self (by positivity)

/-- The real parameterization is injective. -/
theorem coherentUnitPhase_injective : Function.Injective coherentUnitPhase := by
  intro t u h
  have hh := (div_eq_div_iff (coherentUnitPhase_denominator_ne_zero t)
    (coherentUnitPhase_denominator_ne_zero u)).mp h
  have hi := congrArg Complex.im hh
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.one_re, Complex.one_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at hi
  nlinarith

/-- The complete unit-phase locus is infinite, as required by the minor argument. -/
theorem coherentUnitPhases_infinite : {z : ℂ | Complex.normSq z = 1}.Infinite := by
  apply (Set.infinite_range_of_injective coherentUnitPhase_injective).mono
  rintro z ⟨t, rfl⟩
  exact coherentUnitPhase_normSq t

end ThreeCopyQutritWerner
