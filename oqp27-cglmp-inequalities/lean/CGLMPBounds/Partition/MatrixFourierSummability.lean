module

public import CGLMPBounds.Defs.PartitionHardy
public import CGLMPBounds.Circulation.Core
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public section


/-! Convergence of the literal matrix negative Fourier energy. Mathlib's
actual interval Parseval theorem is applied to each matrix entry, then the
finite normalized Hilbert–Schmidt sum is assembled. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

lemma hsSq_eq_entry_sum {r : ℕ} (M : Circulation.Mat r) :
    Circulation.hsSq M = (∑ i : Fin r, ∑ j : Fin r, ‖M i j‖ ^ 2) / (r : ℝ) := by
  rw [Circulation.hsSq, Circulation.reTr_eq]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [Finset.sum_comm]

lemma negative_fourier_scalar_eq (f : ℝ → ℂ) (n : ℕ) :
    (∫ t in (0 : ℝ)..1,
      Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) * f t) =
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f (-((n + 1 : ℕ) : ℤ)) := by
  rw [fourierCoeffOn_eq_integral]
  norm_num only [sub_zero, one_div_one, one_smul, neg_neg]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [fourier_coe_apply]
  simp only [smul_eq_mul]
  congr 1
  congr 1
  push_cast
  ring

lemma matrixNegativeFourierCoefficient_apply {r : ℕ} (U : ℝ → Circulation.Mat r)
    (hU : Measurable U) (C : ℝ) (hbound : ∀ t, ‖U t‖ ≤ C) (n : ℕ) (i j : Fin r) :
    matrixNegativeFourierCoefficient U n i j =
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (fun t => U t i j)
        (-((n + 1 : ℕ) : ℤ)) := by
  letI : ENormedAddMonoid (Circulation.Mat r) :=
    inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))
  letI : TopologicalSpace.PseudoMetrizableSpace (Circulation.Mat r) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin r → Fin r → ℂ))
  letI : SecondCountableTopology (Circulation.Mat r) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → ℂ))
  let φ : ℝ → Circulation.Mat r := fun t =>
    Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) • U t
  have hm : Measurable φ := by dsimp [φ]; fun_prop
  have hb (t : ℝ) : ‖φ t‖ ≤ C := by
    dsimp only [φ]
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hbound t
  have hi : IntervalIntegrable φ volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    exact (integrable_const C).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  let L : Circulation.Mat r →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj j : (Fin r → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj i : (Fin r → Fin r → ℂ) →L[ℂ] (Fin r → ℂ))
  have he := L.intervalIntegral_comp_comm hi
  calc
    _ = ∫ t in (0 : ℝ)..1, φ t i j := by
      simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        matrixNegativeFourierCoefficient, φ] using! he.symm
    _ = _ := negative_fourier_scalar_eq (fun t => U t i j) n

/-- Genuine summability for any bounded measurable matrix function. No
unitarity, fourth-root property or assumed projection identity is needed. -/
theorem matrixNegativeFourierEnergy_summable_of_bounded {r : ℕ}
    (U : ℝ → Circulation.Mat r) (hU : Measurable U)
    (C : ℝ) (hbound : ∀ t, ‖U t‖ ≤ C) :
    Summable (fun n => Circulation.hsSq (matrixNegativeFourierCoefficient U n)) := by
  have hs (i j : Fin r) : Summable
      (fun n => ‖matrixNegativeFourierCoefficient U n i j‖ ^ 2) := by
    have hm : Measurable (fun t => U t i j) := by fun_prop
    have hlp : MemLp (fun t => U t i j) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
      MemLp.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall
        (fun t => (Matrix.norm_entry_le_entrywise_sup_norm (U t)).trans (hbound t)))
    have hall := (hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hlp).summable
    have hn : Function.Injective (fun n : ℕ => -((n + 1 : ℕ) : ℤ)) := by
      intro m n h
      change -((m + 1 : ℕ) : ℤ) = -((n + 1 : ℕ) : ℤ) at h
      omega
    have hsub := hall.comp_injective hn
    exact hsub.congr (fun n => by
      dsimp only [Function.comp_def]
      rw [matrixNegativeFourierCoefficient_apply U hU C hbound])
  have hsum : Summable (fun n => ∑ i : Fin r, ∑ j : Fin r,
      ‖matrixNegativeFourierCoefficient U n i j‖ ^ 2) :=
    summable_sum (fun i _ => summable_sum (fun j _ => hs i j))
  exact (hsum.div_const (r : ℝ)).congr (fun n => (hsSq_eq_entry_sum _).symm)

end
end CGLMPBounds.Partition
