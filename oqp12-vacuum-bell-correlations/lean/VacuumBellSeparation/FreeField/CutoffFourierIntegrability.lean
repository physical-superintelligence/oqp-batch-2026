module

public import VacuumBellSeparation.FreeField.CompactParameterContinuity

@[expose] public section


/-!
# Genuine Banach integrability of the cutoff Fourier kernel

Schwartz decay of the momentum test function controls the polynomial bounds
of every weighted-derivative coordinate. Thus the finite Banach-valued kernel
is Bochner integrable, and the actual distribution evaluation is integrable
after scalar multiplication by the momentum test function. The identification
of this integral with the Fourier transform is a separate step.
-/

open MeasureTheory
open scoped SchwartzMap BoundedContinuousFunction

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace VacuumBellSeparation

abbrev finitePiBanach_continuousENorm
    {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] :
    ContinuousENorm (∀ i, E i) := inferInstance

set_option maxHeartbeats 1600000 in
local instance (s : Finset (ℕ × ℕ)) : ContinuousENorm (SchwartzDerivativeBanach s) :=
  finitePiBanach_continuousENorm (ι := s)
    (E := fun i : s => EuclideanSpace ℝ (Fin 3) →ᵇ
      ContinuousMultilinearMap ℝ (fun _ : Fin i.val.2 => EuclideanSpace ℝ (Fin 3)) ℂ)

abbrev finitePiBanach_normedSpace
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] :
    NormedSpace ℂ (∀ i, E i) := inferInstance

set_option maxHeartbeats 1600000 in
local instance (s : Finset (ℕ × ℕ)) : NormedSpace ℂ (SchwartzDerivativeBanach s) :=
  finitePiBanach_normedSpace (ι := s)
    (E := fun i : s => EuclideanSpace ℝ (Fin 3) →ᵇ
      ContinuousMultilinearMap ℝ (fun _ : Fin i.val.2 => EuclideanSpace ℝ (Fin 3)) ℂ)

noncomputable def cutoffFourierSeminormBound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (k j : ℕ)
    (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
    ((2 * Real.pi * ‖innerSL ℝ (E := EuclideanSpace ℝ (Fin 3))‖) ^ i * ‖p‖ ^ i) *
      SchwartzMap.seminorm ℂ k (j - i) χ

theorem cutoffFourierSeminormBound_nonneg
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (k j : ℕ)
    (p : EuclideanSpace ℝ (Fin 3)) : 0 ≤ cutoffFourierSeminormBound χ k j p := by
  unfold cutoffFourierSeminormBound
  positivity

theorem integrable_norm_mul_cutoffFourierSeminormBound
    (ψ χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (k j : ℕ) :
    Integrable (fun p => ‖ψ p‖ * cutoffFourierSeminormBound χ k j p) := by
  simp only [cutoffFourierSeminormBound, Finset.mul_sum]
  apply integrable_finsetSum
  intro i hi
  have h := (ψ.integrable_pow_mul volume i).const_mul
    ((j.choose i : ℝ) *
      (2 * Real.pi * ‖innerSL ℝ (E := EuclideanSpace ℝ (Fin 3))‖) ^ i *
        SchwartzMap.seminorm ℂ k (j - i) χ)
  convert h using 1
  funext p
  ring

theorem norm_schwartzDerivativeMap_cutoffFourierKernel_le
    (s : Finset (ℕ × ℕ)) (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖schwartzDerivativeMap s (cutoffFourierKernel χ p)‖ ≤
      ∑ i ∈ s, cutoffFourierSeminormBound χ i.1 i.2 p := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i hi =>
    cutoffFourierSeminormBound_nonneg χ i.1 i.2 p)).mpr
  intro i
  change ‖schwartzWeightedDerivative i.val.1 i.val.2 (cutoffFourierKernel χ p)‖ ≤ _
  rw [norm_schwartzWeightedDerivative]
  exact (seminorm_cutoffFourierKernel_le χ p i.val.1 i.val.2).trans
    (Finset.single_le_sum (fun a ha => cutoffFourierSeminormBound_nonneg χ a.1 a.2 p) i.property)

set_option maxHeartbeats 1600000 in
/-- The integral lives in an actual complete normed vector space. -/
theorem integrable_schwartzDerivativeMap_cutoffFourierKernel
    (s : Finset (ℕ × ℕ))
    (ψ χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ) :
    Integrable (fun p => ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p)) := by
  classical
  have hmajorant : Integrable (fun p =>
      ∑ i ∈ s, ‖ψ p‖ * cutoffFourierSeminormBound χ i.1 i.2 p) :=
    integrable_finsetSum s (fun i hi =>
      integrable_norm_mul_cutoffFourierSeminormBound ψ χ i.1 i.2)
  apply hmajorant.mono'
    (f := fun p => ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p))
    ((ψ.continuous.smul
      (continuous_schwartzDerivativeMap_cutoffFourierKernel s χ hχ)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun p => by
    rw [← Finset.mul_sum]
    calc
      ‖ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p)‖ ≤
          ‖ψ p‖ * ‖schwartzDerivativeMap s (cutoffFourierKernel χ p)‖ :=
        norm_smul_le (ψ p) (schwartzDerivativeMap s (cutoffFourierKernel χ p))
      _ ≤ ‖ψ p‖ * ∑ i ∈ s, cutoffFourierSeminormBound χ i.1 i.2 p :=
        mul_le_mul_of_nonneg_left
          (norm_schwartzDerivativeMap_cutoffFourierKernel_le s χ p) (norm_nonneg _)

/-- The actual scalar distributional kernel pairing is absolutely integrable. -/
theorem integrable_distribution_cutoffFourierKernel
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (ψ χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ) :
    Integrable (fun p => ψ p * T (cutoffFourierKernel χ p)) := by
  obtain ⟨s, L, hL⟩ := temperedDistribution_banach_factorization T
  have h : Integrable (fun p => L (ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p))) :=
    ContinuousLinearMap.integrable_comp (μ := volume)
      (φ := fun p => ψ p • schwartzDerivativeMap s (cutoffFourierKernel χ p)) L
      (integrable_schwartzDerivativeMap_cutoffFourierKernel s ψ χ hχ)
  simpa only [Function.comp_def, map_smul, hL, smul_eq_mul] using h

end VacuumBellSeparation
