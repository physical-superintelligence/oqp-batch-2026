module

public import VacuumBellSeparation.Gaussian.MultiModeBargmannPointwise
public import VacuumBellSeparation.Gaussian.MultiModeWeylRepresentation

@[expose] public section


/-!
# Actual finite-mode weak coherent resolution

Complex product Lebesgue measure and the normalization π^(-m/2) turn
coherent coordinates into an actual inner-product-preserving integral.
The theorem is a weak resolution, with explicit scalar integrability.
-/

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory
open scoped ComplexConjugate

def multiCoherentFrameCoordinate {m : ℕ} (x : MultiModeOscillatorSpace m) (z : Fin m → ℂ) : ℂ :=
  ((Real.sqrt Real.pi : ℂ) ^ m)⁻¹ *
    inner ℂ (multiCoherentVector (WithLp.toLp 2 z)) x

theorem multiBargmannPrefactor_eq {m : ℕ} (z : Fin m → ℂ) :
    multiBargmannPrefactor z =
      Complex.exp ((-(∑ j, ‖z j‖ ^ 2) / 2 : ℝ) : ℂ) / (Real.sqrt Real.pi : ℂ) ^ m := by
  simp only [multiBargmannPrefactor, Complex.ofReal_div, Complex.ofReal_exp,
    Finset.prod_div_distrib, ← Complex.exp_sum, ← Complex.ofReal_sum,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.sum_div,
    Finset.sum_neg_distrib]

theorem multiBargmannFunction_conj {m : ℕ} (x : MultiModeOscillatorSpace m) (z : Fin m → ℂ) :
    multiBargmannFunction x (fun j => conj (z j)) = multiCoherentFrameCoordinate x z := by
  rw [multiBargmannFunction, multiBargmannPrefactor_eq]
  simp only [Complex.norm_conj, starRingEnd_self_apply, multiCoherentFrameCoordinate,
    multiCoherentVector, inner_smul_left, ← Complex.exp_conj, Complex.conj_ofReal,
    EuclideanSpace.norm_sq_eq, PiLp.toLp_apply]
  ring

def multiConjugation (m : ℕ) : (Fin m → ℂ) ≃ᵐ (Fin m → ℂ) :=
  MeasurableEquiv.piCongrRight fun _ : Fin m => Complex.conjLIE.toHomeomorph.toMeasurableEquiv

@[simp] theorem multiConjugation_apply {m : ℕ} (z : Fin m → ℂ) :
    multiConjugation m z = fun j => conj (z j) := rfl

theorem multiConjugation_measurePreserving (m : ℕ) : MeasurePreserving (multiConjugation m) :=
  volume_preserving_pi (fun _ : Fin m => Complex.conjLIE.measurePreserving)

theorem integral_inner_multiCoherentFrameCoordinate {m : ℕ} (x y : MultiModeOscillatorSpace m) :
    (∫ z : Fin m → ℂ, inner ℂ (multiCoherentFrameCoordinate x z) (multiCoherentFrameCoordinate y z)) =
      inner ℂ x y := by
  have h := (multiConjugation_measurePreserving m).integral_comp
    (multiConjugation m).measurableEmbedding
    (fun z : Fin m → ℂ => inner ℂ (multiBargmannFunction x z) (multiBargmannFunction y z))
  simpa only [multiConjugation_apply, multiBargmannFunction_conj,
    integral_inner_multiBargmannFunction] using h

theorem integrable_inner_multiCoherentFrameCoordinate {m : ℕ} (x y : MultiModeOscillatorSpace m) :
    Integrable (fun z : Fin m → ℂ =>
      inner ℂ (multiCoherentFrameCoordinate x z) (multiCoherentFrameCoordinate y z)) := by
  have h := (multiConjugation_measurePreserving m).integrable_comp_of_integrable
    (integrable_inner_multiBargmannFunction x y)
  simpa only [Function.comp_def, multiConjugation_apply, multiBargmannFunction_conj] using h

theorem integral_multiCoherentFrameCoordinate_norm_sq {m : ℕ} (x : MultiModeOscillatorSpace m) :
    (∫ z : Fin m → ℂ, ‖multiCoherentFrameCoordinate x z‖ ^ 2) = ‖x‖ ^ 2 := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (integral_inner_multiCoherentFrameCoordinate x x)
  rw [← integral_re (integrable_inner_multiCoherentFrameCoordinate x x)] at h
  simpa only [inner_self_eq_norm_sq] using h

theorem integrable_multiCoherentFrameCoordinate_norm_sq {m : ℕ} (x : MultiModeOscillatorSpace m) :
    Integrable (fun z : Fin m → ℂ => ‖multiCoherentFrameCoordinate x z‖ ^ 2) := by
  have h := (integrable_inner_multiCoherentFrameCoordinate x x).re
  simpa only [inner_self_eq_norm_sq] using h

end VacuumBellSeparation.Gaussian
