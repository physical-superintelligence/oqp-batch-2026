module

public import VacuumBellSeparation.Gaussian.SpatialPolydiscKernels
public import VacuumBellSeparation.Gaussian.PolydiscReconstruction

@[expose] public section


/-!
# Actual six-coordinate expansions of the separated covariance kernels

The two triples use their literal coordinate order. The coefficients are
the actual nested Cauchy integrals of the Bessel kernels; full HasSum and
absolute convergence follow from their proved closed-polydisc holomorphy.
-/

open scoped BigOperators

namespace VacuumBellSeparation.Gaussian

noncomputable def spatialSixPair (z : Fin 6 → ℂ) : SpatialComplexPair :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm
      (fun j => z (Fin.castAdd 3 j)),
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm
      (fun j => z (Fin.natAdd 3 j)))

theorem differentiable_spatialSixPair : Differentiable ℂ spatialSixPair := by
  apply Differentiable.prodMk
  · apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.differentiable.comp
    fun_prop
  · apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.differentiable.comp
    fun_prop

theorem spatialSixPair_mem_polydisc {R : ℝ} {z : Fin 6 → ℂ}
    (hz : z ∈ coordinateClosedPolydisc 6 R) : spatialSixPair z ∈ spatialClosedPolydisc R :=
  ⟨fun j => hz (Fin.castAdd 3 j), fun j => hz (Fin.natAdd 3 j)⟩

noncomputable def spatialSixFieldKernel (μ s : ℝ) (z : Fin 6 → ℂ) : ℂ :=
  spatialPairFieldKernel μ s (spatialSixPair z)

noncomputable def spatialSixMomentumKernel (μ s : ℝ) (z : Fin 6 → ℂ) : ℂ :=
  spatialPairMomentumKernel μ s (spatialSixPair z)

noncomputable def spatialFieldCoefficient (μ s R : ℝ) (k : Fin 6 → ℕ) : ℂ :=
  polydiscCoefficient 6 R (spatialSixFieldKernel μ s) k

noncomputable def spatialMomentumCoefficient (μ s R : ℝ) (k : Fin 6 → ℕ) : ℂ :=
  polydiscCoefficient 6 R (spatialSixMomentumKernel μ s) k

noncomputable def spatialFieldPolydiscBound (μ s R : ℝ) : ℝ :=
  (6 / s ^ 2) * Real.sqrt (1 + μ * s) * Real.exp (-μ * s + 4 * μ * Real.sqrt 3 * R)

noncomputable def spatialMomentumPolydiscBound (μ s R : ℝ) : ℝ :=
  (128 / s ^ 4) * (1 + μ * s) * Real.sqrt (1 + μ * s) *
    Real.exp (-μ * s + 4 * μ * Real.sqrt 3 * R)

theorem spatialSixFieldKernel_differentiable {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 ≤ R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (z : Fin 6 → ℂ) (hz : z ∈ coordinateClosedPolydisc 6 R) :
    DifferentiableAt ℂ (spatialSixFieldKernel μ s) z :=
  (differentiableAt_spatialPairFieldKernel hμ hs hR hsep (spatialSixPair_mem_polydisc hz)).comp z
    (differentiable_spatialSixPair z)

theorem spatialSixMomentumKernel_differentiable {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 ≤ R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (z : Fin 6 → ℂ) (hz : z ∈ coordinateClosedPolydisc 6 R) :
    DifferentiableAt ℂ (spatialSixMomentumKernel μ s) z :=
  (differentiableAt_spatialPairMomentumKernel hμ hs hR hsep (spatialSixPair_mem_polydisc hz)).comp z
    (differentiable_spatialSixPair z)

theorem spatialSixFieldKernel_norm_le {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 ≤ R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (z : Fin 6 → ℂ) (hz : z ∈ coordinateClosedPolydisc 6 R) :
    ‖spatialSixFieldKernel μ s z‖ ≤ spatialFieldPolydiscBound μ s R :=
  spatialPairFieldKernel_norm_le hμ hs hR hsep (spatialSixPair_mem_polydisc hz)

theorem spatialSixMomentumKernel_norm_le {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 ≤ R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (z : Fin 6 → ℂ) (hz : z ∈ coordinateClosedPolydisc 6 R) :
    ‖spatialSixMomentumKernel μ s z‖ ≤ spatialMomentumPolydiscBound μ s R :=
  spatialPairMomentumKernel_norm_le hμ hs hR hsep (spatialSixPair_mem_polydisc hz)

theorem spatialFieldCoefficient_norm_le {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (k : Fin 6 → ℕ) :
    ‖spatialFieldCoefficient μ s R k‖ ≤ spatialFieldPolydiscBound μ s R * R⁻¹ ^ (∑ j, k j) := by
  simpa only [spatialFieldCoefficient, Finset.prod_pow_eq_pow_sum] using
    polydiscCoefficient_norm_le 6 hR
      (show 0 ≤ spatialFieldPolydiscBound μ s R by unfold spatialFieldPolydiscBound; positivity)
      (spatialSixFieldKernel μ s) (spatialSixFieldKernel_norm_le hμ hs hR.le hsep) k

theorem spatialMomentumCoefficient_norm_le {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (k : Fin 6 → ℕ) :
    ‖spatialMomentumCoefficient μ s R k‖ ≤
      spatialMomentumPolydiscBound μ s R * R⁻¹ ^ (∑ j, k j) := by
  simpa only [spatialMomentumCoefficient, Finset.prod_pow_eq_pow_sum] using
    polydiscCoefficient_norm_le 6 hR
      (show 0 ≤ spatialMomentumPolydiscBound μ s R by unfold spatialMomentumPolydiscBound; positivity)
      (spatialSixMomentumKernel μ s) (spatialSixMomentumKernel_norm_le hμ hs hR.le hsep) k

theorem spatialFieldCoefficient_expansion {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (z : Fin 6 → ℂ) (hz : ∀ j, ‖z j‖ < R) :
    HasSum (fun k : Fin 6 → ℕ => spatialFieldCoefficient μ s R k * ∏ j, z j ^ k j)
        (spatialSixFieldKernel μ s z) ∧
      Summable (fun k : Fin 6 → ℕ => ‖spatialFieldCoefficient μ s R k * ∏ j, z j ^ k j‖) :=
  polydiscCoefficient_expansion 6 (M := spatialFieldPolydiscBound μ s R) hR
    (by unfold spatialFieldPolydiscBound; positivity) (spatialSixFieldKernel μ s)
    (spatialSixFieldKernel_differentiable hμ hs hR.le hsep)
    (spatialSixFieldKernel_norm_le hμ hs hR.le hsep) z hz

theorem spatialMomentumCoefficient_expansion {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (z : Fin 6 → ℂ) (hz : ∀ j, ‖z j‖ < R) :
    HasSum (fun k : Fin 6 → ℕ => spatialMomentumCoefficient μ s R k * ∏ j, z j ^ k j)
        (spatialSixMomentumKernel μ s z) ∧
      Summable (fun k : Fin 6 → ℕ => ‖spatialMomentumCoefficient μ s R k * ∏ j, z j ^ k j‖) :=
  polydiscCoefficient_expansion 6 (M := spatialMomentumPolydiscBound μ s R) hR
    (by unfold spatialMomentumPolydiscBound; positivity) (spatialSixMomentumKernel μ s)
    (spatialSixMomentumKernel_differentiable hμ hs hR.le hsep)
    (spatialSixMomentumKernel_norm_le hμ hs hR.le hsep) z hz

end VacuumBellSeparation.Gaussian
