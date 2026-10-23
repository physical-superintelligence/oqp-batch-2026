module

public import VacuumBellSeparation.Shell.FixedMassContourJacobian

@[expose] public section


/-!
# Exact reordering into Lorentz parameters and physical momenta

The active/auxiliary coordinates used by the inverse-function theorem
are a fixed invertible reordering of six Lorentz parameters and three
physical momenta, followed by translation of the second momentum by B.
No independence of Lorentz and momentum variables is assumed implicitly.
-/

namespace VacuumBellSeparation

abbrev LorentzMomentumParameters := (Fin 6 → ℝ) × EuclideanSpace ℝ (Fin 3)

noncomputable def contourParameterReorderLinear :
    ShellPhysicalParameters →ₗ[ℝ] LorentzMomentumParameters where
  toFun q := (![q.1 0, q.1 1, q.1 2, q.1 3, q.1 4, q.2 0],
    WithLp.toLp 2 ![q.2 1, q.1 5, q.2 2])
  map_add' x y := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  map_smul' a x := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

noncomputable def contourParameterReorder :
    ShellPhysicalParameters ≃L[ℝ] LorentzMomentumParameters :=
  ({ contourParameterReorderLinear with
      invFun q := (![q.1 0, q.1 1, q.1 2, q.1 3, q.1 4, q.2 1],
        ![q.1 5, q.2 0, q.2 2])
      left_inv q := by
        apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
      right_inv q := by
        apply Prod.ext <;> ext i <;> fin_cases i <;> rfl } :
      ShellPhysicalParameters ≃ₗ[ℝ] LorentzMomentumParameters).toContinuousLinearEquiv

noncomputable def physicalContourParameters (B : ℝ) (q : ShellPhysicalParameters) :
    LorentzMomentumParameters :=
  contourParameterReorder q + (0, WithLp.toLp 2 ![0, B, 0])

theorem physicalContourParameters_lorentz (B τ : ℝ) (q : ShellPhysicalParameters) :
    (physicalContourParameters B q).1 =
      fullContourLorentzParameters (fixedMassContourEmbedding τ q) := by
  ext i
  fin_cases i <;> simp [physicalContourParameters, contourParameterReorder,
    contourParameterReorderLinear, fullContourLorentzParameters, fixedMassContourEmbedding]

theorem physicalContourParameters_momentum (B τ : ℝ) (q : ShellPhysicalParameters) :
    (physicalContourParameters B q).2 =
      fullContourMomentum B (fixedMassContourEmbedding τ q) := by
  ext i
  fin_cases i <;> simp [physicalContourParameters, contourParameterReorder,
    contourParameterReorderLinear, fullContourMomentum, fixedMassContourEmbedding, add_comm]

theorem hasFDerivAt_physicalContourParameters (B : ℝ) (q : ShellPhysicalParameters) :
    HasFDerivAt (physicalContourParameters B)
      (contourParameterReorder : ShellPhysicalParameters →L[ℝ] LorentzMomentumParameters) q := by
  change HasFDerivAt (fun z : ShellPhysicalParameters =>
    contourParameterReorder z + (0, WithLp.toLp 2 ![0, B, 0]))
    (contourParameterReorder : ShellPhysicalParameters →L[ℝ] LorentzMomentumParameters) q
  exact (contourParameterReorder.hasFDerivAt (x := q)).add_const
    (0, WithLp.toLp 2 ![0, B, 0])

theorem physicalContourParameters_bijective (B : ℝ) :
    Function.Bijective (physicalContourParameters B) := by
  constructor
  · intro x y h
    exact contourParameterReorder.injective (add_right_cancel h)
  · intro y
    refine ⟨contourParameterReorder.symm (y - (0, WithLp.toLp 2 ![0, B, 0])), ?_⟩
    simp [physicalContourParameters]

theorem fixedMassContourMap_physical (m B θ τ : ℝ) (q : ShellPhysicalParameters) :
    (fixedMassContourMap m B θ τ q).1 = complexShellCoordinates
      (complexifiedSpacetimeMap
        (lorentzParameterFamily (physicalContourParameters B q).1)
        (complexShellBoost (m + τ) ((θ : ℂ) * Complex.I)
          (physicalContourParameters B q).2)) := by
  rw [physicalContourParameters_lorentz B τ, physicalContourParameters_momentum B τ]
  simp only [fixedMassContourMap, fullContourMap, complexLorentzFamilyAction,
    fullContourSeed_eq_boost, fixedMassContourEmbedding]

end VacuumBellSeparation
