module

public import VacuumBellSeparation.Shell.CoordinateLorentzProper
public import VacuumBellSeparation.Shell.LorentzFrameMatching

@[expose] public section


/-!
# A literal six-parameter proper future Lorentz family

The factors are the three actual coordinate boosts and three coordinate
plane rotations. The order is chosen to match the six selected contour
variations: boost1, boost2, rotation12, rotation13, rotation23, boost3.
Spatial conjugation preserves determinant without requiring the spatial
permutation itself to have positive determinant.
-/

namespace VacuumBellSeparation

noncomputable def spatialLorentzConjugate
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (Λ : Spacetime ≃L[ℝ] Spacetime) : Spacetime ≃L[ℝ] Spacetime :=
  (spatialRotation R).symm.trans (Λ.trans (spatialRotation R))

theorem spatialLorentzConjugate_apply
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (Λ : Spacetime ≃L[ℝ] Spacetime) (x : Spacetime) :
    spatialLorentzConjugate R Λ x = spatialRotation R (Λ (x.1, R.symm x.2)) := rfl

theorem spatialLorentzConjugate_isProper
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    {Λ : Spacetime ≃L[ℝ] Spacetime} (hΛ : IsProperLorentzMap Λ) :
    IsProperLorentzMap (spatialLorentzConjugate R Λ) := by
  refine ⟨(isLorentzMap_spatialRotation R).symm.trans
    (hΛ.1.trans (isLorentzMap_spatialRotation R)), ?_⟩
  change LinearMap.det
    (((spatialRotation R).toLinearEquiv.toLinearMap.comp Λ.toLinearEquiv.toLinearMap).comp
      (spatialRotation R).symm.toLinearEquiv.toLinearMap) = 1
  rw [LinearMap.det_comp, LinearMap.det_comp, hΛ.2, mul_one]
  exact (spatialRotation R).toLinearEquiv.det_mul_det_symm

theorem spatialLorentzConjugate_isOrthochronous
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    {Λ : Spacetime ≃L[ℝ] Spacetime} (hΛ : IsOrthochronousMap Λ) :
    IsOrthochronousMap (spatialLorentzConjugate R Λ) := by
  simpa only [IsOrthochronousMap, spatialLorentzConjugate_apply,
    map_zero, spatialRotation_apply] using hΛ

noncomputable def coordinateBoost2 (η : ℝ) : Spacetime ≃L[ℝ] Spacetime :=
  spatialLorentzConjugate (spatialCoordinatePermutation (Equiv.swap 0 1)) (boost η)

noncomputable def coordinateBoost3 (η : ℝ) : Spacetime ≃L[ℝ] Spacetime :=
  spatialLorentzConjugate (spatialCoordinatePermutation (Equiv.swap 0 2)) (boost η)

noncomputable def coordinateLorentzRotation13 (θ : ℝ) : Spacetime ≃L[ℝ] Spacetime :=
  spatialLorentzConjugate (spatialCoordinatePermutation (Equiv.swap 1 2))
    (spatialRotation (spatialPlaneRotation θ))

noncomputable def coordinateLorentzRotation23 (θ : ℝ) : Spacetime ≃L[ℝ] Spacetime :=
  spatialLorentzConjugate (spatialCoordinatePermutation (Equiv.swap 0 1))
    (coordinateLorentzRotation13 θ)

theorem coordinateLorentzRotation13_eq (θ : ℝ) :
    coordinateLorentzRotation13 θ = spatialRotation (spatialPlaneRotation13 θ) := by
  apply ContinuousLinearEquiv.ext
  funext x
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> simp [coordinateLorentzRotation13, spatialLorentzConjugate_apply,
      spatialRotation_apply, spatialCoordinatePermutation, spatialPlaneRotation_apply,
      spatialPlaneRotation13_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft', Equiv.swap_apply_def]

theorem coordinateLorentzRotation23_eq (θ : ℝ) :
    coordinateLorentzRotation23 θ = spatialRotation (spatialPlaneRotation23 θ) := by
  apply ContinuousLinearEquiv.ext
  funext x
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> simp [coordinateLorentzRotation23, spatialLorentzConjugate_apply,
      coordinateLorentzRotation13_eq, spatialRotation_apply, spatialCoordinatePermutation,
      spatialPlaneRotation13_apply, spatialPlaneRotation23_apply,
      LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', Equiv.swap_apply_def]

noncomputable def lorentzParameterFactor (j : Fin 6) (s : ℝ) :
    Spacetime ≃L[ℝ] Spacetime :=
  ![boost s, coordinateBoost2 s, spatialRotation (spatialPlaneRotation s),
    coordinateLorentzRotation13 s, coordinateLorentzRotation23 s, coordinateBoost3 s] j

theorem lorentzParameterFactor_isProper (j : Fin 6) (s : ℝ) :
    IsProperLorentzMap (lorentzParameterFactor j s) := by
  fin_cases j
  · exact isProperLorentzMap_boost s
  · exact spatialLorentzConjugate_isProper _ (isProperLorentzMap_boost s)
  · exact isProperLorentzMap_spatialPlaneRotation s
  · exact spatialLorentzConjugate_isProper _ (isProperLorentzMap_spatialPlaneRotation s)
  · exact spatialLorentzConjugate_isProper _
      (spatialLorentzConjugate_isProper _ (isProperLorentzMap_spatialPlaneRotation s))
  · exact spatialLorentzConjugate_isProper _ (isProperLorentzMap_boost s)

theorem lorentzParameterFactor_isOrthochronous (j : Fin 6) (s : ℝ) :
    IsOrthochronousMap (lorentzParameterFactor j s) := by
  fin_cases j
  · exact isOrthochronousMap_boost s
  · exact spatialLorentzConjugate_isOrthochronous _ (isOrthochronousMap_boost s)
  · exact isOrthochronousMap_spatialRotation _
  · exact spatialLorentzConjugate_isOrthochronous _ (isOrthochronousMap_spatialRotation _)
  · exact spatialLorentzConjugate_isOrthochronous _
      (spatialLorentzConjugate_isOrthochronous _ (isOrthochronousMap_spatialRotation _))
  · exact spatialLorentzConjugate_isOrthochronous _ (isOrthochronousMap_boost s)

theorem lorentzParameterFactor_zero (j : Fin 6) :
    lorentzParameterFactor j 0 = ContinuousLinearEquiv.refl ℝ Spacetime := by
  apply ContinuousLinearEquiv.ext
  funext x
  fin_cases j <;>
    simp [lorentzParameterFactor, coordinateBoost2, coordinateBoost3,
      coordinateLorentzRotation13, coordinateLorentzRotation23,
      spatialLorentzConjugate_apply, boost_apply, boostCLM_zero,
      spatialRotation_apply, spatialPlaneRotation_zero]

noncomputable def lorentzParameterFamily (s : Fin 6 → ℝ) :
    Spacetime ≃L[ℝ] Spacetime :=
  (lorentzParameterFactor 0 (s 0)).trans
    ((lorentzParameterFactor 1 (s 1)).trans
      ((lorentzParameterFactor 2 (s 2)).trans
        ((lorentzParameterFactor 3 (s 3)).trans
          ((lorentzParameterFactor 4 (s 4)).trans (lorentzParameterFactor 5 (s 5))))))

theorem lorentzParameterFamily_isProper (s : Fin 6 → ℝ) :
    IsProperLorentzMap (lorentzParameterFamily s) :=
  (lorentzParameterFactor_isProper 0 _).trans
    ((lorentzParameterFactor_isProper 1 _).trans
      ((lorentzParameterFactor_isProper 2 _).trans
        ((lorentzParameterFactor_isProper 3 _).trans
          ((lorentzParameterFactor_isProper 4 _).trans (lorentzParameterFactor_isProper 5 _)))))

theorem lorentzParameterFamily_isOrthochronous (s : Fin 6 → ℝ) :
    IsOrthochronousMap (lorentzParameterFamily s) := by
  have hc {Λ Γ : Spacetime ≃L[ℝ] Spacetime}
      (hΛ : IsLorentzMap Λ ∧ IsOrthochronousMap Λ)
      (hΓ : IsLorentzMap Γ ∧ IsOrthochronousMap Γ) :
      IsLorentzMap (Λ.trans Γ) ∧ IsOrthochronousMap (Λ.trans Γ) :=
    ⟨hΛ.1.trans hΓ.1, IsOrthochronousMap.trans hΛ.1 hΓ.1 hΛ.2 hΓ.2⟩
  have hj (j : Fin 6) : IsLorentzMap (lorentzParameterFactor j (s j)) ∧
      IsOrthochronousMap (lorentzParameterFactor j (s j)) :=
    ⟨(lorentzParameterFactor_isProper j (s j)).1,
      lorentzParameterFactor_isOrthochronous j (s j)⟩
  exact (hc (hj 0) (hc (hj 1) (hc (hj 2) (hc (hj 3) (hc (hj 4) (hj 5)))))).2

theorem lorentzParameterFamily_zero :
    lorentzParameterFamily 0 = ContinuousLinearEquiv.refl ℝ Spacetime := by
  apply ContinuousLinearEquiv.ext
  funext x
  simp [lorentzParameterFamily, lorentzParameterFactor_zero]

end VacuumBellSeparation
