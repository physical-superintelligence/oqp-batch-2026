module

public import ThreeCopyQutritWerner.SharpCrossSupport
public import ThreeCopyQutritWerner.SharpFamilyRotation

@[expose] public section


/-!
# Pair support for arbitrary saturated orthonormal families

The common-null determinant argument and crossed-pair rigidity depend on
actual orthonormality and full gamma-one equality. They therefore apply after
every simultaneous unitary mixing, without identifying the mixed vectors as
the eigenvectors selected by a new singular-value decomposition.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate Kronecker

namespace ThreeCopyQutritWerner

theorem sharpFamily_norm_one {ι n : Type*} [Fintype n] [DecidableEq ι]
    (u : ι → n → ℂ) (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0)
    (i : ι) : vecNormSq (u i) = 1 := by
  have h := hu i i
  rw [if_pos rfl, braket_self] at h
  exact_mod_cast h

/-- Full gamma-one equality gives every polarized tensor relation for an
arbitrary original orthonormal pair of families. -/
theorem sharpGammaFamily_polarized_null
    {ι L R : Type*} [Fintype ι] [Fintype L] [Fintype R]
    [DecidableEq ι] [DecidableEq L] [DecidableEq R]
    (u v : ι → L × R → ℂ)
    (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0)
    (hv : ∀ i j, braket (v i) (v j) = if i = j then 1 else 0)
    (hg : ∀ i j, sharpPartialTraceGamma (u i) (v i) (u j) (v j) = 1)
    (i j : ι) :
    sharpDoubleAnti (sharpTensorRay (u i) (v j) + sharpTensorRay (u j) (v i)) = 0 := by
  by_cases hij : i = j
  · subst j
    have h := sharpPartialTraceGamma_diagonal_eq_one_null (u i) (v i)
      (sharpFamily_norm_one u hu i) (sharpFamily_norm_one v hv i) (hg i i)
    rw [sharpDoubleAnti_add, h, add_zero]
  · exact sharpPartialTraceGamma_offdiagonal_eq_one_null _ _ _ _
      (sharpFamily_norm_one u hu i) (sharpFamily_norm_one v hv i)
      (sharpFamily_norm_one u hu j) (sharpFamily_norm_one v hv j)
      (by rw [hu, if_neg hij]) (hg i j)

/-- Every common complex combination has singular reshape, also for families
obtained by a simultaneous coefficient rotation. -/
theorem sharpGammaFamily_common_reshape_det_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → Fin 3 × Fin 3 → ℂ)
    (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0)
    (hv : ∀ i j, braket (v i) (v j) = if i = j then 1 else 0)
    (hg : ∀ i j, sharpPartialTraceGamma (u i) (v i) (u j) (v j) = 1)
    (z : ι → ℂ) : (sharpReshape (fun r => ∑ i, z i * u i r)).det = 0 := by
  classical
  by_cases hz : z = 0
  · have he : sharpReshape (fun r => ∑ i, z i * u i r) =
        (0 : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext r s
      change (∑ i, z i * u i (r, s)) = 0
      simp [hz]
    rw [he, Matrix.det_zero]
  · have hn := sharp_orthonormal_combination_ne_zero v hv z hz
    have hB : sharpReshape (fun r => ∑ i, z i * v i r) ≠ 0 := by
      intro h
      apply hn
      funext ⟨i, j⟩
      exact congrFun (congrFun h i) j
    apply sharpPolarizedMinor_det_eq_zero _ _ hB
    apply (sharpDoubleAnti_tensor_null_iff _ _).mp
    exact sharpDoubleAnti_common_combination_null u v
      (sharpGammaFamily_polarized_null u v hu hv hg) z

/-- Every distinct pair in an arbitrary orthonormal gamma-one family has
constructed common local support for all four original vectors. -/
theorem sharpGammaFamily_pair_exists_thin_coordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → Fin 3 × Fin 3 → ℂ)
    (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0)
    (hv : ∀ i j, braket (v i) (v j) = if i = j then 1 else 0)
    (hg : ∀ i j, sharpPartialTraceGamma (u i) (v i) (u j) (v j) = 1)
    (i j : ι) (hij : i ≠ j) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧ ∀ r s : Fin 3, r = a ∨ s = a →
        ((U ⊗ₖ V) *ᵥ u i) (r, s) = 0 ∧ ((U ⊗ₖ V) *ᵥ u j) (r, s) = 0 ∧
        ((U ⊗ₖ V) *ᵥ v i) (r, s) = 0 ∧ ((U ⊗ₖ V) *ᵥ v j) (r, s) = 0 := by
  let Y := sharpCrossDifference (u i) (v i) (u j) (v j)
  have ho : braket (u i) (u j) = 0 := by rw [hu, if_neg hij]
  have hn : frobSq Y = 2 := sharpCrossDifference_frobSq _ _ _ _
    (sharpFamily_norm_one u hu i) (sharpFamily_norm_one v hv i)
    (sharpFamily_norm_one u hu j) (sharpFamily_norm_one v hv j) ho
  have hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2 := by
    rw [hn]
    have h := sharpCrossDifference_projection_frobSq _ _ _ _
      (sharpFamily_norm_one u hu i) (sharpFamily_norm_one v hv i)
      (sharpFamily_norm_one u hu j) (sharpFamily_norm_one v hv j) ho (hg i j)
    simpa using h
  have hrange (z : Fin 3 × Fin 3 → ℂ) : (sharpReshape (Y *ᵥ z)).det = 0 := by
    change (sharpReshape (sharpCrossDifference (u i) (v i) (u j) (v j) *ᵥ z)).det = 0
    rw [sharpCrossDifference_mulVec]
    have h := sharpGammaFamily_common_reshape_det_zero u v hu hv hg
      (fun k => (if k = i then ∑ q, v j q * z q else 0) +
        (if k = j then -(∑ q, v i q * z q) else 0))
    simpa only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] using h
  obtain ⟨U, V, a, hU, hV, hsupport⟩ := sharpDoubleAnti_saturation_exists_thin_normal Y
    (sharpCrossDifference_rank_le_two _ _ _ _) hs (by rw [hn]; norm_num) hrange
  have hW := sharpLocalCongruence_unitary U V hU hV
  refine ⟨U, V, a, hU, hV, ?_⟩
  intro r s hrs
  apply sharpCrossDifference_zero_row_column
    ((U ⊗ₖ V) *ᵥ u i) ((U ⊗ₖ V) *ᵥ v i)
    ((U ⊗ₖ V) *ᵥ u j) ((U ⊗ₖ V) *ᵥ v j)
  · rw [singular_braket_isometry _ hW, hu, if_pos rfl]
  · rw [singular_braket_isometry _ hW, hu, if_pos rfl]
  · rw [singular_braket_isometry _ hW, hu, if_neg hij]
  · rw [singular_braket_isometry _ hW, hv, if_pos rfl]
  · rw [singular_braket_isometry _ hW, hv, if_pos rfl]
  · rw [singular_braket_isometry _ hW, hv, if_neg hij]
  · intro p
    simpa only [Y, sharpCrossDifference_congruence] using hsupport r s p hrs

/-- Actual singular families retain pairwise common support after every
common coefficient unitary, with no new singular-family premise. -/
theorem sharpPartialTrace_rotated_pair_exists_thin_coordinates
    (X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hsat : frobSq (ptraceL X) + frobSq (ptraceR X) =
      nuclearTrace X ^ 2 + Complex.normSq X.trace)
    (W : Matrix (SingularPositiveIndex X) (SingularPositiveIndex X) ℂ)
    (hW : Wᴴ * W = 1) (i j : SingularPositiveIndex X) (hij : i ≠ j) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧ ∀ r s : Fin 3, r = a ∨ s = a →
        ((U ⊗ₖ V) *ᵥ sharpRotateFamily W (singularLeft X) i) (r, s) = 0 ∧
        ((U ⊗ₖ V) *ᵥ sharpRotateFamily W (singularLeft X) j) (r, s) = 0 ∧
        ((U ⊗ₖ V) *ᵥ sharpRotateFamily W (singularRight X) i) (r, s) = 0 ∧
        ((U ⊗ₖ V) *ᵥ sharpRotateFamily W (singularRight X) j) (r, s) = 0 :=
  sharpGammaFamily_pair_exists_thin_coordinates _ _
    (sharpRotateFamily_braket W hW _ (singularLeft_braket X))
    (sharpRotateFamily_braket W hW _ (singularRight_braket X))
    (sharpRotateFamily_gamma_eq_one W hW _ _ (singularLeft_braket X)
      (singularRight_braket X) (sharpPartialTrace_singular_gamma_eq_one X hsat)) i j hij

end ThreeCopyQutritWerner
