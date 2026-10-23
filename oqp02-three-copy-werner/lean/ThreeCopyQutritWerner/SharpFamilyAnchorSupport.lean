module

public import ThreeCopyQutritWerner.SharpGammaFamilySupport
public import ThreeCopyQutritWerner.SharpFamilyAnchor
public import ThreeCopyQutritWerner.SharpSupportAnchor

@[expose] public section


/-!
# Common family support in the rank-two reshape branch

A rank-two member fixes its column plane. Every other member of both
orthonormal gamma-one families belongs to that plane by pairwise rigidity.
An actual coefficient unitary places any rank-two combination in this
anchor slot, and inverting that unitary recovers the original whole-family
annihilator. The all-rank-one combination branch is separate.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate Kronecker

namespace ThreeCopyQutritWerner

/-- A rank-two reshape member fixes one common local column plane for both
entire families, provided a second family member exists. -/
theorem sharpGammaFamily_rank_two_anchor_common_coordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → Fin 3 × Fin 3 → ℂ)
    (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0)
    (hv : ∀ i j, braket (v i) (v j) = if i = j then 1 else 0)
    (hg : ∀ i j, sharpPartialTraceGamma (u i) (v i) (u j) (v j) = 1)
    (i j : ι) (hij : i ≠ j) (hi : (sharpReshape (u i)).rank = 2) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3, Uᴴ * U = 1 ∧
      ∀ k c, (U * sharpReshape (u k)) a c = 0 ∧ (U * sharpReshape (v k)) a c = 0 := by
  obtain ⟨U, V, a, hU, hV, hs⟩ :=
    sharpGammaFamily_pair_exists_thin_coordinates u v hu hv hg i j hij
  have hbaseu : ∀ c, (U * sharpReshape (u i)) a c = 0 := by
    intro c
    apply sharpUnitaryTranspose_zero_row_cancel _ U V hV a ?_ c
    intro q
    rw [← sharpReshape_kronecker_mulVec]
    exact (hs a q (Or.inl rfl)).1
  have hbasev : ∀ c, (U * sharpReshape (v i)) a c = 0 := by
    intro c
    apply sharpUnitaryTranspose_zero_row_cancel _ U V hV a ?_ c
    intro q
    rw [← sharpReshape_kronecker_mulVec]
    exact (hs a q (Or.inl rfl)).2.2.1
  refine ⟨U, a, hU, ?_⟩
  intro k c
  by_cases hki : k = i
  · subst k
    exact ⟨hbaseu c, hbasev c⟩
  · obtain ⟨S, T, b, hS, hT, hk⟩ :=
      sharpGammaFamily_pair_exists_thin_coordinates u v hu hv hg i k (Ne.symm hki)
    have hleft := sharpPhysicalSupport_range_le_anchor (u i) (u k) hi S T hS hT b
      (fun q => (hk b q (Or.inl rfl)).1) (fun q => (hk b q (Or.inl rfl)).2.1)
    have hright := sharpPhysicalSupport_range_le_anchor (u i) (v k) hi S T hS hT b
      (fun q => (hk b q (Or.inl rfl)).1) (fun q => (hk b q (Or.inl rfl)).2.2.2)
    exact ⟨sharpSupport_zero_row_of_range_le _ _ U a hbaseu hleft c,
      sharpSupport_zero_row_of_range_le _ _ U a hbaseu hright c⟩

/-- Undoing the actual coefficient unitary preserves a common local
annihilator of every rotated family vector. -/
theorem sharpRotateFamily_zero_row_of_rotated
    {ι L R : Type*} [Fintype ι] [Fintype L] [DecidableEq ι]
    (W : Matrix ι ι ℂ) (hW : Wᴴ * W = 1) (u : ι → L × R → ℂ)
    (T : Matrix L L ℂ) (a : L)
    (hz : ∀ k c, (T * sharpReshape (sharpRotateFamily W u k)) a c = 0) :
    ∀ i c, (T * sharpReshape (u i)) a c = 0 := by
  have hWW : W * Wᴴ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl ι)).mp hW
  have hrec : sharpFamilyMatrix (sharpRotateFamily W u) * Wᴴ = sharpFamilyMatrix u := by
    change (sharpFamilyMatrix u * W) * Wᴴ = sharpFamilyMatrix u
    rw [Matrix.mul_assoc, hWW, Matrix.mul_one]
  have he (i : ι) (r : L × R) : u i r =
      ∑ k, conj (W i k) * sharpRotateFamily W u k r := by
    have h := congrFun (congrFun hrec r) i
    simpa only [sharpFamilyMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      starRingEnd_apply, mul_comm] using h.symm
  intro i c
  change (∑ r, T a r * u i (r, c)) = 0
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ k, conj (W i k) * (T * sharpReshape (sharpRotateFamily W u k)) a c := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [Matrix.mul_apply, sharpReshape, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = 0 := by simp only [hz, mul_zero, Finset.sum_const_zero]

/-- Any actual rank-two reshape combination produces one common physical
annihilator for both complete original gamma-one families. The unitary
mixing, normalized anchor and support are all constructed. -/
theorem sharpGammaFamily_rank_two_combination_common_coordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → Fin 3 × Fin 3 → ℂ)
    (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0)
    (hv : ∀ i j, braket (v i) (v j) = if i = j then 1 else 0)
    (hg : ∀ i j, sharpPartialTraceGamma (u i) (v i) (u j) (v j) = 1)
    (i j : ι) (hij : i ≠ j) (z : ι → ℂ)
    (hz : (sharpReshape (fun r => ∑ k, z k * u k r)).rank = 2) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3, Uᴴ * U = 1 ∧
      ∀ k c, (U * sharpReshape (u k)) a c = 0 ∧ (U * sharpReshape (v k)) a c = 0 := by
  obtain ⟨W, hW, hanchor⟩ := sharpFamily_exists_rank_two_anchor u z hz i
  obtain ⟨U, a, hU, hs⟩ := sharpGammaFamily_rank_two_anchor_common_coordinates
    (sharpRotateFamily W u) (sharpRotateFamily W v)
    (sharpRotateFamily_braket W hW u hu) (sharpRotateFamily_braket W hW v hv)
    (sharpRotateFamily_gamma_eq_one W hW u v hu hv hg) i j hij hanchor
  have hleft := sharpRotateFamily_zero_row_of_rotated W hW u U a (fun k c => (hs k c).1)
  have hright := sharpRotateFamily_zero_row_of_rotated W hW v U a (fun k c => (hs k c).2)
  exact ⟨U, a, hU, fun k c => ⟨hleft k c, hright k c⟩⟩

end ThreeCopyQutritWerner
