module

public import ThreeCopyQutritWerner.ThinOffplaneFamily
public import ThreeCopyQutritWerner.ThinPencilPlaneFamily
public import ThreeCopyQutritWerner.CoherentCommonPlanesCarrier

@[expose] public section


/-!
# Complete classification from the actual thin-factor reduction

All exceptional branches use the original family classification. Otherwise
both input and output share the first coordinate plane and two constructed
retained-site planes, giving the original binary carrier.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem twoSiteFactorFlatten_rank_le_joint_left
    (A B : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ) :
    (twoSiteFactorFlatten A).rank ≤ (twoSiteJointFactorFlatten A B).rank := by
  have he : twoSiteFactorFlatten A =
      (twoSiteJointFactorFlatten A B).submatrix id Sum.inl := rfl
  rw [he]
  exact Matrix.rank_submatrix_le _ _ _

theorem firstSite_zero_block_columns_in_coordinate_plane
    (X : Matrix QutritSites (Fin 2) ℂ) (h2 : firstSiteFactorBlock X 2 = 0) :
    ∀ j, (coherentFlatten₁ X).col j ∈
      LinearMap.range (sharpCoordinatePlaneProjection 2).mulVecLin := by
  have he : sharpCoordinatePlaneProjection 2 * coherentFlatten₁ X = coherentFlatten₁ X := by
    apply sharpCoordinatePlaneProjection_mul
    intro j
    exact congrFun (congrFun h2 j.1) j.2
  intro j
  refine ⟨(coherentFlatten₁ X).col j, ?_⟩
  ext i
  exact congrFun (congrFun he i) j

theorem isQutritZeroFamilyMember_of_thin_factor_bounds
    (X Y : Matrix QutritSites (Fin 2) ℂ) (hX : X.rank = 2)
    (hX2 : firstSiteFactorBlock X 2 = 0)
    (hC : (X * Yᴴ).rank ≤ 2) (hz : endpointEnergy (X * Yᴴ) = 0)
    (hN : frobSq (X * Yᴴ) = 1) (hrow : ∀ r q, (X * Yᴴ) (2, r) q = 0)
    (hr : ∀ z w t : ℂ,
      let A := firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1
      let B := firstSiteFactorBlock Y 1 - w • firstSiteFactorBlock Y 0 +
        t • firstSiteFactorBlock Y 2
      (twoSiteJointFactorFlatten A B).rank ≤ 2 ∧
        (twoSiteJointFactorFlatten (twoSiteFactorFlip A) (twoSiteFactorFlip B)).rank ≤ 2) :
    IsQutritZeroFamilyMember (X * Yᴴ) := by
  by_cases hY2 : firstSiteFactorBlock Y 2 = 0
  swap
  · exact isQutritZeroFamilyMember_of_nonzero_offplane_factor X Y hX hX2 hC hz hN hrow hY2
  have hb (z w : ℂ) :
      (twoSiteJointFactorFlatten
        (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1)
        (firstSiteFactorBlock Y 1 - w • firstSiteFactorBlock Y 0)).rank ≤ 2 ∧
      (twoSiteJointFactorFlatten
        (twoSiteFactorFlip (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1))
        (twoSiteFactorFlip (firstSiteFactorBlock Y 1 - w • firstSiteFactorBlock Y 0))).rank ≤ 2 := by
    simpa only [zero_smul, add_zero] using hr z w 0
  by_cases ha : ∃ z : ℂ, (twoSiteFactorFlatten
      (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1)).rank = 2
  swap
  · apply isQutritZeroFamilyMember_of_firstSite_rank_one_pencil X Y hX2 hC hz hN hrow
    intro z
    have hle := (twoSiteFactorFlatten_rank_le_joint_left _ _).trans (hb z 0).1
    have hn : (twoSiteFactorFlatten
        (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1)).rank ≠ 2 := by
      intro he
      exact ha ⟨z, he⟩
    omega
  obtain ⟨z₂, hz₂⟩ := ha
  rcases thinFirstSite_member_or_retained_plane X Y hX2 hY2 hC hz hN
      (fun z w => (hb z w).1) z₂ hz₂ with hm | ⟨P₂, hp₂, hx₂, hy₂⟩
  · exact hm
  by_cases ha : ∃ z : ℂ, (twoSiteFactorFlatten (twoSiteFactorFlip
      (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1))).rank = 2
  swap
  · apply isQutritZeroFamilyMember_of_firstSite_other_rank_one_pencil X Y hX2 hC hz hN hrow
    intro z
    have hle := (twoSiteFactorFlatten_rank_le_joint_left _ _).trans (hb z 0).2
    have hn : (twoSiteFactorFlatten (twoSiteFactorFlip
        (firstSiteFactorBlock X 0 + z • firstSiteFactorBlock X 1))).rank ≠ 2 := by
      intro he
      exact ha ⟨z, he⟩
    omega
  obtain ⟨z₃, hz₃⟩ := ha
  rcases thinFirstSite_member_or_other_retained_plane X Y hX2 hY2 hC hz hN
      (fun z w => (hb z w).2) z₃ hz₃ with hm | ⟨P₃, hp₃, hx₃, hy₃⟩
  · exact hm
  let P₁ := LinearMap.range (sharpCoordinatePlaneProjection (2 : Fin 3)).mulVecLin
  have hp₁ : Module.finrank ℂ P₁ ≤ 2 := (sharpCoordinatePlaneProjection_rank 2).le
  exact isQutritZeroFamilyMember_of_coherent_common_planes X Y hC hz hN P₁ P₂ P₃
    hp₁ hp₂.le hp₃.le
    (firstSite_zero_block_columns_in_coordinate_plane X hX2)
    (firstSite_zero_block_columns_in_coordinate_plane Y hY2) hx₂ hy₂ hx₃ hy₃

end ThreeCopyQutritWerner
