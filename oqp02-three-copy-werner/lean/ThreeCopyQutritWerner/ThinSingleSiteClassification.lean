module

public import ThreeCopyQutritWerner.ThinSingleOutputClassification
public import ThreeCopyQutritWerner.QutritFamilyAdjointInvariant
public import ThreeCopyQutritWerner.AffinePencilRankOne
public import ThreeCopyQutritWerner.CoherentPencilSupport
public import ThreeCopyQutritWerner.EndpointCorangeStationarity

@[expose] public section


/-! Complete original-family classification when any actual local range or
corange has dimension at most one. All physical data and coordinate changes
are constructed from the original matrix. -/

noncomputable section
open scoped Matrix ComplexOrder
namespace ThreeCopyQutritWerner

theorem hasSingleFirstOutput_of_localRangeDim_le_one
    (C : Matrix QutritSites QutritSites ℂ) (hne : C ≠ 0) (h : localRangeDim₁ C ≤ 1) :
    HasSingleFirstOutput C := by
  rw [localRangeDim₁_eq_coherentFlatten_rank] at h
  obtain ⟨u, v, hF⟩ := matrix_exists_vecMulVec_of_rank_le_one (coherentFlatten₁ C) h
  have he (i : Fin 3) (r : Fin 3 × Fin 3) (q : QutritSites) :
      C (i, r) q = u i * v (r, q) := congrFun (congrFun hF i) (r, q)
  obtain ⟨p, q, hpq⟩ : ∃ p q, C p q ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hne (by ext p q; exact hn p q)
  have hu : u p.1 ≠ 0 := by
    intro hz
    apply hpq
    rw [show p = (p.1, p.2) from rfl, he, hz, zero_mul]
  refine ⟨p.1, fun i => u i / u p.1, div_self hu, ?_⟩
  intro i r s
  rw [he, he]
  field_simp <;> ring

theorem localRangeDim₁_submatrix_site₂
    (C : Matrix QutritSites QutritSites ℂ) :
    localRangeDim₁ (C.submatrix siteEquiv₂ siteEquiv₂) = localRangeDim₂ C := by
  rw [localRangeDim₁_eq_coherentFlatten_rank, localRangeDim₂_eq_coherentFlatten_rank]
  have he : coherentFlatten₁ (C.submatrix siteEquiv₂ siteEquiv₂) =
      (coherentFlatten₂ C).submatrix (Equiv.refl (Fin 3))
        (Equiv.prodCongr (Equiv.refl (Fin 3 × Fin 3)) siteEquiv₂) := rfl
  rw [he, Matrix.rank_submatrix]

theorem localRangeDim₁_submatrix_site₃
    (C : Matrix QutritSites QutritSites ℂ) :
    localRangeDim₁ (C.submatrix siteEquiv₃ siteEquiv₃) = localRangeDim₃ C := by
  rw [localRangeDim₁_eq_coherentFlatten_rank, localRangeDim₃_eq_coherentFlatten_rank]
  have he : coherentFlatten₁ (C.submatrix siteEquiv₃ siteEquiv₃) =
      (coherentFlatten₃ C).submatrix (Equiv.refl (Fin 3))
        (Equiv.prodCongr (Equiv.refl (Fin 3 × Fin 3)) siteEquiv₃) := rfl
  rw [he, Matrix.rank_submatrix]

theorem isQutritZeroFamilyMember_of_single_output_at_site
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1) (i : Fin 3)
    (hfactor : HasSingleFirstOutput
      (C.submatrix (binaryPartitionQutritTuple i) (binaryPartitionQutritTuple i))) :
    IsQutritZeroFamilyMember C := by
  have hr := (Matrix.rank_submatrix C (binaryPartitionQutritTuple i)
    (binaryPartitionQutritTuple i)).trans_le hC
  have hn := (frobSq_submatrix_equiv (binaryPartitionQutritTuple i) C).trans hN
  have he : endpointEnergy
      (C.submatrix (binaryPartitionQutritTuple i) (binaryPartitionQutritTuple i)) = 0 := by
    fin_cases i
    · exact hz
    · exact (energy_submatrix_siteEquiv₂ (1 / 2) C).trans hz
    · exact (energy_submatrix_siteEquiv₃ (1 / 2) C).trans hz
  exact (isQutritZeroFamilyMember_site_iff C i).mp
    (isQutritZeroFamilyMember_of_single_first_output _ hr he hn hfactor)

theorem isQutritZeroFamilyMember_of_single_input_at_site
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1) (i : Fin 3)
    (hfactor : HasSingleFirstOutput
      (Cᴴ.submatrix (binaryPartitionQutritTuple i) (binaryPartitionQutritTuple i))) :
    IsQutritZeroFamilyMember C := by
  apply (isQutritZeroFamilyMember_conjTranspose_iff C).mp
  exact isQutritZeroFamilyMember_of_single_output_at_site Cᴴ
    ((Matrix.rank_conjTranspose C).trans_le hC)
    ((energy_conjTranspose (1 / 2) C).trans hz)
    ((singular_frobSq_conjTranspose C).trans hN) i hfactor

/-- A genuine one-dimensional local support at any of the three sites
suffices, without a binary carrier assumption on the inactive vectors. -/
theorem isQutritZeroFamilyMember_of_local_range_line
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1)
    (hline : localRangeDim₁ C ≤ 1 ∨ localRangeDim₂ C ≤ 1 ∨ localRangeDim₃ C ≤ 1) :
    IsQutritZeroFamilyMember C := by
  have hn : C ≠ 0 := by intro he; simp [he, frobSq] at hN
  rcases hline with h | h | h
  · exact isQutritZeroFamilyMember_of_single_first_output C hC hz hN
      (hasSingleFirstOutput_of_localRangeDim_le_one C hn h)
  · apply isQutritZeroFamilyMember_of_single_output_at_site C hC hz hN 1
    apply hasSingleFirstOutput_of_localRangeDim_le_one
    · intro he
      apply hn
      have hh := congrArg (fun M : Matrix QutritSites QutritSites ℂ =>
        M.submatrix siteEquiv₂.symm siteEquiv₂.symm) he
      simpa [binaryPartitionQutritTuple] using hh
    · exact (localRangeDim₁_submatrix_site₂ C).trans_le h
  · apply isQutritZeroFamilyMember_of_single_output_at_site C hC hz hN 2
    apply hasSingleFirstOutput_of_localRangeDim_le_one
    · intro he
      apply hn
      have hh := congrArg (fun M : Matrix QutritSites QutritSites ℂ =>
        M.submatrix siteEquiv₃.symm siteEquiv₃.symm) he
      simpa [binaryPartitionQutritTuple] using hh
    · exact (localRangeDim₁_submatrix_site₃ C).trans_le h

theorem isQutritZeroFamilyMember_of_local_corange_line
    (C : Matrix QutritSites QutritSites ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hN : frobSq C = 1)
    (hline : localCorangeDim₁ C ≤ 1 ∨ localCorangeDim₂ C ≤ 1 ∨ localCorangeDim₃ C ≤ 1) :
    IsQutritZeroFamilyMember C := by
  apply (isQutritZeroFamilyMember_conjTranspose_iff C).mp
  apply isQutritZeroFamilyMember_of_local_range_line Cᴴ
    ((Matrix.rank_conjTranspose C).trans_le hC)
    ((energy_conjTranspose (1 / 2) C).trans hz)
    ((singular_frobSq_conjTranspose C).trans hN)
  simpa only [localCorangeDim₁_eq_localRangeDim_adjoint,
    localCorangeDim₂_eq_localRangeDim_adjoint, localCorangeDim₃_eq_localRangeDim_adjoint] using hline

end ThreeCopyQutritWerner
