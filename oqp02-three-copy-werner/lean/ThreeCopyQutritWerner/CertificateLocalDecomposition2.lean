module

public import ThreeCopyQutritWerner.CertificateDescendantFrames2
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysicalAll
public import ThreeCopyQutritWerner.CertificateBlockTransport

@[expose] public section


/-! Exact physical local decomposition for sector 2. No source-action or completeness premise remains. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

/-- The original archive Gram matrix of each source type. -/
def certificateLocalDecomposition2Gram : (t : Fin 7) → Matrix (Fin (certificateDescendantFrames2SourceSize t)) (Fin (certificateDescendantFrames2SourceSize t)) ℂ := by
  exact
    Fin.cases (certificateLocalGram2_0.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram2_1.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram2_2.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram2_3.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram2_4.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram2_5.map (Int.cast : ℤ → ℂ)) <|
    Fin.cases (certificateLocalGram2_6.map (Int.cast : ℤ → ℂ)) <|
    Fin.rec0

theorem certificateLocalDecomposition2Gram_posDef (t : Fin 7) :
    (certificateLocalDecomposition2Gram t).PosDef := by
  fin_cases t
  · exact certificateLocalGram2_0_posDef
  · exact certificateLocalGram2_1_posDef
  · exact certificateLocalGram2_2_posDef
  · exact certificateLocalGram2_3_posDef
  · exact certificateLocalGram2_4_posDef
  · exact certificateLocalGram2_5_posDef
  · exact certificateLocalGram2_6_posDef

/-- Actual physical compression, in the unchanged original source columns. -/
def certificateLocalDecomposition2Compression (weight : Equiv.Perm (Fin 6) → ℂ)
    (t : Fin 7) : Matrix (Fin (certificateDescendantFrames2SourceSize t)) (Fin (certificateDescendantFrames2SourceSize t)) ℂ :=
  ((certificateDescendantFrames2Source t).map (Int.cast : ℤ → ℂ))ᴴ *
    certificateLocalDiagramCombination {1, 2, 3, 4, 5} weight *
      (certificateDescendantFrames2Source t).map (Int.cast : ℤ → ℂ)

/-- The recovered coefficient action in the original positive metric. -/
def certificateLocalDecomposition2Action (weight : Equiv.Perm (Fin 6) → ℂ)
    (t : Fin 7) : Matrix (Fin (certificateDescendantFrames2SourceSize t)) (Fin (certificateDescendantFrames2SourceSize t)) ℂ :=
  (certificateLocalDecomposition2Gram t)⁻¹ * certificateLocalDecomposition2Compression weight t

theorem certificateLocalDecomposition2metric_action (weight : Equiv.Perm (Fin 6) → ℂ)
    (t : Fin 7) :
    certificateLocalDecomposition2Gram t * certificateLocalDecomposition2Action weight t = certificateLocalDecomposition2Compression weight t := by
  exact Matrix.mul_nonsing_inv_cancel_left _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp (certificateLocalDecomposition2Gram_posDef t).isUnit)

/-- Highest-space reconstruction proves the physical source action for every type. -/
theorem certificateLocalDecomposition2source_action (weight : Equiv.Perm (Fin 6) → ℂ)
    (t : Fin 7) :
    certificateLocalDiagramCombination {1, 2, 3, 4, 5} weight * (certificateDescendantFrames2Source t).map (Int.cast : ℤ → ℂ) =
      (certificateDescendantFrames2Source t).map (Int.cast : ℤ → ℂ) * certificateLocalDecomposition2Action weight t := by
  fin_cases t
  · exact certificateHighestKernel2_0diagram_action weight
  · exact certificateHighestKernel2_1diagram_action weight
  · exact certificateHighestKernel2_2diagram_action weight
  · exact certificateHighestKernel2_3diagram_action weight
  · exact certificateHighestKernel2_4diagram_action weight
  · exact certificateHighestKernel2_5diagram_action weight
  · exact certificateHighestKernel2_6diagram_action weight

/-- Complete physical basis transport for arbitrary complex diagram coefficients. -/
theorem certificateLocalDecomposition2intertwines (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {1, 2, 3, 4, 5} weight * certificateDescendantFrames2Matrix.map (Int.cast : ℤ → ℂ) =
      certificateDescendantFrames2Matrix.map (Int.cast : ℤ → ℂ) *
        Matrix.blockDiagonal' (fun f => certificateLocalDecomposition2Action weight (certificateDescendantFrames2Type f)) :=
  certificateDescendantFrames2Matrix_intertwines _ _
    (certificateDiagramCombination2_lowering weight) (certificateLocalDecomposition2source_action weight)

/-- The physical trace pairing includes each exact representation multiplicity once. -/
theorem certificateLocalDecomposition2trace_mul (left right : Equiv.Perm (Fin 6) → ℂ) :
    (certificateLocalDiagramCombination {1, 2, 3, 4, 5} left *
      certificateLocalDiagramCombination {1, 2, 3, 4, 5} right).trace =
    ∑ t : Fin 7, (certificateDescendantFrames2TypeCount t : ℂ) *
      (certificateLocalDecomposition2Action left t * certificateLocalDecomposition2Action right t).trace := by
  rw [certificate_trace_mul_of_bijective_intertwiner _ _ _ _ _
    certificateDescendantFrames2Matrix_complex_bijective
    (certificateLocalDecomposition2intertwines left) (certificateLocalDecomposition2intertwines right),
    certificate_trace_mul_blocks]
  exact certificate_sum_type_counts certificateDescendantFrames2Type certificateDescendantFrames2TypeCount
    certificateDescendantFrames2type_count 
    (fun t => (certificateLocalDecomposition2Action left t *
      certificateLocalDecomposition2Action right t).trace)

/-- Literal physical Hilbert–Schmidt squared norm in original coefficient metrics. -/
theorem certificateLocalDecomposition2frobSq (weight : Equiv.Perm (Fin 6) → ℂ)
    (hM : (certificateLocalDiagramCombination {1, 2, 3, 4, 5} weight).IsHermitian) :
    (frobSq (certificateLocalDiagramCombination {1, 2, 3, 4, 5} weight) : ℂ) =
      ∑ t : Fin 7, (certificateDescendantFrames2TypeCount t : ℂ) *
        (certificateLocalDecomposition2Action weight t * certificateLocalDecomposition2Action weight t).trace := by
  rw [ofReal_frobSq_eq_trace, hM.eq]
  exact certificateLocalDecomposition2trace_mul weight weight

/-- Positivity is checked in every original physical source compression. -/
theorem certificateLocalDecomposition2posSemidef_iff (weight : Equiv.Perm (Fin 6) → ℂ)
    (hM : (certificateLocalDiagramCombination {1, 2, 3, 4, 5} weight).IsHermitian) :
    (certificateLocalDiagramCombination {1, 2, 3, 4, 5} weight).PosSemidef ↔
      ∀ t : Fin 7, (certificateLocalDecomposition2Compression weight t).PosSemidef := by
  constructor
  · intro h t
    exact h.conjTranspose_mul_mul_same ((certificateDescendantFrames2Source t).map (Int.cast : ℤ → ℂ))
  · intro h
    apply certificate_posSemidef_of_block_intertwiner _
      (certificateDescendantFrames2Matrix.map (Int.cast : ℤ → ℂ))
      (fun f => certificateLocalDecomposition2Gram (certificateDescendantFrames2Type f))
      (fun f => certificateLocalDecomposition2Action weight (certificateDescendantFrames2Type f))
      hM certificateDescendantFrames2Matrix_complex_surjective
      (fun f => certificateLocalDecomposition2Gram_posDef _) _ (certificateLocalDecomposition2intertwines weight)
    intro f
    rw [certificateLocalDecomposition2metric_action]
    exact h _

end ThreeCopyQutritWerner
