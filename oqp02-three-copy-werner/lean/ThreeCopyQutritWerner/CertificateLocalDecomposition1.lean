module

public import ThreeCopyQutritWerner.CertificateLocalGramFamilies
public import ThreeCopyQutritWerner.CertificateDescendantFrames1
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical1_0
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical1_1
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical1_2
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical1_3
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical1_4
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical1_5
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical1_6
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical1_7
public import ThreeCopyQutritWerner.CertificateBlockTransport

@[expose] public section


/-! Exact physical local decomposition for sector 1. No source-action or completeness premise remains. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner



/-- Actual physical compression, in the unchanged original source columns. -/
def certificateLocalDecomposition1Compression (weight : Equiv.Perm (Fin 6) → ℂ)
    (t : Fin 8) : Matrix (Fin (certificateDescendantFrames1SourceSize t)) (Fin (certificateDescendantFrames1SourceSize t)) ℂ :=
  ((certificateDescendantFrames1Source t).map (Int.cast : ℤ → ℂ))ᴴ *
    certificateLocalDiagramCombination {3, 4, 5} weight *
      (certificateDescendantFrames1Source t).map (Int.cast : ℤ → ℂ)

/-- The recovered coefficient action in the original positive metric. -/
def certificateLocalDecomposition1Action (weight : Equiv.Perm (Fin 6) → ℂ)
    (t : Fin 8) : Matrix (Fin (certificateDescendantFrames1SourceSize t)) (Fin (certificateDescendantFrames1SourceSize t)) ℂ :=
  (certificateLocalDecomposition1Gram t)⁻¹ * certificateLocalDecomposition1Compression weight t

theorem certificateLocalDecomposition1metric_action (weight : Equiv.Perm (Fin 6) → ℂ)
    (t : Fin 8) :
    certificateLocalDecomposition1Gram t * certificateLocalDecomposition1Action weight t = certificateLocalDecomposition1Compression weight t := by
  exact Matrix.mul_nonsing_inv_cancel_left _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp (certificateLocalDecomposition1Gram_posDef t).isUnit)

/-- Highest-space reconstruction proves the physical source action for every type. -/
theorem certificateLocalDecomposition1source_action (weight : Equiv.Perm (Fin 6) → ℂ)
    (t : Fin 8) :
    certificateLocalDiagramCombination {3, 4, 5} weight * (certificateDescendantFrames1Source t).map (Int.cast : ℤ → ℂ) =
      (certificateDescendantFrames1Source t).map (Int.cast : ℤ → ℂ) * certificateLocalDecomposition1Action weight t := by
  fin_cases t
  · exact certificateHighestKernel1_0diagram_action weight
  · exact certificateHighestKernel1_1diagram_action weight
  · exact certificateHighestKernel1_2diagram_action weight
  · exact certificateHighestKernel1_3diagram_action weight
  · exact certificateHighestKernel1_4diagram_action weight
  · exact certificateHighestKernel1_5diagram_action weight
  · exact certificateHighestKernel1_6diagram_action weight
  · exact certificateHighestKernel1_7diagram_action weight

/-- Complete physical basis transport for arbitrary complex diagram coefficients. -/
theorem certificateLocalDecomposition1intertwines (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {3, 4, 5} weight * certificateDescendantFrames1Matrix.map (Int.cast : ℤ → ℂ) =
      certificateDescendantFrames1Matrix.map (Int.cast : ℤ → ℂ) *
        Matrix.blockDiagonal' (fun f => certificateLocalDecomposition1Action weight (certificateDescendantFrames1Type f)) :=
  certificateDescendantFrames1Matrix_intertwines _ _
    (certificateDiagramCombination1_lowering weight) (certificateLocalDecomposition1source_action weight)

/-- The physical trace pairing includes each exact representation multiplicity once. -/
theorem certificateLocalDecomposition1trace_mul (left right : Equiv.Perm (Fin 6) → ℂ) :
    (certificateLocalDiagramCombination {3, 4, 5} left *
      certificateLocalDiagramCombination {3, 4, 5} right).trace =
    ∑ t : Fin 8, (certificateDescendantFrames1TypeCount t : ℂ) *
      (certificateLocalDecomposition1Action left t * certificateLocalDecomposition1Action right t).trace := by
  rw [certificate_trace_mul_of_bijective_intertwiner _ _ _ _ _
    certificateDescendantFrames1Matrix_complex_bijective
    (certificateLocalDecomposition1intertwines left) (certificateLocalDecomposition1intertwines right),
    certificate_trace_mul_blocks]
  exact certificate_sum_type_counts certificateDescendantFrames1Type certificateDescendantFrames1TypeCount
    certificateDescendantFrames1type_count 
    (fun t => (certificateLocalDecomposition1Action left t *
      certificateLocalDecomposition1Action right t).trace)

/-- Literal physical Hilbert–Schmidt squared norm in original coefficient metrics. -/
theorem certificateLocalDecomposition1frobSq (weight : Equiv.Perm (Fin 6) → ℂ)
    (hM : (certificateLocalDiagramCombination {3, 4, 5} weight).IsHermitian) :
    (frobSq (certificateLocalDiagramCombination {3, 4, 5} weight) : ℂ) =
      ∑ t : Fin 8, (certificateDescendantFrames1TypeCount t : ℂ) *
        (certificateLocalDecomposition1Action weight t * certificateLocalDecomposition1Action weight t).trace := by
  rw [ofReal_frobSq_eq_trace, hM.eq]
  exact certificateLocalDecomposition1trace_mul weight weight

/-- Positivity is checked in every original physical source compression. -/
theorem certificateLocalDecomposition1posSemidef_iff (weight : Equiv.Perm (Fin 6) → ℂ)
    (hM : (certificateLocalDiagramCombination {3, 4, 5} weight).IsHermitian) :
    (certificateLocalDiagramCombination {3, 4, 5} weight).PosSemidef ↔
      ∀ t : Fin 8, (certificateLocalDecomposition1Compression weight t).PosSemidef := by
  constructor
  · intro h t
    exact h.conjTranspose_mul_mul_same ((certificateDescendantFrames1Source t).map (Int.cast : ℤ → ℂ))
  · intro h
    apply certificate_posSemidef_of_block_intertwiner _
      (certificateDescendantFrames1Matrix.map (Int.cast : ℤ → ℂ))
      (fun f => certificateLocalDecomposition1Gram (certificateDescendantFrames1Type f))
      (fun f => certificateLocalDecomposition1Action weight (certificateDescendantFrames1Type f))
      hM certificateDescendantFrames1Matrix_complex_surjective
      (fun f => certificateLocalDecomposition1Gram_posDef _) _ (certificateLocalDecomposition1intertwines weight)
    intro f
    rw [certificateLocalDecomposition1metric_action]
    exact h _

end ThreeCopyQutritWerner
