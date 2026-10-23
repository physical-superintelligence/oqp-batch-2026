module

public import ThreeCopyQutritWerner.CertificateLocalGramFamilies
public import ThreeCopyQutritWerner.CertificateDescendantFrames0
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical0_0
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical0_1
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical0_2
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical0_3
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical0_4
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical0_5
public import ThreeCopyQutritWerner.CertificateHighestKernelPhysical0_6
public import ThreeCopyQutritWerner.CertificateBlockTransport

@[expose] public section


/-! Exact physical local decomposition for sector 0. No source-action or completeness premise remains. -/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner



/-- Actual physical compression, in the unchanged original source columns. -/
def certificateLocalDecomposition0Compression (weight : Equiv.Perm (Fin 6) → ℂ)
    (t : Fin 7) : Matrix (Fin (certificateDescendantFrames2SourceSize t)) (Fin (certificateDescendantFrames2SourceSize t)) ℂ :=
  ((certificateDescendantFrames0Source t).map (Int.cast : ℤ → ℂ))ᴴ *
    certificateLocalDiagramCombination {5} weight *
      (certificateDescendantFrames0Source t).map (Int.cast : ℤ → ℂ)

/-- The recovered coefficient action in the original positive metric. -/
def certificateLocalDecomposition0Action (weight : Equiv.Perm (Fin 6) → ℂ)
    (t : Fin 7) : Matrix (Fin (certificateDescendantFrames2SourceSize t)) (Fin (certificateDescendantFrames2SourceSize t)) ℂ :=
  (certificateLocalDecomposition0Gram t)⁻¹ * certificateLocalDecomposition0Compression weight t

theorem certificateLocalDecomposition0metric_action (weight : Equiv.Perm (Fin 6) → ℂ)
    (t : Fin 7) :
    certificateLocalDecomposition0Gram t * certificateLocalDecomposition0Action weight t = certificateLocalDecomposition0Compression weight t := by
  exact Matrix.mul_nonsing_inv_cancel_left _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp (certificateLocalDecomposition0Gram_posDef t).isUnit)

/-- Highest-space reconstruction proves the physical source action for every type. -/
theorem certificateLocalDecomposition0source_action (weight : Equiv.Perm (Fin 6) → ℂ)
    (t : Fin 7) :
    certificateLocalDiagramCombination {5} weight * (certificateDescendantFrames0Source t).map (Int.cast : ℤ → ℂ) =
      (certificateDescendantFrames0Source t).map (Int.cast : ℤ → ℂ) * certificateLocalDecomposition0Action weight t := by
  fin_cases t
  · exact certificateHighestKernel0_0diagram_action weight
  · exact certificateHighestKernel0_1diagram_action weight
  · exact certificateHighestKernel0_2diagram_action weight
  · exact certificateHighestKernel0_3diagram_action weight
  · exact certificateHighestKernel0_4diagram_action weight
  · exact certificateHighestKernel0_5diagram_action weight
  · exact certificateHighestKernel0_6diagram_action weight

/-- Complete physical basis transport for arbitrary complex diagram coefficients. -/
theorem certificateLocalDecomposition0intertwines (weight : Equiv.Perm (Fin 6) → ℂ) :
    certificateLocalDiagramCombination {5} weight * certificateDescendantFrames0Matrix.map (Int.cast : ℤ → ℂ) =
      certificateDescendantFrames0Matrix.map (Int.cast : ℤ → ℂ) *
        Matrix.blockDiagonal' (fun f => certificateLocalDecomposition0Action weight (certificateDescendantFrames2Type f)) :=
  certificateDescendantFrames0Matrix_intertwines _ _
    (certificateDiagramCombination0_lowering weight) (certificateLocalDecomposition0source_action weight)

/-- The physical trace pairing includes each exact representation multiplicity once. -/
theorem certificateLocalDecomposition0trace_mul (left right : Equiv.Perm (Fin 6) → ℂ) :
    (certificateLocalDiagramCombination {5} left *
      certificateLocalDiagramCombination {5} right).trace =
    ∑ t : Fin 7, (certificateDescendantFrames2TypeCount t : ℂ) *
      (certificateLocalDecomposition0Action left t * certificateLocalDecomposition0Action right t).trace := by
  rw [certificate_trace_mul_of_bijective_intertwiner _ _ _ _ _
    certificateDescendantFrames0Matrix_complex_bijective
    (certificateLocalDecomposition0intertwines left) (certificateLocalDecomposition0intertwines right),
    certificate_trace_mul_blocks]
  exact certificate_sum_type_counts certificateDescendantFrames2Type certificateDescendantFrames2TypeCount
    certificateDescendantFrames2type_count 
    (fun t => (certificateLocalDecomposition0Action left t *
      certificateLocalDecomposition0Action right t).trace)

/-- Literal physical Hilbert–Schmidt squared norm in original coefficient metrics. -/
theorem certificateLocalDecomposition0frobSq (weight : Equiv.Perm (Fin 6) → ℂ)
    (hM : (certificateLocalDiagramCombination {5} weight).IsHermitian) :
    (frobSq (certificateLocalDiagramCombination {5} weight) : ℂ) =
      ∑ t : Fin 7, (certificateDescendantFrames2TypeCount t : ℂ) *
        (certificateLocalDecomposition0Action weight t * certificateLocalDecomposition0Action weight t).trace := by
  rw [ofReal_frobSq_eq_trace, hM.eq]
  exact certificateLocalDecomposition0trace_mul weight weight

/-- Positivity is checked in every original physical source compression. -/
theorem certificateLocalDecomposition0posSemidef_iff (weight : Equiv.Perm (Fin 6) → ℂ)
    (hM : (certificateLocalDiagramCombination {5} weight).IsHermitian) :
    (certificateLocalDiagramCombination {5} weight).PosSemidef ↔
      ∀ t : Fin 7, (certificateLocalDecomposition0Compression weight t).PosSemidef := by
  constructor
  · intro h t
    exact h.conjTranspose_mul_mul_same ((certificateDescendantFrames0Source t).map (Int.cast : ℤ → ℂ))
  · intro h
    apply certificate_posSemidef_of_block_intertwiner _
      (certificateDescendantFrames0Matrix.map (Int.cast : ℤ → ℂ))
      (fun f => certificateLocalDecomposition0Gram (certificateDescendantFrames2Type f))
      (fun f => certificateLocalDecomposition0Action weight (certificateDescendantFrames2Type f))
      hM certificateDescendantFrames0Matrix_complex_surjective
      (fun f => certificateLocalDecomposition0Gram_posDef _) _ (certificateLocalDecomposition0intertwines weight)
    intro f
    rw [certificateLocalDecomposition0metric_action]
    exact h _

end ThreeCopyQutritWerner
