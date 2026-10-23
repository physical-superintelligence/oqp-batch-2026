module

public import ThreeCopyQutritWerner.CertificateTensorActions
public import ThreeCopyQutritWerner.CertificateEndpointDiagramCore

@[expose] public section


/-!
# The literal endpoint operator in the original diagram coordinates

The distinguished local registers are row=0 and col=5; registers 1 through 4
carry the identity. Their swap, partially transposed at register 5, is the
unnormalized maximally entangled projector. This identifies the manuscript's
normalized Werner endpoint with the precise local diagram coefficients used
by the original source actions. The frame-free identities (`certificateSixRegisterOperator_diagram`
and its lemmas) are in `CertificateEndpointDiagramCore`; this module adds the source action on the
complete three-site frame basis.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Endpoint action on the complete original source tensor basis; no saved action is assumed. -/
theorem certificateSixRegisterOperator_source_action :
    certificateRegroupMatrix sixRegisterOperator * certificateThreeSiteFrameSystem0.basis =
      certificateThreeSiteFrameSystem0.basis * Matrix.blockDiagonal' (fun f =>
        certificateTripleSourceAction certificatePhysicalFrameSystem0
          (certificateLocalDecomposition0Action certificateEndpointDiagramWeight)
          (certificateLocalDecomposition0Action certificateEndpointDiagramWeight)
          (certificateLocalDecomposition0Action certificateEndpointDiagramWeight)
          (certificateThreeSiteFrameSystem0.type f)) := by
  rw [certificateSixRegisterOperator_diagram]
  exact certificateThreeSiteDiagramActions0 certificateEndpointDiagramWeight
    certificateEndpointDiagramWeight certificateEndpointDiagramWeight

end ThreeCopyQutritWerner
