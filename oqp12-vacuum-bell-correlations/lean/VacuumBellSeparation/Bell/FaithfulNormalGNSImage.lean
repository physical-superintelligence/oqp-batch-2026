module

public import VacuumBellSeparation.Bell.NormalGNSBoundedWOT
public import VacuumBellSeparation.Bell.GNSFaithfulRange
public import VacuumBellSeparation.Bell.WOTClosedBallVNA

@[expose] public section


/-!
The faithful normal GNS representation has its LITERAL image as a VNA.
The unit ball is exactly the continuous image of the original compact WOT
unit ball. Faithfulness gives the isometry needed for equality of these
balls; the separately proved closed-ball criterion then supplies the VNA.
No normality, closedness or support equality is assumed for the image.
-/

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped Topology ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance faithfulImage_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

set_option maxHeartbeats 800000 in
/-- The image of the ORIGINAL WOT unit ball is exactly the LITERAL GNS-range
unit ball. The reverse inclusion uses the genuine faithful C-star isometry. -/
theorem gns_unitBall_image_eq_of_faithful
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hf : ∀ a : M.toStarSubalgebra, φ (star a * a) = 0 → a = 0) :
    Set.range (fun T : vnaWOTBall M 1 =>
      ContinuousLinearMapWOT.ofCLM (φ.gnsStarAlgHom (vnaWOTBallElement T))) =
      {T : φ.GNS →WOT[ℂ] φ.GNS |
        T.toCLM ∈ φ.gnsStarAlgHom.range ∧ ‖T.toCLM‖ ≤ 1} := by
  ext T
  constructor
  · rintro ⟨X, rfl⟩
    refine ⟨⟨vnaWOTBallElement X, rfl⟩, ?_⟩
    change ‖φ.gnsStarAlgHom (vnaWOTBallElement X)‖ ≤ 1
    rw [gnsStarAlgHom_norm_of_faithful φ hf]
    exact X.2.2
  · rintro ⟨⟨a, ha⟩, hnorm⟩
    change φ.gnsStarAlgHom a = T.toCLM at ha
    have han : ‖a‖ ≤ 1 := by
      rw [← gnsStarAlgHom_norm_of_faithful φ hf a, ha]
      exact hnorm
    have han_op : ‖(a : H →L[ℂ] H)‖ ≤ 1 := han
    let X : vnaWOTBall M 1 := ⟨ContinuousLinearMapWOT.ofCLM (a : H →L[ℂ] H), a.2, han_op⟩
    refine ⟨X, ?_⟩
    change ContinuousLinearMapWOT.ofCLM (φ.gnsStarAlgHom a) = T
    exact congrArg ContinuousLinearMapWOT.ofCLM ha

/-- Compactness is in actual GNS WOT, not operator norm or a replacement topology. -/
theorem isCompact_gns_unitBall_wot_of_faithful_normal
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hn : IsNormalFunctional M φ)
    (hf : ∀ a : M.toStarSubalgebra, φ (star a * a) = 0 → a = 0) :
    IsCompact {T : φ.GNS →WOT[ℂ] φ.GNS |
      T.toCLM ∈ φ.gnsStarAlgHom.range ∧ ‖T.toCLM‖ ≤ 1} := by
  letI : CompactSpace (vnaWOTBall M 1) :=
    isCompact_iff_compactSpace.mp (isCompact_vna_unitBall_wot M)
  rw [← gns_unitBall_image_eq_of_faithful M φ hf]
  exact isCompact_range (continuous_gns_on_vnaWOTBall M 1 zero_le_one φ hn)

/-- An actual VNA with exactly the faithful normal GNS image carrier. This
is not merely the generated double commutant or the norm closure of the image. -/
theorem exists_vna_eq_gns_range_of_faithful_normal
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hn : IsNormalFunctional M φ)
    (hf : ∀ a : M.toStarSubalgebra, φ (star a * a) = 0 → a = 0) :
    ∃ N : VonNeumannAlgebra φ.GNS, N.toStarSubalgebra = φ.gnsStarAlgHom.range := by
  apply exists_vna_eq_starSubalgebra_of_wot_closed_unitBall φ.gnsStarAlgHom.range
    (gns_range_norm_closed_of_faithful φ hf)
  exact (isCompact_gns_unitBall_wot_of_faithful_normal M φ hn hf).isClosed

end VacuumBellSeparation.Bipartite
