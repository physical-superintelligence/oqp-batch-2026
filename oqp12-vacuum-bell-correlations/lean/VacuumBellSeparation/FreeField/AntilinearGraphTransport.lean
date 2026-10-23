module

public import VacuumBellSeparation.FreeField.AntilinearGraphAdjoint

@[expose] public section


/-!
# Unitary covariance of universal antilinear adjoint and square graphs

The hypothesis identifies the entire original relation. The conclusions
quantify the full universal adjoint and retain its intermediate-domain
witness; no density or test-core approximation enters the transport.
-/

namespace VacuumBellSeparation

variable {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem antilinearGraphAdjoint_unitary (V : H ≃ₗᵢ[ℂ] K)
    (S : Set (H × H)) (T : Set (K × K))
    (h : ∀ x y, (V x, V y) ∈ T ↔ (x, y) ∈ S) (x y : H) :
    (V x, V y) ∈ antilinearGraphAdjoint T ↔ (x, y) ∈ antilinearGraphAdjoint S := by
  constructor
  · intro hx u v huv
    have hh := hx (V u) (V v) ((h u v).mpr huv)
    simpa only [LinearIsometryEquiv.inner_map_map] using hh
  · intro hx u v huv
    have hback : (V.symm u, V.symm v) ∈ S := by
      apply (h _ _).mp
      simpa only [LinearIsometryEquiv.apply_symm_apply] using huv
    have hh := hx (V.symm u) (V.symm v) hback
    calc
      inner ℂ v (V x) = inner ℂ (V (V.symm v)) (V x) := by
        rw [LinearIsometryEquiv.apply_symm_apply]
      _ = inner ℂ (V.symm v) x := V.inner_map_map _ _
      _ = inner ℂ y (V.symm u) := hh
      _ = inner ℂ (V y) (V (V.symm u)) := (V.inner_map_map _ _).symm
      _ = inner ℂ (V y) u := by rw [LinearIsometryEquiv.apply_symm_apply]

theorem antilinearGraphSquare_unitary (V : H ≃ₗᵢ[ℂ] K)
    (S : Set (H × H)) (T : Set (K × K))
    (h : ∀ x y, (V x, V y) ∈ T ↔ (x, y) ∈ S) (x y : H) :
    (V x, V y) ∈ antilinearGraphSquare T ↔ (x, y) ∈ antilinearGraphSquare S := by
  constructor
  · rintro ⟨v, hxv, hvy⟩
    refine ⟨V.symm v, (h _ _).mp ?_, ?_⟩
    · simpa only [LinearIsometryEquiv.apply_symm_apply] using hxv
    · apply (antilinearGraphAdjoint_unitary V S T h _ _).mp
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hvy
  · rintro ⟨v, hxv, hvy⟩
    exact ⟨V v, (h _ _).mpr hxv,
      (antilinearGraphAdjoint_unitary V S T h _ _).mpr hvy⟩

end VacuumBellSeparation
