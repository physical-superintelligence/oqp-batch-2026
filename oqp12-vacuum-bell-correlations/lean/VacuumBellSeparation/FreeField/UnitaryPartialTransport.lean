module

public import VacuumBellSeparation.FreeField.RatioRegularizerIndependence

@[expose] public section


/-!
# Full-domain unitary transport of partial operators

Transport uses the actual inverse-image domain. The universal resolvent
equation is invariant under this construction, hence it identifies both
the domain and values of the transported operator.
-/

namespace VacuumBellSeparation

open ContinuousLinearMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

noncomputable def unitaryPartialTransport (V : E ≃ₗᵢ[ℂ] F) (T : E →ₗ.[ℂ] E) : F →ₗ.[ℂ] F :=
  V.toLinearEquiv.toLinearMap.compPMap
    (T.comp (V.symm.toLinearEquiv.toLinearMap.toPMap
      (T.domain.comap V.symm.toLinearEquiv.toLinearMap)) (fun x => x.property))

@[simp] theorem unitaryPartialTransport_domain (V : E ≃ₗᵢ[ℂ] F) (T : E →ₗ.[ℂ] E) :
    (unitaryPartialTransport V T).domain = T.domain.comap V.symm.toLinearEquiv.toLinearMap := rfl

@[simp] theorem unitaryPartialTransport_apply (V : E ≃ₗᵢ[ℂ] F) (T : E →ₗ.[ℂ] E)
    (x : (unitaryPartialTransport V T).domain) :
    unitaryPartialTransport V T x = V (T ⟨V.symm x, x.property⟩) := rfl

theorem unitaryPartialTransport_resolvent (V : E ≃ₗᵢ[ℂ] F) (T : E →ₗ.[ℂ] E)
    (R : E →L[ℂ] E)
    (hR : ∀ x y : E, (∃ hy : y ∈ T.domain, y + T ⟨y, hy⟩ = x) ↔ R x = y)
    (x y : F) :
    (∃ hy : y ∈ (unitaryPartialTransport V T).domain,
      y + unitaryPartialTransport V T ⟨y, hy⟩ = x) ↔
        V (R (V.symm x)) = y := by
  constructor
  · rintro ⟨hy, hh⟩
    have heq : V.symm y + T ⟨V.symm y, hy⟩ = V.symm x := by
      apply V.injective
      simpa only [map_add, LinearIsometryEquiv.apply_symm_apply,
        unitaryPartialTransport_apply] using hh
    rw [(hR (V.symm x) (V.symm y)).mp ⟨hy, heq⟩,
      LinearIsometryEquiv.apply_symm_apply]
  · intro hh
    have heq : R (V.symm x) = V.symm y := by
      apply V.injective
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hh
    obtain ⟨hy, ht⟩ := (hR (V.symm x) (V.symm y)).mpr heq
    refine ⟨hy, ?_⟩
    simpa only [map_add, LinearIsometryEquiv.apply_symm_apply,
      unitaryPartialTransport_apply] using congrArg V ht

end VacuumBellSeparation
