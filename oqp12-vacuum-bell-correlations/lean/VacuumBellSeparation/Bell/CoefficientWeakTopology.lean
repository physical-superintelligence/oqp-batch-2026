module

public import VacuumBellSeparation.Bell.CoefficientPredual
public import Mathlib.Analysis.LocallyConvex.WeakDual

@[expose] public section


/-!
The literal weak topology on the original algebra paired with its concrete
coefficient norm closure. Positive continuity in this topology is equivalent
to all-directed order normality. Identifying the coefficient space as an
actual Banach predual is the separate surjectivity theorem
`coefficientPredualEvaluation_surjective` in `Bell/CoefficientPredualDuality.lean`.
-/

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance coefficientWeak_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

def coefficientPairing (M : VonNeumannAlgebra H) :
    M.toStarSubalgebra →ₗ[ℂ] (coefficientPredual M) →ₗ[ℂ] ℂ where
  toFun a := (coefficientPredualEvaluation M a).toLinearMap
  map_add' a b := by
    ext f
    exact f.1.map_add a b
  map_smul' c a := by
    ext f
    exact f.1.map_smul c a

abbrev CoefficientWeakAlgebra (M : VonNeumannAlgebra H) := WeakBilin (coefficientPairing M)

@[simp] theorem coefficientPairing_apply (M : VonNeumannAlgebra H)
    (a : M.toStarSubalgebra) (f : coefficientPredual M) :
    coefficientPairing M a f = f.1 a := rfl

theorem continuous_coefficientWeak_of_mem (M : VonNeumannAlgebra H)
    (f : StrongDual ℂ M.toStarSubalgebra) (hf : f ∈ coefficientPredual M) :
    Continuous (fun a : CoefficientWeakAlgebra M => f a) :=
  WeakBilin.eval_continuous (coefficientPairing M) ⟨f, hf⟩

theorem mem_coefficientPredual_of_continuous_coefficientWeak
    (M : VonNeumannAlgebra H) (f : StrongDual ℂ M.toStarSubalgebra)
    (hf : Continuous (fun a : CoefficientWeakAlgebra M => f a)) :
    f ∈ coefficientPredual M := by
  let g : StrongDual ℂ (CoefficientWeakAlgebra M) :=
    { toLinearMap := f.toLinearMap
      cont := hf }
  obtain ⟨p, hp⟩ := LinearMap.dualEmbedding_surjective (coefficientPairing M) g
  have he : p.1 = f := by
    ext a
    exact congrArg (fun ℓ : StrongDual ℂ (CoefficientWeakAlgebra M) => ℓ a) hp
  exact he ▸ p.2

theorem mem_coefficientPredual_iff_continuous_coefficientWeak
    (M : VonNeumannAlgebra H) (f : StrongDual ℂ M.toStarSubalgebra) :
    f ∈ coefficientPredual M ↔ Continuous (fun a : CoefficientWeakAlgebra M => f a) :=
  ⟨continuous_coefficientWeak_of_mem M f,
    mem_coefficientPredual_of_continuous_coefficientWeak M f⟩

theorem isNormalFunctional_iff_continuous_coefficientWeak
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) :
    IsNormalFunctional M φ ↔ Continuous (fun a : CoefficientWeakAlgebra M => φ a) :=
  (isNormalFunctional_iff_mem_coefficientPredual M φ).trans
    (mem_coefficientPredual_iff_continuous_coefficientWeak M
      (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap)

theorem continuous_boundedWOT_to_coefficientWeak
    (M : VonNeumannAlgebra H) (R : ℝ) (hR : 0 ≤ R) :
    Continuous (Y := CoefficientWeakAlgebra M)
      (fun T : vnaWOTBall M R => vnaWOTBallElement T) := by
  apply WeakBilin.continuous_of_continuous_eval (coefficientPairing M)
  intro f
  exact continuous_vnaWOTBall_eval_of_mem_coefficientPredual M R hR f.1 f.2

end VacuumBellSeparation.Bipartite
