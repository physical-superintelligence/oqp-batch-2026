module

public import VacuumBellSeparation.Bell.ConcreteWeakStarInclusion
public import VacuumBellSeparation.Bell.UniversalWeakStarBellSequence

@[expose] public section


/-!
The common Bell sequence also converges in the canonical weak-star topology
of the full original operator algebra. This is a concrete inclusion theorem;
no extension of a joint-algebra state is assumed. Identification with a
separately defined trace-class or series presentation remains separate.
-/

noncomputable section
namespace VacuumBellSeparation.Bipartite

open HC00 TopologicalSpace Filter
open scoped Topology

/-- The full operator algebra on the original H, with no change of representation. -/
def fullOperatorAlgebra (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : VonNeumannAlgebra H where
  toStarSubalgebra := ⊤
  centralizer_centralizer' :=
    Set.Subset.antisymm (Set.subset_univ _) Set.subset_centralizer_centralizer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def fullOperatorElement (T : H →L[ℂ] H) :
    (fullOperatorAlgebra H).toStarSubalgebra := ⟨T, Set.mem_univ T⟩

@[simp] theorem fullOperatorElement_coe (T : H →L[ℂ] H) :
    (fullOperatorElement T : H →L[ℂ] H) = T := rfl

theorem tendsto_fullOperator_coefficientWeak {ι : Type*} {l : Filter ι}
    (M : VonNeumannAlgebra H) {T : ι → M.toStarSubalgebra} {L : M.toStarSubalgebra}
    (hT : Tendsto (β := CoefficientWeakAlgebra M) (fun i => T i) l
      (nhds (X := CoefficientWeakAlgebra M) L)) :
    Tendsto (β := CoefficientWeakAlgebra (fullOperatorAlgebra H))
      (fun i => fullOperatorElement (T i)) l
        (nhds (X := CoefficientWeakAlgebra (fullOperatorAlgebra H)) (fullOperatorElement L)) := by
  let h : M.toStarSubalgebra ≤ (fullOperatorAlgebra H).toStarSubalgebra :=
    fun a _ => Set.mem_univ a
  exact tendsto_coefficientWeak_inclusion h hT

theorem exists_ambient_weakStar_Bell_sequence_of_all_normal_maximal
    [SeparableSpace H] [Nontrivial H]
    (A B : VonNeumannAlgebra H) (hcomm : Commuting A B)
    (hmax : ∀ φ : NormalStateSpace (jointAlgebra A B),
      jointSignedBellCorrelation A B φ.1 = Real.sqrt 2) :
    ∃ T : ℕ → (jointAlgebra A B).toStarSubalgebra,
      (∀ n, T n ∈ jointNormalizedBellOperators A B) ∧
      Tendsto (fun n => coefficientWeakDualHomeomorph (fullOperatorAlgebra H)
        (fullOperatorElement (T n))) atTop
          (𝓝 (coefficientWeakDualHomeomorph (fullOperatorAlgebra H)
            (fullOperatorElement (((Real.sqrt 2 : ℝ) : ℂ) • (1 : H →L[ℂ] H))))) := by
  obtain ⟨T, hT, hlim⟩ :=
    (all_normal_maximal_iff_coefficientWeak_Bell_sequence A B hcomm).mp hmax
  have hfull := tendsto_fullOperator_coefficientWeak (jointAlgebra A B) hlim
  exact ⟨T, hT,
    (coefficientWeakDualHomeomorph (fullOperatorAlgebra H)).continuous.continuousAt.tendsto.comp hfull⟩

end VacuumBellSeparation.Bipartite
