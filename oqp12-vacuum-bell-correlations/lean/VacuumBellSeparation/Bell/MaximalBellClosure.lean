module

public import VacuumBellSeparation.Bell.GenericBellCorrelationConvex

@[expose] public section


/-! Norm closure of Bell-correlation level sets on the entire original
normal-state space. This is the subtype topology inherited from the full
continuous dual, not pointwise/weak-star closure or a vector-state image. -/

noncomputable section
namespace VacuumBellSeparation.Bipartite.HC00

open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isClosed_jointBellCorrelation_level_normal (A B : VonNeumannAlgebra H) (C : ℝ) :
    IsClosed {φ : NormalStateSpace (jointAlgebra A B) | jointBellCorrelation A B φ.1 = C} := by
  apply isClosed_eq
  · exact (lipschitzWith_jointBellCorrelation A B).continuous.comp continuous_subtype_val
  · exact continuous_const

/-- For commuting A,B this is exactly the sharp maximal Bell level set.
Closedness itself uses continuity and needs no commutation assumption. -/
def maximalBellNormalStates (A B : VonNeumannAlgebra H) :
    Set (NormalStateSpace (jointAlgebra A B)) :=
  {φ | jointBellCorrelation A B φ.1 = Real.sqrt 2}

theorem isClosed_maximalBellNormalStates (A B : VonNeumannAlgebra H) :
    IsClosed (maximalBellNormalStates A B) :=
  isClosed_jointBellCorrelation_level_normal A B (Real.sqrt 2)

theorem closure_maximalBellNormalStates (A B : VonNeumannAlgebra H) :
    closure (maximalBellNormalStates A B) = maximalBellNormalStates A B :=
  (isClosed_maximalBellNormalStates A B).closure_eq

theorem jointBellCorrelation_eq_of_mem_closure_normal (A B : VonNeumannAlgebra H)
    {S : Set (NormalStateSpace (jointAlgebra A B))} {C : ℝ}
    (hS : ∀ φ ∈ S, jointBellCorrelation A B φ.1 = C)
    {φ : NormalStateSpace (jointAlgebra A B)} (hφ : φ ∈ closure S) :
    jointBellCorrelation A B φ.1 = C :=
  closure_minimal hS (isClosed_jointBellCorrelation_level_normal A B C) hφ

/-- A supplied dense maximal family suffices for all normal states. -/
theorem all_normal_states_maximal_of_dense (A B : VonNeumannAlgebra H)
    (S : Set (NormalStateSpace (jointAlgebra A B))) (hS : Dense S)
    (hmax : ∀ φ ∈ S, jointBellCorrelation A B φ.1 = Real.sqrt 2) :
    ∀ φ : NormalStateSpace (jointAlgebra A B), jointBellCorrelation A B φ.1 = Real.sqrt 2 := by
  intro φ
  exact jointBellCorrelation_eq_of_mem_closure_normal A B hmax (hS φ)

end VacuumBellSeparation.Bipartite.HC00
