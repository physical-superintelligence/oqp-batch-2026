module

public import VacuumBellSeparation.Bell.NormalFunctionalFiniteVectorApproximation
public import VacuumBellSeparation.Bell.BoundedWOTFunctionalContinuity
public import VacuumBellSeparation.Bell.GNSNormalDirectedSuprema
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Topology.Algebra.GroupWithZero

@[expose] public section


/-!
Order-normal positive functionals are continuous on the original bounded
WOT balls by ACTUAL finite-vector norm approximation. This applies to all
GNS diagonal coefficients. Polarization gives every matrix coefficient,
without assuming that the GNS representation image is already a VNA.
-/

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped Topology ComplexOrder InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance normalWOT_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- No global-WOT continuity is asserted: the domain is the actual bounded ball. -/
theorem continuous_vnaWOTBall_eval_of_positive_normal
    (M : VonNeumannAlgebra H) (R : ℝ) (hR : 0 ≤ R)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ) :
    Continuous (fun T : vnaWOTBall M R => φ (vnaWOTBallElement T)) := by
  apply continuous_vnaWOTBall_eval_of_norm_approximation M R hR
    (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap
  intro ε hε
  obtain ⟨n, ξ, hξ⟩ := exists_finite_vectors_approx_normalFunctional M φ hn hε
  refine ⟨(PositiveContinuousLinearMap.ofClass (finiteVectorFunctional M ξ)).toContinuousLinearMap,
    continuous_vnaWOTBall_eval_of_finite_coefficients M R _ ?_, hξ⟩
  refine ⟨n, ξ, ξ, fun _ => 1, ?_⟩
  intro a
  change finiteVectorFunctional M ξ a = ∑ i, (1 : ℂ) * ⟪ξ i, (a : H →L[ℂ] H) (ξ i)⟫_ℂ
  simpa only [one_mul] using finiteVectorFunctional_apply M ξ a

/-- Actual completed-GNS diagonal coefficients, pulled back to original M. -/
theorem continuous_gns_diagonal_on_vnaWOTBall
    (M : VonNeumannAlgebra H) (R : ℝ) (hR : 0 ≤ R)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ) (x : φ.GNS) :
    Continuous (fun T : vnaWOTBall M R =>
      inner ℂ x (φ.gnsStarAlgHom (vnaWOTBallElement T) x)) :=
  continuous_vnaWOTBall_eval_of_positive_normal M R hR (gnsVectorPositiveLinearMap M φ x)
    (gns_vectorFunctional_isNormal M φ hn x)

/-- Complex polarization uses the actual linear operator; self-adjointness
of the observable is not assumed. Both vector arguments range over all GNS. -/
theorem continuous_gns_coefficient_on_vnaWOTBall
    (M : VonNeumannAlgebra H) (R : ℝ) (hR : 0 ≤ R)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ) (x y : φ.GNS) :
    Continuous (fun T : vnaWOTBall M R =>
      inner ℂ x (φ.gnsStarAlgHom (vnaWOTBallElement T) y)) := by
  let q (z : φ.GNS) (T : vnaWOTBall M R) : ℂ :=
    inner ℂ (φ.gnsStarAlgHom (vnaWOTBallElement T) z) z
  have hq (z : φ.GNS) : Continuous (q z) := by
    simpa only [Function.comp_def, inner_conj_symm, q] using
      Complex.continuous_conj.comp (continuous_gns_diagonal_on_vnaWOTBall M R hR φ hn z)
  have he : (fun T : vnaWOTBall M R =>
      inner ℂ x (φ.gnsStarAlgHom (vnaWOTBallElement T) y)) =
      fun T => conj ((q (x + y) T - q (x - y) T +
        Complex.I * q (x + Complex.I • y) T - Complex.I * q (x - Complex.I • y) T) / 4) := by
    funext T
    calc
      _ = conj (inner ℂ (φ.gnsStarAlgHom (vnaWOTBallElement T) y) x) :=
        (inner_conj_symm _ _).symm
      _ = _ := congrArg conj
        (inner_map_polarization (φ.gnsStarAlgHom (vnaWOTBallElement T)).toLinearMap x y)
  rw [he]
  have hpoly := (((hq (x + y)).sub (hq (x - y))).add
    ((hq (x + Complex.I • y)).const_mul Complex.I)).sub
      ((hq (x - Complex.I • y)).const_mul Complex.I)
  exact Complex.continuous_conj.comp (hpoly.div_const 4)

/-- The actual representation is WOT-continuous on each bounded original ball.
No faithfulness or unit normalization is needed for this continuity assertion. -/
theorem continuous_gns_on_vnaWOTBall
    (M : VonNeumannAlgebra H) (R : ℝ) (hR : 0 ≤ R)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ) :
    Continuous (fun T : vnaWOTBall M R =>
      ContinuousLinearMapWOT.ofCLM (φ.gnsStarAlgHom (vnaWOTBallElement T))) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  exact continuous_gns_coefficient_on_vnaWOTBall M R hR φ hn y x

end VacuumBellSeparation.Bipartite
