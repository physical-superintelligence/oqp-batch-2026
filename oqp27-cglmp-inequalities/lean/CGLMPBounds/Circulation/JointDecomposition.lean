module

public import CGLMPBounds.Circulation.Rigidity
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.Matrix.Hermitian

@[expose] public section


/-!
# The common spectral decomposition at equality

The Mathlib joint-eigenspace theorem is applied to the actual Hermitian
spectral projections. Pairwise commutation follows from the forbidden
overlaps, including the same-site case by PVM orthogonality.
-/

open Matrix

namespace CGLMPBounds.Circulation
noncomputable section
variable {d r : ℕ}

lemma spectral_pairwise_commute_of_forbidden_zero [NeZero r] (V : Fin d → Mat r)
    (hunit : ∀ i, (V i)ᴴ * V i = 1) (hfour : ∀ i, V i ^ 4 = 1)
    (hzero : ∀ i j, i < j → forbidden (V i) (V j) = 0) :
    ∀ i j a b, spectral (V i) a * spectral (V j) b =
      spectral (V j) b * spectral (V i) a := by
  intro i j a b
  have hp (k : Fin d) : IsPVM (spectral (V k)) := spectral_isPVM (hunit k) (hfour k)
  rcases lt_trichotomy i j with hij | hij | hji
  · exact forbidden_root_eq_zero_commute _ _ (hp i) (hp j)
      (by simpa only [root_spectral] using hzero i j hij) a b
  · subst j
    by_cases hab : a = b
    · subst b; rfl
    · rw [(hp i).mul_eq_zero (Ne.symm hab), (hp i).mul_eq_zero hab]
  · exact (forbidden_root_eq_zero_commute _ _ (hp j) (hp i)
      (by simpa only [root_spectral] using hzero j i hji) b a).symm

/-- The joint eigenspaces of all spectral projections span the original
Hilbert space. This includes arbitrary multiplicities and zero projections. -/
theorem fourth_root_joint_eigenspaces_span [NeZero r] (V : Fin d → Mat r)
    (hunit : ∀ i, (V i)ᴴ * V i = 1) (hfour : ∀ i, V i ^ 4 = 1)
    (hzero : ∀ i j, i < j → forbidden (V i) (V j) = 0) :
    (⨆ χ : Fin d × Fin 4 → ℂ, ⨅ ia : Fin d × Fin 4,
      Module.End.eigenspace (spectral (V ia.1) ia.2).toEuclideanLin (χ ia)) = ⊤ := by
  apply LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute
  · intro ia
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((spectral_isPVM (hunit ia.1) (hfour ia.1)).isHermitian ia.2)
  · intro ia jb _
    change (spectral (V ia.1) ia.2).toEuclideanLin *
        (spectral (V jb.1) jb.2).toEuclideanLin =
      (spectral (V jb.1) jb.2).toEuclideanLin *
        (spectral (V ia.1) ia.2).toEuclideanLin
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, Module.End.mul_eq_comp]
      using congrArg (Matrix.toLpLin 2 2)
        (spectral_pairwise_commute_of_forbidden_zero V hunit hfour hzero ia.1 jb.1 ia.2 jb.2)

end
end CGLMPBounds.Circulation
