module

public import ThreeCopyQutritWerner.TwoCutRotate
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


/-!
# Extending an actual pair of orthonormal families

Two equally indexed orthonormal families in the same finite complex coordinate
space are related by a square unitary matrix. The finite-dimensional isometry
extension theorem supplies the complement; no completion is an input.
-/

noncomputable section

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Coordinate pairing agrees with the genuine Euclidean inner product. -/
theorem braket_eq_euclidean_inner {n : Type*} [Fintype n] (u v : n → ℂ) :
    braket u v = inner ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 v) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, braket, dotProduct,
    Complex.star_def, mul_comm]

/-- Any finite orthonormal family induces an actual isometric coordinate embedding. -/
theorem orthonormalFamily_exists_isometry {n k : Type*} [Fintype n] [Fintype k]
    [DecidableEq k]
    (u : k → n → ℂ) (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0) :
    ∃ f : EuclideanSpace ℂ k →ₗᵢ[ℂ] EuclideanSpace ℂ n,
      ∀ j, f (EuclideanSpace.basisFun k ℂ j) = WithLp.toLp 2 (u j) := by
  classical
  let b := EuclideanSpace.basisFun k ℂ
  let L := b.toBasis.constr ℂ (fun j => WithLp.toLp 2 (u j))
  have hLb (j : k) : L (b.toBasis j) = WithLp.toLp 2 (u j) :=
    b.toBasis.constr_basis ℂ _ j
  have hL : Orthonormal ℂ (L ∘ b.toBasis) := by
    rw [orthonormal_iff_ite]
    intro i j
    change inner ℂ (L (b.toBasis i)) (L (b.toBasis j)) = _
    rw [hLb, hLb, ← braket_eq_euclidean_inner]
    exact hu i j
  have hb : Orthonormal ℂ b.toBasis := by
    simpa only [OrthonormalBasis.coe_toBasis] using b.orthonormal
  refine ⟨L.isometryOfOrthonormal hb hL, ?_⟩
  intro j
  rw [LinearMap.coe_isometryOfOrthonormal]
  exact hLb j

/-- A square unitary carrying every member of one actual orthonormal family to
the corresponding member of another, including an empty family or ambient space. -/
theorem orthonormalFamilies_exists_unitary {n k : Type*} [Fintype n] [Fintype k]
    [DecidableEq n] [DecidableEq k] (u v : k → n → ℂ)
    (hu : ∀ i j, braket (u i) (u j) = if i = j then 1 else 0)
    (hv : ∀ i j, braket (v i) (v j) = if i = j then 1 else 0) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ ∀ j, W *ᵥ v j = u j := by
  classical
  obtain ⟨fu, hfu⟩ := orthonormalFamily_exists_isometry u hu
  obtain ⟨fv, hfv⟩ := orthonormalFamily_exists_isometry v hv
  let L : (LinearMap.range fv.toLinearMap) →ₗᵢ[ℂ] EuclideanSpace ℂ n :=
    fu.comp fv.equivRange.symm.toLinearIsometry
  let F := L.extend
  have hF : ∀ j, F (WithLp.toLp 2 (v j)) = WithLp.toLp 2 (u j) := by
    intro j
    let s := fv.equivRange (EuclideanSpace.basisFun k ℂ j)
    have hs : (s : EuclideanSpace ℂ n) = WithLp.toLp 2 (v j) := by
      simpa [s] using hfv j
    rw [← hs]
    change L.extend s = _
    rw [LinearIsometry.extend_apply]
    simpa [L, s] using hfu j
  let b := EuclideanSpace.basisFun n ℂ
  let W := F.toLinearMap.toMatrix b.toBasis b.toBasis
  refine ⟨W, ?_, ?_⟩
  · ext i j
    have hcol : ∀ j, WithLp.toLp 2 (Wᵀ j) = F (b j) := by
      intro j
      ext i
      simp [W, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        EuclideanSpace.basisFun_repr, b]
    rw [← inner_matrix_col_col W W, hcol, hcol, F.inner_map_map]
    exact b.inner_eq_ite i j
  · intro j
    have h := F.toLinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis
      (WithLp.toLp 2 (v j))
    have hb : ⇑(b.toBasis.repr (WithLp.toLp 2 (v j))) = v j := by
      ext i
      rw [OrthonormalBasis.coe_toBasis_repr_apply]
      rfl
    ext i
    simpa only [W, hb, OrthonormalBasis.coe_toBasis_repr_apply,
      LinearIsometry.coe_toLinearMap, hF, EuclideanSpace.basisFun_repr, b,
      WithLp.ofLp_toLp] using congrFun h i

end ThreeCopyQutritWerner
