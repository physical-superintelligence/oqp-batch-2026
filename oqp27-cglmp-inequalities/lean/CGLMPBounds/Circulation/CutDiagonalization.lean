module

public import CGLMPBounds.Circulation.CutBasis

@[expose] public section


/-! A common unitary diagonalizes the original fourth-root tuple into literal cuts. -/

open Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
namespace CGLMPBounds.Circulation
noncomputable section
variable {d r : ℕ} [NeZero d] [NeZero r]

theorem exists_unitary_cut_diagonalization (V : Fin d → Mat r)
    (hunit : ∀ j, (V j)ᴴ * V j = 1) (hfour : ∀ j, V j ^ 4 = 1)
    (hzero : scalarForbiddenTotal V = 0) :
    ∃ (Q : Mat r) (a : Fin r → Fin 4) (j₀ : Fin r → Fin d),
      Qᴴ * Q = 1 ∧ Q * Qᴴ = 1 ∧ ∀ j,
      V j = Q * Matrix.diagonal (fun k =>
        Complex.I ^ (fourthRootCutLabels (a k) (j₀ k) j).val) * Qᴴ := by
  obtain ⟨b, a, j₀, hb⟩ := exists_orthonormal_cut_basis V hunit hfour hzero
  let Q : Mat r := (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.toMatrix b
  have hQ : Qᴴ * Q = 1 :=
    (EuclideanSpace.basisFun (Fin r) ℂ).toMatrix_orthonormalBasis_conjTranspose_mul_self b
  have hQ' : Q * Qᴴ = 1 :=
    (EuclideanSpace.basisFun (Fin r) ℂ).toMatrix_orthonormalBasis_self_mul_conjTranspose b
  have hQapply (i k : Fin r) : Q i k = (b k) i := rfl
  refine ⟨Q, a, j₀, hQ, hQ', ?_⟩
  intro j
  let D : Mat r := Matrix.diagonal (fun k =>
    Complex.I ^ (fourthRootCutLabels (a k) (j₀ k) j).val)
  have hVQ : V j * Q = Q * D := by
    ext i k
    rw [Matrix.mul_apply]
    change (∑ l, V j i l * Q l k) =
      (Q * Matrix.diagonal (fun k => Complex.I ^
        (fourthRootCutLabels (a k) (j₀ k) j).val)) i k
    rw [Matrix.mul_diagonal]
    simp only [hQapply]
    have hi := congrArg (fun x : EuclideanSpace ℂ (Fin r) => x i) (hb k j)
    change (∑ l, V j i l * (b k) l) =
      Complex.I ^ (fourthRootCutLabels (a k) (j₀ k) j).val * (b k) i at hi
    simpa only [mul_comm] using hi
  calc
    V j = V j * (Q * Qᴴ) := by rw [hQ', Matrix.mul_one]
    _ = (Q * D) * Qᴴ := by rw [← Matrix.mul_assoc, hVQ]
    _ = _ := rfl

end
end CGLMPBounds.Circulation
