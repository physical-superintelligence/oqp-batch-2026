module

public import CGLMPBounds.Defs.Quantum

@[expose] public section


/-!
# Factoring a finite orthogonal projection as an isometry times its adjoint

We reuse Mathlib's Hermitian spectral theorem. Idempotence forces every spectral
value to be zero or one, and selecting the eigenvalue-one columns gives the
rectangular isometry. This includes the zero projection and zero-dimensional range.
-/

open Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
namespace CGLMPBounds
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_projection_isometry_factor (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hP2 : P * P = P) :
    ∃ (k : ℕ) (B : Matrix ι (Fin k) ℂ), Bᴴ * B = 1 ∧ B * Bᴴ = P := by
  classical
  let v : ι → ℂ := RCLike.ofReal ∘ hP.eigenvalues
  let U : Matrix ι ι ℂ := hP.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hP.eigenvectorUnitary
  have hdiag : Matrix.diagonal v * Matrix.diagonal v = Matrix.diagonal v := by
    have he := congrArg
      (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) (star hP.eigenvectorUnitary)) hP2
    simpa only [map_mul, hP.conjStarAlgAut_star_eigenvectorUnitary] using he
  have hv : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i
    have hi := congrArg (fun M : Matrix ι ι ℂ => M i i) hdiag
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Pi.mul_apply] at hi
    have hz : v i * (v i - 1) = 0 := by rw [mul_sub, hi, mul_one, sub_self]
    exact (mul_eq_zero.mp hz).imp_right sub_eq_zero.mp
  let s : Finset ι := Finset.univ.filter (fun i => v i = 1)
  have hvs (i : ι) : v i = if i ∈ s then 1 else 0 := by
    by_cases hi : v i = 1
    · simp [s, hi]
    · have hz : v i = 0 := (hv i).resolve_right hi
      simp [s, hi, hz]
  let k := Fintype.card s
  let e : Fin k ≃ s := (Fintype.equivFin s).symm
  let B : Matrix ι (Fin k) ℂ := Matrix.of fun i j => U i (e j).val
  have hBB : Bᴴ * B = 1 := by
    ext i j
    have he := congrArg (fun M : Matrix ι ι ℂ => M (e i).val (e j).val) hU
    have hinj : (e i).val = (e j).val ↔ i = j :=
      ⟨fun h => e.injective (Subtype.ext h), fun h => congrArg (fun x => (e x).val) h⟩
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      B, Matrix.of_apply, hinj] using he
  have hfactor : B * Bᴴ = U * Matrix.diagonal v * Uᴴ := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, B, Matrix.of_apply]
    change (∑ a : Fin k, U i (e a).val * star (U j (e a).val)) =
      ∑ a : ι, (U * Matrix.diagonal v) i a * star (U j a)
    rw [Fintype.sum_equiv e (fun a => U i (e a).val * star (U j (e a).val))
      (fun a => U i a.val * star (U j a.val)) (fun _ => rfl)]
    rw [← Finset.sum_subtype s (fun _ => Iff.rfl) (fun a => U i a * star (U j a))]
    rw [show s = Finset.univ.filter (fun i => v i = 1) from rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.mul_diagonal]
    rcases hv a with ha | ha <;> simp [ha]
  have hspec : P = U * Matrix.diagonal v * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hP.spectral_theorem
  exact ⟨k, B, hBB, hfactor.trans hspec.symm⟩

end
end CGLMPBounds
