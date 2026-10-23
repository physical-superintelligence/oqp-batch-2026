module

public import CGLMPBounds.CGLMP.FourierRestriction

@[expose] public section


/-!
# Descending a standard amplification through a common reducing isometry

This is the final linear-algebra step of Appendix E.1. A common physical
standardizer and a common reducing isometry produce one unitary in the original
coordinates, together with n=d*k. All intermediate maps are actual matrices.
-/

open Matrix
open scoped Kronecker ComplexOrder
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
namespace CGLMPBounds
noncomputable section
variable {Ω κ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype κ] [DecidableEq κ]
variable (d : ℕ) [NeZero d]

theorem standard_fourier_descent {n : ℕ}
    (M : Fin 4 → ZMod d → Matrix Ω Ω ℂ)
    (P : Fin 4 → ZMod d → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix Ω (Fin d × κ) ℂ) (hT : Tᴴ * T = 1) (hT' : T * Tᴴ = 1)
    (hM : ∀ t a, M t a = T * (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) * Tᴴ)
    (Z : Matrix Ω (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (hinter : ∀ t a, M t a * Z = Z * P t a)
    (hcomm : ∀ t a, Commute (M t a) (Z * Zᴴ)) :
    ∃ (k : ℕ) (U : Matrix (Fin n) (Fin d × Fin k) ℂ),
      n = d * k ∧ U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
      ∀ (t : Fin 4) (a : ZMod d),
        P t a = U * (fourierProjector d t.val a ⊗ₖ
          (1 : Matrix (Fin k) (Fin k) ℂ)) * Uᴴ := by
  let W : Matrix (Fin d × κ) (Fin n) ℂ := Tᴴ * Z
  have hW : Wᴴ * W = 1 := by
    dsimp only [W]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      (Zᴴ * T) * (Tᴴ * Z) = Zᴴ * (T * Tᴴ) * Z := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hT', Matrix.mul_one, hZ]
  have hTF (t : Fin 4) (a : ZMod d) :
      T * (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) = M t a * T := by
    rw [hM]
    simp only [Matrix.mul_assoc, hT, Matrix.mul_one]
  have hFT (t : Fin 4) (a : ZMod d) :
      (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) * Tᴴ = Tᴴ * M t a := by
    rw [hM]
    calc
      _ = (Tᴴ * T) * (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) * Tᴴ := by
        rw [hT, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hcommW (t : Fin 4) (a : ZMod d) :
      (W * Wᴴ) * (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) =
        (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) * (W * Wᴴ) := by
    let F := fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)
    have hrange : W * Wᴴ = Tᴴ * (Z * Zᴴ) * T := by
      simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    rw [hrange]
    change (Tᴴ * (Z * Zᴴ) * T) * F = F * (Tᴴ * (Z * Zᴴ) * T)
    calc
      _ = Tᴴ * (Z * Zᴴ) * (T * F) := by simp only [Matrix.mul_assoc]
      _ = Tᴴ * ((Z * Zᴴ) * M t a) * T := by
        rw [hTF]; simp only [Matrix.mul_assoc]
      _ = Tᴴ * (M t a * (Z * Zᴴ)) * T := by rw [(hcomm t a).eq]
      _ = (Tᴴ * M t a) * (Z * Zᴴ) * T := by simp only [Matrix.mul_assoc]
      _ = (F * Tᴴ) * (Z * Zᴴ) * T := by rw [← hFT]
      _ = _ := by simp only [Matrix.mul_assoc]
  obtain ⟨k, U, hdim, hU, hU', hstd⟩ := standard_fourier_restriction d W hW hcommW
  refine ⟨k, U, hdim, hU, hU', ?_⟩
  intro t a
  have hcompress : Wᴴ * (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) * W = P t a := by
    dsimp only [W]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = Zᴴ * (T * (fourierProjector d t.val a ⊗ₖ (1 : Matrix κ κ ℂ)) * Tᴴ) * Z := by
        simp only [Matrix.mul_assoc]
      _ = Zᴴ * (M t a * Z) := by rw [← hM]; simp only [Matrix.mul_assoc]
      _ = P t a := by rw [hinter, ← Matrix.mul_assoc, hZ, Matrix.one_mul]
  exact hcompress.symm.trans (hstd t a)

end
end CGLMPBounds
