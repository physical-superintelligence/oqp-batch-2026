module

public import ThreeCopyQutritWerner.CertificateX2Reduced
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section


/-!
# The parts argument over the complex numbers

The same statements as CertificateX2BridgeRank and CertificateX2BridgeHSide, for complex
matrices and conjugate transposes, so that they apply directly to the frame-coordinate h-side
forms `πᴴ (T - Q₁ - Q₂) π` of `x2_qutritEndpointInequality_of_hside` (CertificateX2BridgeMain),
where `π` is the carrier's joint action `certificateCarrierJointAction0`.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

theorem x2_idempotent_eq_mul_of_trace_complex {n r : Type*} [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r] (P : Matrix n n ℂ) (hP : P * P = P) (J : Matrix n r ℂ)
    (hPJ : P * J = J) (L : Matrix r n ℂ) (hLJ : L * J = 1)
    (htr : P.trace = (Fintype.card r : ℂ)) :
    ∃ A : Matrix r n ℂ, P = J * A := by
  have hidem : IsIdempotentElem (Matrix.toLin' P) := by
    show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  have hproj := LinearMap.IsIdempotentElem.isProj_range (Matrix.toLin' P) hidem
  have htrace := hproj.trace
  rw [Matrix.trace_toLin'_eq, htr] at htrace
  have hfr : Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) = Fintype.card r := by
    exact_mod_cast htrace.symm
  have hJinj : Function.Injective (Matrix.toLin' J) := by
    intro x y hxy
    have h := congrArg (Matrix.toLin' L) hxy
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hLJ, Matrix.one_mulVec] at h
    exact h
  have hJr : Module.finrank ℂ (LinearMap.range (Matrix.toLin' J)) = Fintype.card r := by
    rw [LinearMap.finrank_range_of_inj hJinj, Module.finrank_fintype_fun_eq_card]
  have hle : LinearMap.range (Matrix.toLin' J) ≤ LinearMap.range (Matrix.toLin' P) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨Matrix.toLin' J x, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hPJ]
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hJr, hfr])
  have hcol : ∀ j : n, ∃ a : r → ℂ, J *ᵥ a = fun i => P i j := by
    intro j
    have hmem : (fun i => P i j) ∈ LinearMap.range (Matrix.toLin' P) := by
      refine ⟨Pi.single j 1, ?_⟩
      funext i
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [← heq] at hmem
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, by simpa only [Matrix.toLin'_apply] using ha⟩
  choose a ha using hcol
  refine ⟨Matrix.of fun i j => a j i, ?_⟩
  ext i j
  have h := congrFun (ha j) i
  simp only [Matrix.mulVec, dotProduct] at h
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact h.symm

theorem x2_eq_mul_of_fix_trace_det_complex {n r : Type*} [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r] (P : Matrix n n ℂ) (hP : P * P = P) (M : Matrix n r ℂ)
    (hPM : P * M = M) (G : Matrix n n ℂ) (hdet : (Mᴴ * G * M).det ≠ 0)
    (htr : P.trace = (Fintype.card r : ℂ)) :
    ∃ A : Matrix r n ℂ, P = M * A := by
  refine x2_idempotent_eq_mul_of_trace_complex P hP M hPM ((Mᴴ * G * M)⁻¹ * (Mᴴ * G)) ?_ htr
  rw [Matrix.mul_assoc ((Mᴴ * G * M)⁻¹) (Mᴴ * G) M]
  exact Matrix.nonsing_inv_mul _ (Ne.isUnit hdet)

/-- POSITIVITY FROM PARTS (complex form). -/
theorem x2_posSemidef_of_parts_complex {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
    [DecidableEq κ] (π f G : Matrix n n ℂ) (P : κ → Matrix n n ℂ)
    (hsum : ∑ k, P k = 1) (hπ : π * π = π) (hπP : ∀ k, π * P k = P k * π)
    (hPP : ∀ k l, P k * P l = if k = l then P k else 0) (hPt : ∀ k, (P k)ᴴ = P k)
    (hfP : ∀ k, f * P k = P k * f)
    {r : κ → Type*} [∀ k, Fintype (r k)] [∀ k, DecidableEq (r k)]
    (M : (k : κ) → Matrix n (r k) ℂ) (hM : ∀ k, π * P k * M k = M k)
    (hdet : ∀ k, ((M k)ᴴ * G * M k).det ≠ 0)
    (htr : ∀ k, (π * P k).trace = (Fintype.card (r k) : ℂ))
    (hpsd : ∀ k, ((M k)ᴴ * f * M k).PosSemidef) :
    (πᴴ * f * π).PosSemidef := by
  have hidem : ∀ k, (π * P k) * (π * P k) = π * P k := by
    intro k
    calc (π * P k) * (π * P k) = π * (P k * π) * P k := by simp only [Matrix.mul_assoc]
      _ = π * (π * P k) * P k := by rw [hπP k]
      _ = (π * π) * (P k * P k) := by simp only [Matrix.mul_assoc]
      _ = π * P k := by rw [hπ, hPP k k, if_pos rfl]
  have hfac : ∀ k, ∃ A : Matrix (r k) n ℂ, π * P k = M k * A := fun k =>
    x2_eq_mul_of_fix_trace_det_complex (π * P k) (hidem k) (M k) (hM k) G (hdet k) (htr k)
  choose A hA using hfac
  have hcross : ∀ k l, k ≠ l → (π * P k)ᴴ * f * (π * P l) = 0 := by
    intro k l hkl
    rw [hπP k, Matrix.conjTranspose_mul, hPt k]
    calc πᴴ * P k * f * (π * P l) = πᴴ * (P k * f) * (π * P l) := by
          simp only [Matrix.mul_assoc]
      _ = πᴴ * (f * P k) * (P l * π) := by rw [hfP k, hπP l]
      _ = πᴴ * f * (P k * P l) * π := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hPP k l, if_neg hkl, Matrix.mul_zero, Matrix.zero_mul]
  have hπsum : π = ∑ k, π * P k := by rw [← Matrix.mul_sum, hsum, Matrix.mul_one]
  have hexp : πᴴ * f * π = ∑ k, (π * P k)ᴴ * f * (π * P k) := by
    have h1 : πᴴ * f * π = ∑ k, ∑ l, (π * P k)ᴴ * f * (π * P l) := by
      conv_lhs => rw [hπsum]
      rw [Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.mul_sum]
    rw [h1]
    apply Finset.sum_congr rfl
    intro k _
    exact Fintype.sum_eq_single k (fun l hl => hcross k l (Ne.symm hl))
  rw [hexp]
  apply Matrix.posSemidef_sum
  intro k _
  have he : (π * P k)ᴴ * f * (π * P k) = (A k)ᴴ * ((M k)ᴴ * f * M k) * A k := by
    rw [hA k, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [he]
  exact (hpsd k).conjTranspose_mul_mul_same (A k)

end ThreeCopyQutritWerner

end
