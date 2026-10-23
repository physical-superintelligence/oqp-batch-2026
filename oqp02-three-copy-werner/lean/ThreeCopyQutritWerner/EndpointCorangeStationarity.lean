module

public import ThreeCopyQutritWerner.EndpointSourceStationarity
public import ThreeCopyQutritWerner.PartialTraceLinear

@[expose] public section


/-!
# Original endpoint adjoint symmetry and corange stationarity

The literal physical operator has the real three-site kernel. Adjoint
symmetry therefore gives the corresponding complex corange gradient at a
rank-two zero. Endpoint nonnegativity remains an explicit open premise.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Actual entries of the physical endpoint operator, with its original normalization. -/
theorem endpointOperator_site_kernel (i j k l : QutritSites) :
    endpointOperator (i, j) (k, l) =
      siteKer (1 / 2) i.1 j.1 k.1 l.1 *
        siteKer (1 / 2) i.2.1 j.2.1 k.2.1 l.2.1 *
        siteKer (1 / 2) i.2.2 j.2.2 k.2.2 l.2.2 := by
  change (15 / 2 : ℂ)^3 *
    (partialTranspose (werner 3 (1 / 2)) (i.1, j.1) (k.1, l.1) *
      partialTranspose (werner 3 (1 / 2)) (i.2.1, j.2.1) (k.2.1, l.2.1) *
      partialTranspose (werner 3 (1 / 2)) (i.2.2, j.2.2) (k.2.2, l.2.2)) = _
  simp only [partialTranspose_werner_apply']
  norm_num <;> ring

/-- Swapping matrix row and column registers is conjugate-compatible. -/
theorem endpointOperator_swap_star (i j k l : QutritSites) :
    star (endpointOperator (j, i) (l, k)) = endpointOperator (i, j) (k, l) := by
  have hdelta (a b : Fin 3) :
      star (if a = b then (1 : ℂ) else 0) = (if a = b then (1 : ℂ) else 0) := by
    split_ifs <;> simp
  have hsite (a b c d : Fin 3) :
      star (siteKer (1 / 2) b a d c) = siteKer (1 / 2) a b c d := by
    simp only [siteKer, star_sub, star_mul, star_div₀, star_one, star_ofNat, hdelta]
    simp only [eq_comm]
    ring
  simp only [endpointOperator_site_kernel, star_mul, hsite]
  ring

/-- The actual endpoint image commutes with the ordinary matrix adjoint. -/
theorem endpointImage_conjTranspose (C : Matrix QutritSites QutritSites ℂ) :
    endpointImage Cᴴ = (endpointImage C)ᴴ := by
  ext i j
  simp only [endpointImage, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    vec, star_sum, star_mul']
  apply Fintype.sum_equiv (Equiv.prodComm QutritSites QutritSites)
  rintro ⟨k, l⟩
  change endpointOperator (i, j) (k, l) * star (C l k) =
    star (endpointOperator (j, i) (l, k)) * star (C l k)
  exact congrArg (fun z : ℂ => z * star (C l k))
    (endpointOperator_swap_star i j k l).symm

/-- Adjoint symmetry of the original three-site energy, at every parameter. -/
theorem energy_conjTranspose {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (alpha : ℝ) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    energy alpha Cᴴ = energy alpha C := by
  simp only [energy, invN, invA, invB, invT, ptrace₁_conjTranspose,
    ptrace₂_conjTranspose, ptrace₃_conjTranspose, ptrace₁₂_conjTranspose,
    ptrace₁₃_conjTranspose, ptrace₂₃_conjTranspose, singular_frobSq_conjTranspose,
    Matrix.trace_conjTranspose, Complex.star_def, Complex.normSq_conj]

/-- REDUCTION: every original rank-two zero annihilates the full complex
corange gradient as well as the source gradient. -/
theorem endpointCorange_zero_gradient (hendpoint : QutritEndpointInequality)
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hzero : endpointEnergy (X * Yᴴ) = 0) : endpointImage (X * Yᴴ) * Y = 0 := by
  have he : Y * Xᴴ = (X * Yᴴ)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hz : endpointEnergy (Y * Xᴴ) = 0 := by
    rw [he, endpointEnergy, energy_conjTranspose]
    exact hzero
  have hg := endpointSource_zero_gradient hendpoint Y Xᴴ hz
  have h := congrArg Matrix.conjTranspose hg
  rw [Matrix.conjTranspose_mul, he, endpointImage_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero] at h
  exact h

end ThreeCopyQutritWerner
