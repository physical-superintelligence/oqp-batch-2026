module

public import ThreeCopyQutritWerner.PartialTraceLinear

@[expose] public section


/-!
# Coherent-reserve polarization and exact four-phase cancellation

All quantities are the actual three-site contractions. The phase average is
a four-term identity, requiring no integration or limiting argument.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Frobenius polarization after an arbitrary actual complex linear map. -/
theorem coherent_frob_linear_mix {p q m n : Type*}
    [Fintype p] [Fintype q] [Fintype m] [Fintype n]
    (L : Matrix p q ℂ →ₗ[ℂ] Matrix m n ℂ)
    (A B : Matrix p q ℂ) (s t : ℝ) :
    frobSq (L ((s : ℂ) • A + (t : ℂ) • B)) =
      s ^ 2 * frobSq (L A) + t ^ 2 * frobSq (L B) +
        2 * s * t * (hsInner (L A) (L B)).re := by
  rw [map_add, map_smul, map_smul, zeroReserve_frobSq_real_mix]

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- The actual real polarization of the reserve in the original physical coordinates. -/
def coherentReserveMixed (A B : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  (3 * (hsInner A B).re -
    2 * ((hsInner (ptrace₁ A) (ptrace₁ B)).re +
      (hsInner (ptrace₂ A) (ptrace₂ B)).re + (hsInner (ptrace₃ A) (ptrace₃ B)).re) +
    ((hsInner (ptrace₁₂ A) (ptrace₁₂ B)).re +
      (hsInner (ptrace₁₃ A) (ptrace₁₃ B)).re + (hsInner (ptrace₂₃ A) (ptrace₂₃ B)).re)) / 4

/-- Real polarization of the literal reserve, for arbitrary matrices and real weights. -/
theorem zeroReserve_real_mix (A B : Matrix (a × b × c) (a × b × c) ℂ) (s t : ℝ) :
    zeroReserve ((s : ℂ) • A + (t : ℂ) • B) =
      s ^ 2 * zeroReserve A + t ^ 2 * zeroReserve B +
        2 * s * t * coherentReserveMixed A B := by
  have hN := zeroReserve_frobSq_real_mix A B s t
  have h1 := coherent_frob_linear_mix ptrace₁LinearMap A B s t
  have h2 := coherent_frob_linear_mix ptrace₂LinearMap A B s t
  have h3 := coherent_frob_linear_mix ptrace₃LinearMap A B s t
  have h4 := coherent_frob_linear_mix ptrace₁₂LinearMap A B s t
  have h5 := coherent_frob_linear_mix ptrace₁₃LinearMap A B s t
  have h6 := coherent_frob_linear_mix ptrace₂₃LinearMap A B s t
  change frobSq (ptrace₁ ((s : ℂ) • A + (t : ℂ) • B)) =
    s ^ 2 * frobSq (ptrace₁ A) + t ^ 2 * frobSq (ptrace₁ B) +
      2 * s * t * (hsInner (ptrace₁ A) (ptrace₁ B)).re at h1
  change frobSq (ptrace₂ ((s : ℂ) • A + (t : ℂ) • B)) =
    s ^ 2 * frobSq (ptrace₂ A) + t ^ 2 * frobSq (ptrace₂ B) +
      2 * s * t * (hsInner (ptrace₂ A) (ptrace₂ B)).re at h2
  change frobSq (ptrace₃ ((s : ℂ) • A + (t : ℂ) • B)) =
    s ^ 2 * frobSq (ptrace₃ A) + t ^ 2 * frobSq (ptrace₃ B) +
      2 * s * t * (hsInner (ptrace₃ A) (ptrace₃ B)).re at h3
  change frobSq (ptrace₁₂ ((s : ℂ) • A + (t : ℂ) • B)) =
    s ^ 2 * frobSq (ptrace₁₂ A) + t ^ 2 * frobSq (ptrace₁₂ B) +
      2 * s * t * (hsInner (ptrace₁₂ A) (ptrace₁₂ B)).re at h4
  change frobSq (ptrace₁₃ ((s : ℂ) • A + (t : ℂ) • B)) =
    s ^ 2 * frobSq (ptrace₁₃ A) + t ^ 2 * frobSq (ptrace₁₃ B) +
      2 * s * t * (hsInner (ptrace₁₃ A) (ptrace₁₃ B)).re at h5
  change frobSq (ptrace₂₃ ((s : ℂ) • A + (t : ℂ) • B)) =
    s ^ 2 * frobSq (ptrace₂₃ A) + t ^ 2 * frobSq (ptrace₂₃ B) +
      2 * s * t * (hsInner (ptrace₂₃ A) (ptrace₂₃ B)).re at h6
  unfold zeroReserve invN invA invB coherentReserveMixed
  rw [hN, h1, h2, h3, h4, h5, h6]
  ring

/-- Homogeneity for an arbitrary complex scalar. -/
theorem zeroReserve_smul (A : Matrix (a × b × c) (a × b × c) ℂ) (z : ℂ) :
    zeroReserve (z • A) = Complex.normSq z * zeroReserve A := by
  simp only [zeroReserve, invN, invA, invB, ptrace₁_smul, ptrace₂_smul,
    ptrace₃_smul, ptrace₁₂_smul, ptrace₁₃_smul, ptrace₂₃_smul, frobSq_smul]
  ring

/-- Taking adjoints preserves the actual reserve. -/
theorem zeroReserve_conjTranspose (A : Matrix (a × b × c) (a × b × c) ℂ) :
    zeroReserve Aᴴ = zeroReserve A := by
  simp only [zeroReserve, invN, invA, invB, ptrace₁_conjTranspose,
    ptrace₂_conjTranspose, ptrace₃_conjTranspose, ptrace₁₂_conjTranspose,
    ptrace₁₃_conjTranspose, ptrace₂₃_conjTranspose, singular_frobSq_conjTranspose]

/-- The parallelogram law holds despite the reserve's signed coefficients. -/
theorem zeroReserve_parallelogram (A B : Matrix (a × b × c) (a × b × c) ℂ) :
    zeroReserve (A + B) + zeroReserve (A - B) =
      2 * zeroReserve A + 2 * zeroReserve B := by
  have hp := zeroReserve_real_mix A B 1 1
  have hm := zeroReserve_real_mix A B 1 (-1)
  norm_num only [Complex.ofReal_one, Complex.ofReal_neg, one_smul, neg_smul,
    one_pow, neg_one_sq, one_mul, sub_eq_add_neg] at hp hm
  rw [sub_eq_add_neg]
  linarith

/-- Exact cancellation at phases 1,-1,i,-i. No sign hypothesis is used. -/
theorem zeroReserve_four_phase (A C : Matrix (a × b × c) (a × b × c) ℂ) :
    zeroReserve (A + (C + Cᴴ)) + zeroReserve (A - (C + Cᴴ)) +
      zeroReserve (A + Complex.I • (C - Cᴴ)) +
      zeroReserve (A - Complex.I • (C - Cᴴ)) =
        4 * zeroReserve A + 8 * zeroReserve C := by
  have h1 := zeroReserve_parallelogram A (C + Cᴴ)
  have h2 := zeroReserve_parallelogram A (Complex.I • (C - Cᴴ))
  have h3 := zeroReserve_parallelogram C Cᴴ
  rw [zeroReserve_smul, Complex.normSq_I, one_mul] at h2
  rw [zeroReserve_conjTranspose] at h3
  linarith

end ThreeCopyQutritWerner

