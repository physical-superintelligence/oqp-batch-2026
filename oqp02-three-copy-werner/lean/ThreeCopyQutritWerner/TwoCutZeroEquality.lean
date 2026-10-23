module

public import ThreeCopyQutritWerner.TwoCutBalanced
public import ThreeCopyQutritWerner.TwoCutFactor
public import ThreeCopyQutritWerner.RankOne

@[expose] public section


/-!
# Equality data for the two-site cut sum of squares

The original rank-at-most-two operator supplies balanced factors and the common
rotation supplies equal diagonal overlaps. A zero cut form then annihilates all
seven nonnegative terms. No three-site endpoint inequality is used here.
-/

noncomputable section

namespace ThreeCopyQutritWerner

variable {L R : Type*} [Fintype L] [Fintype R]

/-- Vanishing defect is the literal coordinatewise polarized-minor condition. -/
theorem biDefect_eq_zero_iff_biAnti_eq_zero (u v : L × R → ℂ) :
    biDefect u v = 0 ↔ biAnti u v = 0 := by
  constructor
  · intro h
    have hs : ∑ p, Complex.normSq (biAnti u v p) = 0 := by
      rw [← four_mul_biDefect, h, mul_zero]
    funext p
    exact Complex.normSq_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg
        (fun q _ => Complex.normSq_nonneg (biAnti u v q))).mp hs p (Finset.mem_univ p))
  · intro h
    have hs := four_mul_biDefect u v
    simp only [h, Pi.zero_apply, Complex.normSq_zero, Finset.sum_const_zero] at hs
    linarith

/-- The combined partial-trace square vanishes precisely when both traces do. -/
theorem ptraceNormSq_eq_zero_iff (X : Matrix (L × R) (L × R) ℂ) :
    ptraceNormSq X = 0 ↔ ptraceL X = 0 ∧ ptraceR X = 0 := by
  constructor
  · intro h
    have hL := frobSq_nonneg (ptraceL X)
    have hR := frobSq_nonneg (ptraceR X)
    unfold ptraceNormSq at h
    exact ⟨matrix_eq_zero_of_frobSq_eq_zero _ (by linarith),
      matrix_eq_zero_of_frobSq_eq_zero _ (by linarith)⟩
  · rintro ⟨hL, hR⟩
    simp [ptraceNormSq, hL, hR, frobSq]

/-- Equality in the normalized balanced identity annihilates every SOS term. -/
theorem cutForm_zero_balanced_terms (x₁ x₂ y₁ y₂ : L × R → ℂ)
    (h1 : vecNormSq x₁ = vecNormSq y₁) (h2 : vecNormSq x₂ = vecNormSq y₂)
    (hg : braket x₁ x₂ = braket y₁ y₂)
    (hτ : braket y₁ x₁ = braket y₂ x₂)
    (hz : cutForm (ketBra x₁ y₁ + ketBra x₂ y₂) = 0) :
    vecNormSq x₁ = vecNormSq x₂ ∧ braket x₁ x₂ = 0 ∧
      biDefect x₁ y₁ = 0 ∧ biDefect x₂ y₂ = 0 ∧
      biDefect x₂ x₁ = 0 ∧ biDefect y₂ y₁ = 0 ∧
      ptraceNormSq (ketBra x₂ x₁ - ketBra y₂ y₁) = 0 := by
  rw [cutForm_ketBra_add x₁ x₂ y₁ y₂ (vecNormSq x₁) (vecNormSq x₂)
    (braket x₁ x₂) (braket y₁ x₁) rfl h1.symm rfl h2.symm
    rfl hg.symm rfl hτ.symm] at hz
  have e1 := biDefect_nonneg x₁ y₁
  have e2 := biDefect_nonneg x₂ y₂
  have e3 := biDefect_nonneg x₂ x₁
  have e4 := biDefect_nonneg y₂ y₁
  have e5 := ptraceNormSq_nonneg (ketBra x₂ x₁ - ketBra y₂ y₁)
  have e6 := Complex.normSq_nonneg (braket x₁ x₂)
  have e7 := sq_nonneg (vecNormSq x₁ - vecNormSq x₂)
  have hs : (vecNormSq x₁ - vecNormSq x₂) ^ 2 = 0 := by linarith
  have hg0 : Complex.normSq (braket x₁ x₂) = 0 := by linarith
  exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hs), Complex.normSq_eq_zero.mp hg0,
    by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Actual cut zeros of rank at most two admit equal-norm orthogonal pairs
with all four polarized-minor tensors and both cross partial traces zero. -/
theorem cutForm_zero_exists_equal_orthogonal_factors [DecidableEq L] [DecidableEq R]
    (C : Matrix (L × R) (L × R) ℂ) (hC : C.rank ≤ 2) (hz : cutForm C = 0) :
    ∃ x₁ x₂ y₁ y₂ : L × R → ℂ,
      C = ketBra x₁ y₁ + ketBra x₂ y₂ ∧
      vecNormSq x₁ = vecNormSq x₂ ∧
      vecNormSq x₁ = vecNormSq y₁ ∧ vecNormSq x₂ = vecNormSq y₂ ∧
      braket x₁ x₂ = 0 ∧ braket y₁ y₂ = 0 ∧
      braket y₁ x₁ = braket y₂ x₂ ∧
      biAnti x₁ y₁ = 0 ∧ biAnti x₂ y₂ = 0 ∧
      biAnti x₂ x₁ = 0 ∧ biAnti y₂ y₁ = 0 ∧
      ptraceL (ketBra x₂ x₁ - ketBra y₂ y₁) = 0 ∧
      ptraceR (ketBra x₂ x₁ - ketBra y₂ y₁) = 0 := by
  obtain ⟨a₁, a₂, b₁, b₂, hsum, h1, h2, hg⟩ := exists_balanced_ketBra C hC
  obtain ⟨x₁, x₂, y₁, y₂, heq, hx1, hx2, hxg, hτ⟩ :=
    exists_equal_diagonal a₁ a₂ b₁ b₂ h1 h2 hg
  have hCx : C = ketBra x₁ y₁ + ketBra x₂ y₂ := hsum.trans heq.symm
  have hxz : cutForm (ketBra x₁ y₁ + ketBra x₂ y₂) = 0 := hCx ▸ hz
  obtain ⟨hd, hg0, he1, he2, he3, he4, hp⟩ :=
    cutForm_zero_balanced_terms x₁ x₂ y₁ y₂ hx1 hx2 hxg hτ hxz
  obtain ⟨hpL, hpR⟩ := (ptraceNormSq_eq_zero_iff _).mp hp
  exact ⟨x₁, x₂, y₁, y₂, hCx, hd, hx1, hx2, hg0, hxg.symm.trans hg0, hτ,
    (biDefect_eq_zero_iff_biAnti_eq_zero _ _).mp he1,
    (biDefect_eq_zero_iff_biAnti_eq_zero _ _).mp he2,
    (biDefect_eq_zero_iff_biAnti_eq_zero _ _).mp he3,
    (biDefect_eq_zero_iff_biAnti_eq_zero _ _).mp he4, hpL, hpR⟩

end ThreeCopyQutritWerner

end
