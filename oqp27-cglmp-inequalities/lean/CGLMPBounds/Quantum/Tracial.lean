module

public import CGLMPBounds.Defs.Quantum

@[expose] public section


/-!
# Tracial behaviours of projective measurements are no-signalling behaviours

For projective measurements on `Φ_n` (`n ≥ 1`), the table `q(a,b|x,y) = n⁻¹ Tr(A_x(a) B_y(b))`
is nonnegative, normalised in every context, and no-signalling (Letter: "Quantum behaviours obey
no signalling").

* `re_trace_mul_nonneg` : `Tr(PQ) ≥ 0` for orthogonal projections, via `Tr(PQ) = Tr((PQ)ᴴ PQ)`;
* `tracialTable_isNoSignalling`.
-/

open scoped ComplexOrder
open Matrix

namespace CGLMPBounds

noncomputable section

variable {n : ℕ}

/-- The trace of a product of two orthogonal projections has nonnegative real part. -/
theorem re_trace_mul_nonneg {P Q : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (hP2 : P * P = P) (hQ : Q.IsHermitian) (hQ2 : Q * Q = Q) :
    0 ≤ (Matrix.trace (P * Q)).re := by
  have key : Matrix.trace (P * Q) = Matrix.trace ((P * Q)ᴴ * (P * Q)) := by
    rw [Matrix.conjTranspose_mul, hP.eq, hQ.eq, Matrix.mul_assoc, ← Matrix.mul_assoc P P Q, hP2,
      Matrix.trace_mul_comm Q (P * Q), Matrix.mul_assoc, hQ2]
  have h0 : (0 : ℂ) ≤ Matrix.trace ((P * Q)ᴴ * (P * Q)) :=
    (Matrix.posSemidef_conjTranspose_mul_self (P * Q)).trace_nonneg
  rw [key]
  exact (Complex.nonneg_iff.mp h0).1

variable {α β : Type*} [Fintype α] [Fintype β]

theorem sum_right_re_trace_mul {A : Matrix (Fin n) (Fin n) ℂ} {B : β → Matrix (Fin n) (Fin n) ℂ}
    (hB : ∑ b, B b = 1) : ∑ b, (Matrix.trace (A * B b)).re = (Matrix.trace A).re := by
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, hB, Matrix.mul_one]

theorem sum_left_re_trace_mul {A : α → Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∑ a, A a = 1) : ∑ a, (Matrix.trace (A a * B)).re = (Matrix.trace B).re := by
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hA, Matrix.one_mul]

/-- Behaviours of projective measurements on `Φ_n` (`n ≥ 1`) are no-signalling behaviours. -/
theorem tracialTable_isNoSignalling [NeZero n] {A : Fin 2 → α → Matrix (Fin n) (Fin n) ℂ}
    {B : Fin 2 → β → Matrix (Fin n) (Fin n) ℂ} (hA : ∀ x, IsPVM (A x)) (hB : ∀ y, IsPVM (B y)) :
    IsNoSignalling (tracialTable A B) where
  isBehaviour :=
    { nonneg := fun x y a b =>
        div_nonneg (re_trace_mul_nonneg ((hA x).isHermitian a) ((hA x).mul_self a)
          ((hB y).isHermitian b) ((hB y).mul_self b)) (Nat.cast_nonneg _)
      sum_eq_one := fun x y => by
        have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
        calc ∑ a, ∑ b, (Matrix.trace (A x a * B y b)).re / (n : ℝ)
            = ∑ a, (Matrix.trace (A x a)).re / (n : ℝ) := by
              refine Finset.sum_congr rfl (fun a _ => ?_)
              rw [← Finset.sum_div, sum_right_re_trace_mul (hB y).sum_eq_one]
          _ = (Matrix.trace (∑ a, A x a)).re / (n : ℝ) := by
              rw [← Finset.sum_div, ← Complex.re_sum, ← Matrix.trace_sum]
          _ = 1 := by
              rw [(hA x).sum_eq_one, Matrix.trace_one, Fintype.card_fin, Complex.natCast_re,
                div_self hn] }
  margA_indep := fun x y y' a => by
    simp only [tracialTable]
    rw [← Finset.sum_div, ← Finset.sum_div, sum_right_re_trace_mul (hB y).sum_eq_one,
      sum_right_re_trace_mul (hB y').sum_eq_one]
  margB_indep := fun x x' y b => by
    simp only [tracialTable]
    rw [← Finset.sum_div, ← Finset.sum_div, sum_left_re_trace_mul (hA x).sum_eq_one,
      sum_left_re_trace_mul (hA x').sum_eq_one]

end

end CGLMPBounds
