module

public import CGLMPBounds.Companion.Covariance
public import CGLMPBounds.Defs.CGLMP

@[expose] public section


/-!
# Outcome covariance preserves the Bell value

The normalized trace of the covariant construction is the uniform average of
simultaneous outcome translations. Every CGLMP residual is invariant under these
translations. This is the first Bell-value preservation step in Lemma C.1, p. 6;
the later clock averaging and Fourier coefficient identity are separate steps.
-/

open Matrix
namespace CGLMPBounds.Companion
noncomputable section

variable {d n : ℕ} [NeZero d]

def translateTable (q : Table (ZMod d) (ZMod d)) (k : ZMod d) :
    Table (ZMod d) (ZMod d) :=
  fun x y a b => q x y (a - k) (b - k)

def averageTable (q : Table (ZMod d) (ZMod d)) : Table (ZMod d) (ZMod d) :=
  fun x y a b => (∑ k, translateTable q k x y a b) / (d : ℝ)

/-- The tracial table of the covariant matrices on `C^d ⊗ C^n`, with dimension `dn`. -/
def covariantTable (A B : Fin 2 → ZMod d → Base n) : Table (ZMod d) (ZMod d) :=
  fun x y a b => (Matrix.trace (covariant (A x) a * covariant (B y) b)).re /
    ((d : ℝ) * (n : ℝ))

lemma trace_flatten (X : Blocks d n) :
    Matrix.trace (flatten X) = ∑ k, Matrix.trace (X k k) := by
  simp only [Matrix.trace, Matrix.diag, flatten_apply, Fintype.sum_prod_type]

lemma trace_covariant_mul (P Q : ZMod d → Base n) (a b : ZMod d) :
    Matrix.trace (covariant P a * covariant Q b) =
      ∑ k, Matrix.trace (P (a - k) * Q (b - k)) := by
  rw [covariant, covariant, ← map_mul, trace_flatten]
  simp only [covariantBlocks, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]

lemma covariantTable_eq_average (A B : Fin 2 → ZMod d → Base n) :
    covariantTable A B = averageTable (tracialTable A B) := by
  funext x y a b
  simp only [covariantTable, trace_covariant_mul, Complex.re_sum,
    averageTable, translateTable, tracialTable]
  rw [← Finset.sum_div, div_div, mul_comm (n : ℝ) (d : ℝ)]

lemma residual_sub_same (x y : Fin 2) (a b k : ZMod d) :
    residual d x y (a - k) (b - k) = residual d x y a b := by
  simp only [residual, sub_sub_sub_cancel_right]

lemma context_cost_translate (q : Table (ZMod d) (ZMod d)) (x y : Fin 2) (k : ZMod d) :
    (∑ a, ∑ b, (residual d x y a b : ℝ) * translateTable q k x y a b) =
      ∑ a, ∑ b, (residual d x y a b : ℝ) * q x y a b := by
  unfold translateTable
  calc
    (∑ a, ∑ b, (residual d x y a b : ℝ) * q x y (a - k) (b - k)) =
      ∑ a, ∑ b, (residual d x y (a - k) (b - k) : ℝ) * q x y (a - k) (b - k) := by
        simp only [residual_sub_same]
    _ = ∑ a, ∑ b, (residual d x y a b : ℝ) * q x y a b := by
      refine Fintype.sum_equiv (Equiv.subRight k) _ _ ?_
      intro a
      exact Fintype.sum_equiv (Equiv.subRight k) _ _ (fun _ => rfl)

lemma context_cost_average (q : Table (ZMod d) (ZMod d)) (x y : Fin 2) :
    (∑ a, ∑ b, (residual d x y a b : ℝ) * averageTable q x y a b) =
      ∑ a, ∑ b, (residual d x y a b : ℝ) * q x y a b := by
  have hswap :
      (∑ a, ∑ b, ∑ k, (residual d x y a b : ℝ) * translateTable q k x y a b) =
        ∑ k, ∑ a, ∑ b, (residual d x y a b : ℝ) * translateTable q k x y a b := by
    calc
      _ = ∑ a, ∑ k, ∑ b,
          (residual d x y a b : ℝ) * translateTable q k x y a b := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  simp only [averageTable, ← mul_div_assoc, Finset.mul_sum, ← Finset.sum_div]
  rw [hswap]
  simp only [context_cost_translate, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  field_simp [hd]

lemma cglmpS_average (q : Table (ZMod d) (ZMod d)) :
    cglmpS d (averageTable q) = cglmpS d q := by
  unfold cglmpS
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact context_cost_average q x y

lemma cglmp_average (q : Table (ZMod d) (ZMod d)) :
    cglmp d (averageTable q) = cglmp d q := by
  simp only [cglmp, cglmpS_average]

/-- The outcome-covariant strategy has exactly the original CGLMP value. -/
theorem covariant_cglmp (A B : Fin 2 → ZMod d → Base n) :
    cglmp d (covariantTable A B) = cglmp d (tracialTable A B) := by
  rw [covariantTable_eq_average, cglmp_average]

end
end CGLMPBounds.Companion
