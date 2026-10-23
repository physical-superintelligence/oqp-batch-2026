module

public import ThreeCopyQutritWerner.RankTwoSpectralBound

@[expose] public section


/-!
# Equality support for the rank-two spectral mass estimate

At saturation of a uniform largest squared weight, every strictly smaller
weight has zero occupancy. The matrix version applies this to the actual
overlap of two orthonormal families, without supplying a support conclusion.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Saturated mass at a uniform upper weight cannot occupy a strictly
smaller weight. Neither strict separation among maximal weights nor an
ordering or nonempty index set is required. -/
theorem rankTwo_weighted_mass_eq_submax_zero
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (ha : ∀ i, a i ≤ S) (hb : ∀ i, 0 ≤ b i)
    (hbs : ∑ i, b i ≤ 2) (heq : ∑ i, a i * b i = 2 * S)
    (j : ι) (hj : a j < S) : b j = 0 := by
  have hg : ∀ i, 0 ≤ (S - a i) * b i :=
    fun i => mul_nonneg (sub_nonneg.mpr (ha i)) (hb i)
  have hsum : ∑ i, (S - a i) * b i = S * (∑ i, b i) - 2 * S := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, heq]
  have hsum_le : (∑ i, (S - a i) * b i) ≤ 0 := by
    rw [hsum]
    have h := mul_le_mul_of_nonneg_left hbs hS
    linarith
  have hz : (∑ i, (S - a i) * b i) = 0 :=
    le_antisymm hsum_le (Finset.sum_nonneg fun i _ => hg i)
  have hjz : (S - a j) * b j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hg i)).mp hz j (Finset.mem_univ j)
  exact (mul_eq_zero.mp hjz).resolve_left (sub_pos.mpr hj).ne'

/-- At saturated rank-two compression, every overlap entry with a strictly
submaximal actual spectral vector vanishes. Maximal degeneracies are retained. -/
theorem rankTwo_weighted_frame_eq_submax_zero
    {m k r : Type*} [Fintype m] [Fintype k] [Fintype r]
    [DecidableEq k] [DecidableEq r]
    (U : Matrix m k ℂ) (V : Matrix m r ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (hk : Fintype.card k ≤ 2) (w : r → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hw : ∀ j, w j ^ 2 ≤ S)
    (heq : frobSq (Uᴴ * V * Matrix.diagonal (fun j => (w j : ℂ))) = 2 * S)
    (j : r) (hj : w j ^ 2 < S) (i : k) : (Uᴴ * V) i j = 0 := by
  let b : r → ℝ := fun j => ∑ i, Complex.normSq ((Uᴴ * V) i j)
  have hb : ∀ j, 0 ≤ b j := fun j =>
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hbs : ∑ j, b j ≤ 2 := by
    have hcard : (Fintype.card k : ℝ) ≤ 2 := by exact_mod_cast hk
    exact (rankTwo_isometry_overlap_sum_le U V hU hV).trans hcard
  have he : ∑ j, w j ^ 2 * b j = 2 * S := by
    simpa only [rankTwo_weighted_overlap_frobSq, b] using heq
  have hjz := rankTwo_weighted_mass_eq_submax_zero (fun j => w j ^ 2) b S hS hw hb
    hbs he j hj
  have hi : Complex.normSq ((Uᴴ * V) i j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg ((Uᴴ * V) a j))).mp
      hjz i (Finset.mem_univ i)
  exact Complex.normSq_eq_zero.mp hi

end ThreeCopyQutritWerner
