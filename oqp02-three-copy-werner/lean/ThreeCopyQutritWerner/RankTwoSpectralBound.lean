module

public import ThreeCopyQutritWerner.TakagiFamily
public import ThreeCopyQutritWerner.NuclearTrace

@[expose] public section


/-!
# Finite spectral estimates for rank at most two

The scalar estimate is the two-largest-weights bound without choosing an
ordering. The matrix estimate is the exact Hilbert--Schmidt contraction of an
orthogonal compression, obtained from the existing isometry and Cauchy bounds.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- If every one- or two-element weight sum is at most c, a mass of at most two
with each occupancy at most one has weighted sum at most c. -/
theorem rankTwo_weighted_mass_le {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ c)
    (ha2 : ∀ i j, i ≠ j → a i + a j ≤ c)
    (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) (hbs : ∑ i, b i ≤ 2) :
    ∑ i, a i * b i ≤ c := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI := h
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact hc
  | inr h =>
    letI := h
    obtain ⟨p, hp⟩ := Finite.exists_max a
    by_cases hsmall : a p ≤ c / 2
    · calc
        ∑ i, a i * b i ≤ ∑ i, (c / 2) * b i :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right ((hp i).trans hsmall) (hb0 i))
        _ = (c / 2) * ∑ i, b i := by rw [Finset.mul_sum]
        _ ≤ c := by nlinarith [mul_le_mul_of_nonneg_left hbs (by positivity : 0 ≤ c / 2)]
    · have hcpa : 0 ≤ c - a p := sub_nonneg.mpr (ha1 p)
      have hrest : ∑ i ∈ Finset.univ.erase p, a i * b i ≤
          (c - a p) * ∑ i ∈ Finset.univ.erase p, b i := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hip : i ≠ p := (Finset.mem_erase.mp hi).1
        apply mul_le_mul_of_nonneg_right _ (hb0 i)
        linarith [ha2 i p hip]
      have hs : (∑ i ∈ Finset.univ.erase p, b i) + b p = ∑ i, b i :=
        Finset.sum_erase_add _ _ (Finset.mem_univ p)
      have hsa : (∑ i ∈ Finset.univ.erase p, a i * b i) + a p * b p =
          ∑ i, a i * b i := Finset.sum_erase_add _ _ (Finset.mem_univ p)
      have htail : (∑ i ∈ Finset.univ.erase p, b i) ≤ 2 - b p := by linarith
      have htailmul := mul_le_mul_of_nonneg_left htail hcpa
      have hlast := mul_le_mul_of_nonneg_left (hb1 p)
        (show 0 ≤ 2 * a p - c by linarith)
      nlinarith

/-- Orthogonal compression cannot increase the literal Frobenius square. -/
theorem rankTwo_frobSq_compression_le {m n k : Type*}
    [Fintype m] [Fintype n] [Fintype k] [DecidableEq k]
    (U : Matrix m k ℂ) (hU : Uᴴ * U = 1) (A : Matrix m n ℂ) :
    frobSq (Uᴴ * A) ≤ frobSq A := by
  let B := Uᴴ * A
  have ht : ((U * B)ᴴ * A).trace = (frobSq B : ℂ) := by
    rw [ofReal_frobSq_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h := nuclearTrace_pair_normSq_le (U * B) A
  rw [ht, Complex.normSq_ofReal, frobSq_isometry_mul U hU] at h
  have hb := frobSq_nonneg B
  have ha := frobSq_nonneg A
  change frobSq B ≤ frobSq A
  nlinarith

/-- Adjoint preserves the literal Frobenius square, including rectangular matrices. -/
theorem rankTwo_frobSq_conjTranspose {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : frobSq Aᴴ = frobSq A := by
  simp only [frobSq, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

/-- Every column of an actual rectangular isometry has squared norm one. -/
theorem rankTwo_isometry_column_normSq {m k : Type*}
    [Fintype m] [Fintype k] [DecidableEq k]
    (U : Matrix m k ℂ) (hU : Uᴴ * U = 1) (j : k) :
    (∑ i, Complex.normSq (U i j)) = 1 := by
  have h : braket (fun i => U i j) (fun i => U i j) = 1 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, braket] using
      congrFun (congrFun hU j) j
  rw [braket_self] at h
  exact_mod_cast h

/-- An overlap column between two orthonormal families has occupancy at most one. -/
theorem rankTwo_isometry_overlap_column_le {m k r : Type*}
    [Fintype m] [Fintype k] [Fintype r] [DecidableEq k] [DecidableEq r]
    (U : Matrix m k ℂ) (V : Matrix m r ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (j : r) : (∑ i, Complex.normSq ((Uᴴ * V) i j)) ≤ 1 := by
  have h := rankTwo_frobSq_compression_le U hU
    (V.submatrix id (fun _ : Unit => j))
  change frobSq ((Uᴴ * V).submatrix id (fun _ : Unit => j)) ≤
    frobSq (V.submatrix id (fun _ : Unit => j)) at h
  simpa [frobSq, Matrix.submatrix_apply, rankTwo_isometry_column_normSq V hV j] using h

/-- Total overlap occupancy is bounded by the number of compression columns. -/
theorem rankTwo_isometry_overlap_sum_le {m k r : Type*}
    [Fintype m] [Fintype k] [Fintype r] [DecidableEq k] [DecidableEq r]
    (U : Matrix m k ℂ) (V : Matrix m r ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (∑ j, ∑ i, Complex.normSq ((Uᴴ * V) i j)) ≤ (Fintype.card k : ℝ) := by
  have h := rankTwo_frobSq_compression_le V hV U
  have he : Vᴴ * U = (Uᴴ * V)ᴴ := by simp
  rw [he, rankTwo_frobSq_conjTranspose] at h
  have hUnorm : frobSq U = (Fintype.card k : ℝ) := by
    unfold frobSq
    rw [Finset.sum_comm]
    simp [rankTwo_isometry_column_normSq U hU]
  rw [hUnorm] at h
  change (∑ i, ∑ j, Complex.normSq ((Uᴴ * V) i j)) ≤ (Fintype.card k : ℝ) at h
  rw [Finset.sum_comm] at h
  exact h

/-- A real diagonal weight measures each overlap column with its exact squared weight. -/
theorem rankTwo_weighted_overlap_frobSq {k r : Type*}
    [Fintype k] [Fintype r] [DecidableEq r]
    (W : Matrix k r ℂ) (w : r → ℝ) :
    frobSq (W * Matrix.diagonal (fun j => (w j : ℂ))) =
      ∑ j, w j ^ 2 * ∑ i, Complex.normSq (W i j) := by
  simp only [frobSq, Matrix.mul_diagonal, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The two-weight scalar bound controls every actual compression with at most two columns. -/
theorem rankTwo_weighted_frame_le {m k r : Type*}
    [Fintype m] [Fintype k] [Fintype r] [DecidableEq k] [DecidableEq r]
    (U : Matrix m k ℂ) (V : Matrix m r ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (hk : Fintype.card k ≤ 2) (w : r → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h1 : ∀ i, w i ^ 2 ≤ c) (h2 : ∀ i j, i ≠ j → w i ^ 2 + w j ^ 2 ≤ c) :
    frobSq (Uᴴ * V * Matrix.diagonal (fun j => (w j : ℂ))) ≤ c := by
  rw [rankTwo_weighted_overlap_frobSq]
  apply rankTwo_weighted_mass_le (fun j => w j ^ 2)
    (fun j => ∑ i, Complex.normSq ((Uᴴ * V) i j)) c hc (fun j => sq_nonneg _) h1 h2
  · intro j
    exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  · exact rankTwo_isometry_overlap_column_le U V hU hV
  · have hcard : (Fintype.card k : ℝ) ≤ 2 := by exact_mod_cast hk
    exact (rankTwo_isometry_overlap_sum_le U V hU hV).trans hcard

/-- Pairwise Takagi squared-weight bounds control every orthogonal rank-two compression. -/
theorem rankTwo_takagi_compression_le {m k : Type*}
    [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (X : Matrix m m ℂ) (hX : Xᵀ = X)
    (U : Matrix m k ℂ) (hU : Uᴴ * U = 1) (hk : Fintype.card k ≤ 2)
    (c : ℝ) (hc : 0 ≤ c)
    (h1 : ∀ i : TakagiPositiveIndex X hX, takagiWeight X hX i ^ 2 ≤ c)
    (h2 : ∀ i j : TakagiPositiveIndex X hX, i ≠ j →
      takagiWeight X hX i ^ 2 + takagiWeight X hX j ^ 2 ≤ c) :
    frobSq (Uᴴ * X) ≤ c := by
  have he : Uᴴ * X =
      (Uᴴ * takagiFrame X hX * Matrix.diagonal (fun j => (takagiWeight X hX j : ℂ))) *
        (takagiFrame X hX)ᵀ := by
    conv_lhs => rw [takagiFrame_factorization X hX]
    simp only [Matrix.mul_assoc]
  rw [he, ← frobSq_transpose', Matrix.transpose_mul, Matrix.transpose_transpose,
    frobSq_isometry_mul _ (takagiFrame_gram X hX), frobSq_transpose']
  exact rankTwo_weighted_frame_le U (takagiFrame X hX) hU (takagiFrame_gram X hX)
    hk (takagiWeight X hX) c hc h1 h2

/-- Best-rank-two overlap bound derived from actual rank factorization and Takagi weights. -/
theorem rankTwo_takagi_overlap_le {m : Type*} [Fintype m] [DecidableEq m]
    (X : Matrix m m ℂ) (hX : Xᵀ = X) (Y : Matrix m m ℂ) (hY : Y.rank ≤ 2)
    (c : ℝ) (hc : 0 ≤ c)
    (h1 : ∀ i : TakagiPositiveIndex X hX, takagiWeight X hX i ^ 2 ≤ c)
    (h2 : ∀ i j : TakagiPositiveIndex X hX, i ≠ j →
      takagiWeight X hX i ^ 2 + takagiWeight X hX j ^ 2 ≤ c) :
    Complex.normSq (Xᴴ * Y).trace ≤ c * frobSq Y := by
  obtain ⟨d, U, B, hd, hU, hUB⟩ := exists_orthonormal_mul Y
  have hk : Fintype.card (Fin d) ≤ 2 := by simpa [hd] using hY
  have hcomp := rankTwo_takagi_compression_le X hX U hU hk c hc h1 h2
  have hcs := nuclearTrace_pair_normSq_le (Uᴴ * X) B
  have htrace : (Xᴴ * Y).trace = ((Uᴴ * X)ᴴ * B).trace := by
    rw [hUB]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← htrace] at hcs
  have hB : frobSq B = frobSq Y := by rw [hUB, frobSq_isometry_mul U hU]
  exact hcs.trans (by
    rw [← hB]
    exact mul_le_mul_of_nonneg_right hcomp (frobSq_nonneg B))

end ThreeCopyQutritWerner
