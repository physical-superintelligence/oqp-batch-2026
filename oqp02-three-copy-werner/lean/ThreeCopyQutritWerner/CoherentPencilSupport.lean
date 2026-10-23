module

public import ThreeCopyQutritWerner.CoherentPencilMinors
public import ThreeCopyQutritWerner.AppendixCInputs
public import ThreeCopyQutritWerner.RankTwo

@[expose] public section


/-!
# Cubic minors and the actual physical support ranks

Vanishing of every three-column minor of a three-row matrix bounds its rank by
two. The physical local flattenings are then bound to `rank Tr_other(CC†)` by
an exact Gram identity. For `C=X Y†`, a common thin site for the flattenings of
X and Y therefore bounds the source and corange at that same physical site.
The infinite phase-wise minor hypothesis remains explicit.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

/-- The rectangular determinant expansion over all column choices, including repetitions.
Unlike the injective-column Cauchy--Binet formula, this form needs no ordering of columns. -/
theorem det_rectangular_mul_eq_sum {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (A : Matrix m n ℂ) (B : Matrix n m ℂ) :
    (A * B).det = ∑ cols : m → n, (∏ i, B (cols i) i) * (A.submatrix id cols).det := by
  classical
  calc
    (A * B).det = ∑ cols : m → n, ∑ σ : Equiv.Perm m,
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) (cols i) * B (cols i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro cols _
      simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq,
        Finset.mul_sum, Finset.prod_mul_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      ring

/-- All three-column minors vanish only when a three-row matrix has rank at most two. -/
theorem rank_le_two_of_all_three_minors_zero {n : Type*} [Fintype n]
    (A : Matrix (Fin 3) n ℂ)
    (hminor : ∀ cols : Fin 3 → n, (A.submatrix id cols).det = 0) : A.rank ≤ 2 := by
  classical
  have hle : A.rank ≤ 3 := (Matrix.rank_le_card_height A).trans_eq (Fintype.card_fin 3)
  by_contra hn
  have hr : A.rank = Fintype.card (Fin 3) := by simp only [Fintype.card_fin]; omega
  have hsurj := Matrix.mulVec_surjective_iff_rank_eq_card.mpr hr
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hsurj
  have he := det_rectangular_mul_eq_sum A B
  rw [hB, Matrix.det_one] at he
  simp only [hminor, mul_zero, Finset.sum_const_zero] at he
  exact one_ne_zero he

/-- Site-one flattening: the complementary physical coordinates and the source-column
index form a single column index. -/
def coherentFlatten₁ {a b c n : Type*} (X : Matrix (a × b × c) n ℂ) :
    Matrix a ((b × c) × n) ℂ := fun i p => X (i, p.1.1, p.1.2) p.2

/-- Site-two flattening, in the original physical coordinate order. -/
def coherentFlatten₂ {a b c n : Type*} (X : Matrix (a × b × c) n ℂ) :
    Matrix b ((a × c) × n) ℂ := fun i p => X (p.1.1, i, p.1.2) p.2

/-- Site-three flattening, in the original physical coordinate order. -/
def coherentFlatten₃ {a b c n : Type*} (X : Matrix (a × b × c) n ℂ) :
    Matrix c ((a × b) × n) ℂ := fun i p => X (p.1.1, p.1.2, i) p.2

section LocalRanks

variable {a b c m n : Type*} [Fintype a] [Fintype b] [Fintype c]
  [Fintype m] [Fintype n]

theorem coherentFlatten₁_mul_rank_le (X : Matrix (a × b × c) m ℂ) (B : Matrix m n ℂ) :
    (coherentFlatten₁ (X * B)).rank ≤ (coherentFlatten₁ X).rank := by
  classical
  have he : coherentFlatten₁ (X * B) =
      coherentFlatten₁ X * ((1 : Matrix (b × c) (b × c) ℂ) ⊗ₖ B) := by
    ext i ⟨⟨j, k⟩, s⟩
    simp [coherentFlatten₁, Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply,
      Fintype.sum_prod_type, mul_ite, ite_mul, Prod.mk.injEq]
  rw [he]
  exact Matrix.rank_mul_le_left _ _

theorem coherentFlatten₂_mul_rank_le (X : Matrix (a × b × c) m ℂ) (B : Matrix m n ℂ) :
    (coherentFlatten₂ (X * B)).rank ≤ (coherentFlatten₂ X).rank := by
  classical
  have he : coherentFlatten₂ (X * B) =
      coherentFlatten₂ X * ((1 : Matrix (a × c) (a × c) ℂ) ⊗ₖ B) := by
    ext i ⟨⟨j, k⟩, s⟩
    simp [coherentFlatten₂, Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply,
      Fintype.sum_prod_type, mul_ite, ite_mul, Prod.mk.injEq]
  rw [he]
  exact Matrix.rank_mul_le_left _ _

theorem coherentFlatten₃_mul_rank_le (X : Matrix (a × b × c) m ℂ) (B : Matrix m n ℂ) :
    (coherentFlatten₃ (X * B)).rank ≤ (coherentFlatten₃ X).rank := by
  classical
  have he : coherentFlatten₃ (X * B) =
      coherentFlatten₃ X * ((1 : Matrix (a × b) (a × b) ℂ) ⊗ₖ B) := by
    ext i ⟨⟨j, k⟩, s⟩
    simp [coherentFlatten₃, Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply,
      Fintype.sum_prod_type, mul_ite, ite_mul, Prod.mk.injEq]
  rw [he]
  exact Matrix.rank_mul_le_left _ _

/-- The flattening rank is exactly the existing reduced-Gram support dimension. -/
theorem localRangeDim₁_eq_coherentFlatten_rank (C : Matrix (a × b × c) (a × b × c) ℂ) :
    localRangeDim₁ C = (coherentFlatten₁ C).rank := by
  have he : ptrace₂₃ (C * Cᴴ) = coherentFlatten₁ C * (coherentFlatten₁ C)ᴴ := by
    ext i j
    simp only [ptrace₂₃, coherentFlatten₁, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
  rw [localRangeDim₁, he, Matrix.rank_self_mul_conjTranspose]

theorem localRangeDim₂_eq_coherentFlatten_rank (C : Matrix (a × b × c) (a × b × c) ℂ) :
    localRangeDim₂ C = (coherentFlatten₂ C).rank := by
  have he : ptrace₁₃ (C * Cᴴ) = coherentFlatten₂ C * (coherentFlatten₂ C)ᴴ := by
    ext i j
    simp only [ptrace₁₃, coherentFlatten₂, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
  rw [localRangeDim₂, he, Matrix.rank_self_mul_conjTranspose]

theorem localRangeDim₃_eq_coherentFlatten_rank (C : Matrix (a × b × c) (a × b × c) ℂ) :
    localRangeDim₃ C = (coherentFlatten₃ C).rank := by
  have he : ptrace₁₂ (C * Cᴴ) = coherentFlatten₃ C * (coherentFlatten₃ C)ᴴ := by
    ext i j
    simp only [ptrace₁₂, coherentFlatten₃, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
  rw [localRangeDim₃, he, Matrix.rank_self_mul_conjTranspose]

theorem localCorangeDim₁_eq_localRangeDim_adjoint
    (C : Matrix (a × b × c) (a × b × c) ℂ) : localCorangeDim₁ C = localRangeDim₁ Cᴴ := by
  simp only [localCorangeDim₁, localRangeDim₁, Matrix.conjTranspose_conjTranspose]

theorem localCorangeDim₂_eq_localRangeDim_adjoint
    (C : Matrix (a × b × c) (a × b × c) ℂ) : localCorangeDim₂ C = localRangeDim₂ Cᴴ := by
  simp only [localCorangeDim₂, localRangeDim₂, Matrix.conjTranspose_conjTranspose]

theorem localCorangeDim₃_eq_localRangeDim_adjoint
    (C : Matrix (a × b × c) (a × b × c) ℂ) : localCorangeDim₃ C = localRangeDim₃ Cᴴ := by
  simp only [localCorangeDim₃, localRangeDim₃, Matrix.conjTranspose_conjTranspose]

end LocalRanks

/-- Collect the three qutrit source flattenings with a common column-index type. -/
def coherentQutritFlatten (X : Matrix QutritSites (Fin 2) ℂ) :
    Fin 3 → Matrix (Fin 3) ((Fin 3 × Fin 3) × Fin 2) ℂ :=
  ![coherentFlatten₁ X, coherentFlatten₂ X, coherentFlatten₃ X]

theorem coherentQutritFlatten_pencil (X Y : Matrix QutritSites (Fin 2) ℂ)
    (z : ℂ) (i : Fin 3) :
    coherentQutritFlatten (X + z • Y) i =
      coherentQutritFlatten X i + z • coherentQutritFlatten Y i := by
  fin_cases i <;> rfl

/-- A site's source and corange minor conditions imply its actual support-rank bounds. -/
theorem localRangeCorange₁_le_two_of_source_minors
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hX : ∀ cols, ((coherentFlatten₁ X).submatrix id cols).det = 0)
    (hY : ∀ cols, ((coherentFlatten₁ Y).submatrix id cols).det = 0) :
    localRangeDim₁ (X * Yᴴ) ≤ 2 ∧ localCorangeDim₁ (X * Yᴴ) ≤ 2 := by
  have hrX := rank_le_two_of_all_three_minors_zero (coherentFlatten₁ X) hX
  have hrY := rank_le_two_of_all_three_minors_zero (coherentFlatten₁ Y) hY
  constructor
  · rw [localRangeDim₁_eq_coherentFlatten_rank]
    exact (coherentFlatten₁_mul_rank_le X Yᴴ).trans hrX
  · rw [localCorangeDim₁_eq_localRangeDim_adjoint, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, localRangeDim₁_eq_coherentFlatten_rank]
    exact (coherentFlatten₁_mul_rank_le Y Xᴴ).trans hrY

theorem localRangeCorange₂_le_two_of_source_minors
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hX : ∀ cols, ((coherentFlatten₂ X).submatrix id cols).det = 0)
    (hY : ∀ cols, ((coherentFlatten₂ Y).submatrix id cols).det = 0) :
    localRangeDim₂ (X * Yᴴ) ≤ 2 ∧ localCorangeDim₂ (X * Yᴴ) ≤ 2 := by
  have hrX := rank_le_two_of_all_three_minors_zero (coherentFlatten₂ X) hX
  have hrY := rank_le_two_of_all_three_minors_zero (coherentFlatten₂ Y) hY
  constructor
  · rw [localRangeDim₂_eq_coherentFlatten_rank]
    exact (coherentFlatten₂_mul_rank_le X Yᴴ).trans hrX
  · rw [localCorangeDim₂_eq_localRangeDim_adjoint, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, localRangeDim₂_eq_coherentFlatten_rank]
    exact (coherentFlatten₂_mul_rank_le Y Xᴴ).trans hrY

theorem localRangeCorange₃_le_two_of_source_minors
    (X Y : Matrix QutritSites (Fin 2) ℂ)
    (hX : ∀ cols, ((coherentFlatten₃ X).submatrix id cols).det = 0)
    (hY : ∀ cols, ((coherentFlatten₃ Y).submatrix id cols).det = 0) :
    localRangeDim₃ (X * Yᴴ) ≤ 2 ∧ localCorangeDim₃ (X * Yᴴ) ≤ 2 := by
  have hrX := rank_le_two_of_all_three_minors_zero (coherentFlatten₃ X) hX
  have hrY := rank_le_two_of_all_three_minors_zero (coherentFlatten₃ Y) hY
  constructor
  · rw [localRangeDim₃_eq_coherentFlatten_rank]
    exact (coherentFlatten₃_mul_rank_le X Yᴴ).trans hrX
  · rw [localCorangeDim₃_eq_localRangeDim_adjoint, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, localRangeDim₃_eq_coherentFlatten_rank]
    exact (coherentFlatten₃_mul_rank_le Y Xᴴ).trans hrY

/-- The full common-site conclusion from an explicit infinite family of thin pencil minors.
No balanced-factor, scalar-idempotence, or endpoint-energy assumption is smuggled into the
analytic premise; obtaining that premise in QR1--9 is a separate obligation. -/
theorem common_local_support_of_infinite_pencil_minors
    (X Y : Matrix QutritSites (Fin 2) ℂ) (S : Set ℂ) (hS : S.Infinite)
    (hthin : ∀ z ∈ S, ∃ i, ∀ cols : Fin 3 → ((Fin 3 × Fin 3) × Fin 2),
      ((coherentQutritFlatten (X + z • Y) i).submatrix id cols).det = 0) :
    (localRangeDim₁ (X * Yᴴ) ≤ 2 ∧ localCorangeDim₁ (X * Yᴴ) ≤ 2) ∨
      (localRangeDim₂ (X * Yᴴ) ≤ 2 ∧ localCorangeDim₂ (X * Yᴴ) ≤ 2) ∨
        (localRangeDim₃ (X * Yᴴ) ≤ 2 ∧ localCorangeDim₃ (X * Yᴴ) ≤ 2) := by
  obtain ⟨i, hX, hY⟩ := exists_common_site_minor_zero_of_infinite_pencil
    (coherentQutritFlatten X) (coherentQutritFlatten Y) S hS (by
      intro z hz
      obtain ⟨i, hi⟩ := hthin z hz
      refine ⟨i, ?_⟩
      intro cols
      simpa only [coherentQutritFlatten_pencil] using hi cols)
  fin_cases i
  · exact Or.inl (localRangeCorange₁_le_two_of_source_minors X Y hX hY)
  · exact Or.inr (Or.inl (localRangeCorange₂_le_two_of_source_minors X Y hX hY))
  · exact Or.inr (Or.inr (localRangeCorange₃_le_two_of_source_minors X Y hX hY))

end ThreeCopyQutritWerner

end
