module

public import ThreeCopyQutritWerner.HFeature
public import ThreeCopyQutritWerner.ZeroFamilies
public import ThreeCopyQutritWerner.RankOne

@[expose] public section


/-!
# S5.1-H: the zero relations of eq. (24), part 1 (definitions, parity, rank-two inverses)

Manuscript Section 5.1, eq. (24): with `A_i = (I - F_i)/2` acting on two replicas of site `i`
(`F_i` exchanges the site-`i` components of the row and column index, `siteSwap_i`), the known
zero features satisfy `(A_j A_k H(C, p)) ⊗ (A_i p) = 0` for `{i, j, k} = {1, 2, 3}`. This file
states the relations literally (`ZeroRelations`) and proves the certificate-free tools:

* `siteAnti₁_eq_zero_of_symm` (and `₂`, `₃`): Appendix C's parity step. For symmetric `H`, the
  three relations `A_j A_k H = 0` force `A_i H = 0` for every `i` (two of them suffice for each
  `i`: e.g. `A₁ H = A₁ A₃ H + A₁ A₂ H` pointwise, since `F₁ F₂ F₃` fixes a symmetric `H`);
* `exists_left_inverse_of_rank_eq_two`, `exists_right_inverse_of_rank_eq_two`,
  `rank_eq_two_of_mul`: a rank-two `C = X B` has `X` left invertible and `B` right invertible;
* `hFeature_eq_zero_of_sq_of_rank`: for a rank-two `C = X B` with `C² = κ C`, `H(C, p) = 0`
  (Appendix C), hence `ZeroRelations H p` trivially (`zeroRelations_of_hFeature_eq_zero`).

Part 2a (below): the relations for family I at all three placements (`zeroRelations_familyIMat`,
`_site₂`, `_site₃`), via `C² = κ C`; part 2b: family III (`zeroRelations_familyIII`, via
`B₃(U)² = κ B₃(U)`).
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

section Anti

variable {a b c : Type*}

/-- `A₁ = (I - F₁)/2` on two replicas of site 1: `(A₁ M)(r, s) = (M(r, s) - M(F₁(r, s)))/2`. -/
def siteAnti₁ (M : Matrix (a × b × c) (a × b × c) ℂ) : Matrix (a × b × c) (a × b × c) ℂ :=
  Matrix.of fun r s => (M r s - M (siteSwap₁ (r, s)).1 (siteSwap₁ (r, s)).2) / 2

/-- `A₂ = (I - F₂)/2` on two replicas of site 2. -/
def siteAnti₂ (M : Matrix (a × b × c) (a × b × c) ℂ) : Matrix (a × b × c) (a × b × c) ℂ :=
  Matrix.of fun r s => (M r s - M (siteSwap₂ (r, s)).1 (siteSwap₂ (r, s)).2) / 2

/-- `A₃ = (I - F₃)/2` on two replicas of site 3. -/
def siteAnti₃ (M : Matrix (a × b × c) (a × b × c) ℂ) : Matrix (a × b × c) (a × b × c) ℂ :=
  Matrix.of fun r s => (M r s - M (siteSwap₃ (r, s)).1 (siteSwap₃ (r, s)).2) / 2

/-- Eq. (24), literally: `(A_j A_k H) ⊗ (A_i P) = 0` for `{i, j, k} = {1, 2, 3}`. -/
def ZeroRelations (H P : Matrix (a × b × c) (a × b × c) ℂ) : Prop :=
  (∀ r s r' s', siteAnti₂ (siteAnti₃ H) r s * siteAnti₁ P r' s' = 0) ∧
  (∀ r s r' s', siteAnti₁ (siteAnti₃ H) r s * siteAnti₂ P r' s' = 0) ∧
  (∀ r s r' s', siteAnti₁ (siteAnti₂ H) r s * siteAnti₃ P r' s' = 0)

/-- The relations hold as soon as, for each `i`, `A_j A_k H = 0` or `A_i P = 0`. -/
theorem zeroRelations_of_cases {H P : Matrix (a × b × c) (a × b × c) ℂ}
    (h1 : siteAnti₂ (siteAnti₃ H) = 0 ∨ siteAnti₁ P = 0)
    (h2 : siteAnti₁ (siteAnti₃ H) = 0 ∨ siteAnti₂ P = 0)
    (h3 : siteAnti₁ (siteAnti₂ H) = 0 ∨ siteAnti₃ P = 0) : ZeroRelations H P := by
  refine ⟨fun r s r' s' => ?_, fun r s r' s' => ?_, fun r s r' s' => ?_⟩
  · rcases h1 with h | h <;> simp [h]
  · rcases h2 with h | h <;> simp [h]
  · rcases h3 with h | h <;> simp [h]

theorem siteAnti₁_zero : siteAnti₁ (0 : Matrix (a × b × c) (a × b × c) ℂ) = 0 := by
  ext r s
  simp [siteAnti₁]

theorem siteAnti₂_zero : siteAnti₂ (0 : Matrix (a × b × c) (a × b × c) ℂ) = 0 := by
  ext r s
  simp [siteAnti₂]

theorem siteAnti₃_zero : siteAnti₃ (0 : Matrix (a × b × c) (a × b × c) ℂ) = 0 := by
  ext r s
  simp [siteAnti₃]

/-- If `H = 0`, the relations hold for every `P`. -/
theorem zeroRelations_of_hFeature_eq_zero (P : Matrix (a × b × c) (a × b × c) ℂ) :
    ZeroRelations 0 P :=
  zeroRelations_of_cases (Or.inl (by rw [siteAnti₃_zero, siteAnti₂_zero]))
    (Or.inl (by rw [siteAnti₃_zero, siteAnti₁_zero]))
    (Or.inl (by rw [siteAnti₂_zero, siteAnti₁_zero]))

/-- A symmetric matrix takes the same value at `(r, s)` and `(s, r)`. -/
theorem apply_comm_of_transpose_eq {H : Matrix (a × b × c) (a × b × c) ℂ} (hH : Hᵀ = H)
    (x y : a × b × c) : H x y = H y x := by
  have h := congrFun (congrFun hH y) x
  rwa [Matrix.transpose_apply] at h

/-- Appendix C, parity step, site 1: for symmetric `H`, `A₁A₃H = 0` and `A₁A₂H = 0` give
`A₁H = 0`. -/
theorem siteAnti₁_eq_zero_of_symm {H : Matrix (a × b × c) (a × b × c) ℂ} (hH : Hᵀ = H)
    (h13 : siteAnti₁ (siteAnti₃ H) = 0) (h12 : siteAnti₁ (siteAnti₂ H) = 0) :
    siteAnti₁ H = 0 := by
  ext ⟨r₁, r₂, r₃⟩ ⟨s₁, s₂, s₃⟩
  have e3 := congrFun (congrFun h13 (r₁, r₂, r₃)) (s₁, s₂, s₃)
  have e4 := congrFun (congrFun h12 (r₁, r₂, r₃)) (s₁, s₂, s₃)
  simp only [siteAnti₁, siteAnti₂, siteAnti₃, Matrix.of_apply, Matrix.zero_apply, siteSwap₁,
    siteSwap₂, siteSwap₃, Equiv.coe_fn_mk] at e3 e4 ⊢
  rw [apply_comm_of_transpose_eq hH (s₁, r₂, s₃) (r₁, s₂, r₃)] at e3
  rw [apply_comm_of_transpose_eq hH (s₁, s₂, r₃) (r₁, r₂, s₃)] at e4
  linear_combination e3 + e4

/-- Appendix C, parity step, site 2: for symmetric `H`, `A₁A₂H = 0` and `A₂A₃H = 0` give
`A₂H = 0`. -/
theorem siteAnti₂_eq_zero_of_symm {H : Matrix (a × b × c) (a × b × c) ℂ} (hH : Hᵀ = H)
    (h12 : siteAnti₁ (siteAnti₂ H) = 0) (h23 : siteAnti₂ (siteAnti₃ H) = 0) :
    siteAnti₂ H = 0 := by
  ext ⟨r₁, r₂, r₃⟩ ⟨s₁, s₂, s₃⟩
  have e4 := congrFun (congrFun h12 (r₁, r₂, r₃)) (s₁, s₂, s₃)
  have e1 := congrFun (congrFun h23 (r₁, r₂, r₃)) (s₁, s₂, s₃)
  simp only [siteAnti₁, siteAnti₂, siteAnti₃, Matrix.of_apply, Matrix.zero_apply, siteSwap₁,
    siteSwap₂, siteSwap₃, Equiv.coe_fn_mk] at e4 e1 ⊢
  rw [apply_comm_of_transpose_eq hH (s₁, s₂, r₃) (r₁, r₂, s₃)] at e4
  rw [apply_comm_of_transpose_eq hH (r₁, s₂, s₃) (s₁, r₂, r₃)] at e1
  linear_combination e4 + e1

/-- Appendix C, parity step, site 3: for symmetric `H`, `A₁A₃H = 0` and `A₂A₃H = 0` give
`A₃H = 0`. -/
theorem siteAnti₃_eq_zero_of_symm {H : Matrix (a × b × c) (a × b × c) ℂ} (hH : Hᵀ = H)
    (h13 : siteAnti₁ (siteAnti₃ H) = 0) (h23 : siteAnti₂ (siteAnti₃ H) = 0) :
    siteAnti₃ H = 0 := by
  ext ⟨r₁, r₂, r₃⟩ ⟨s₁, s₂, s₃⟩
  have e3 := congrFun (congrFun h13 (r₁, r₂, r₃)) (s₁, s₂, s₃)
  have e1 := congrFun (congrFun h23 (r₁, r₂, r₃)) (s₁, s₂, s₃)
  simp only [siteAnti₁, siteAnti₂, siteAnti₃, Matrix.of_apply, Matrix.zero_apply, siteSwap₁,
    siteSwap₂, siteSwap₃, Equiv.coe_fn_mk] at e3 e1 ⊢
  rw [apply_comm_of_transpose_eq hH (s₁, r₂, s₃) (r₁, s₂, r₃)] at e3
  rw [apply_comm_of_transpose_eq hH (r₁, s₂, s₃) (s₁, r₂, r₃)] at e1
  linear_combination e3 + e1

end Anti

section Inverses

variable {n : Type*} [Fintype n]

/-- A matrix with two rows and rank two has a right inverse. -/
theorem exists_right_inverse_of_rank_eq_two (B : Matrix (Fin 2) n ℂ) (h : B.rank = 2) :
    ∃ R : Matrix n (Fin 2) ℂ, B * R = 1 := by
  rw [← Matrix.mulVec_surjective_iff_exists_right_inverse]
  have htop : LinearMap.range B.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact h
  intro v
  obtain ⟨w, hw⟩ := (LinearMap.range_eq_top.mp htop) v
  exact ⟨w, by rw [← Matrix.mulVecLin_apply]; exact hw⟩

/-- A matrix with two columns and rank two has a left inverse. -/
theorem exists_left_inverse_of_rank_eq_two (X : Matrix n (Fin 2) ℂ) (h : X.rank = 2) :
    ∃ L : Matrix (Fin 2) n ℂ, L * X = 1 := by
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank_eq_two Xᵀ (by rw [Matrix.rank_transpose]; exact h)
  refine ⟨Rᵀ, ?_⟩
  rw [← Matrix.transpose_transpose (Rᵀ * X), Matrix.transpose_mul, Matrix.transpose_transpose, hR,
    Matrix.transpose_one]

/-- `rank (X B) = 2` with `X : n × 2` forces `rank X = rank B = 2`. -/
theorem rank_eq_two_of_mul (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ)
    (h : (X * B).rank = 2) : X.rank = 2 ∧ B.rank = 2 := by
  have hX1 := Matrix.rank_mul_le_left X B
  have hB1 := Matrix.rank_mul_le_right X B
  have hX2 : X.rank ≤ 2 := by simpa using Matrix.rank_le_card_width X
  have hB2 : B.rank ≤ 2 := by simpa using Matrix.rank_le_card_height B
  omega

/-- Appendix C: for a rank-two `C = X B` with `C² = κ C`, `H(C, p) = 0`. -/
theorem hFeature_eq_zero_of_sq_of_rank (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ)
    (hr : (X * B).rank = 2) (κ : ℂ) (h : X * B * (X * B) = κ • (X * B)) :
    hFeature (X * B) (bivecMat X) = 0 := by
  obtain ⟨hX, hB⟩ := rank_eq_two_of_mul X B hr
  obtain ⟨L, hL⟩ := exists_left_inverse_of_rank_eq_two X hX
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank_eq_two B hB
  exact hFeature_eq_zero_of_sq X B L R hL hR κ h

end Inverses

section Families

/-- For a rank-two `C` with `C² = κ C`, every factorization `C = X B` gives the relations of
eq. (24) for `H(C, p)` and `p = bivecMat X` (indeed `H = 0`). -/
theorem zeroRelations_of_sq_of_rank {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (hr : C.rank = 2) (κ : ℂ) (hsq : C * C = κ • C)
    (X : Matrix (a × b × c) (Fin 2) ℂ) (B : Matrix (Fin 2) (a × b × c) ℂ) (hXB : C = X * B) :
    ZeroRelations (hFeature C (bivecMat X)) (bivecMat X) := by
  subst hXB
  rw [hFeature_eq_zero_of_sq_of_rank X B hr κ hsq]
  exact zeroRelations_of_hFeature_eq_zero _

/-- Members of the union of families I–III have rank exactly two. -/
theorem rank_eq_two_of_isQutritZeroFamilyMember
    {C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ}
    (hC : IsQutritZeroFamilyMember C) : C.rank = 2 := by
  obtain ⟨hr, hN, hq, -⟩ := isNormalizedHalfSingularZero_of_isQutritZeroFamilyMember hC
  refine rank_eq_two_of_endpointEnergy_eq_zero C hr hq ?_
  rintro rfl
  simp [invN, frobSq] at hN

/-- `C² = κ C` is preserved by a simultaneous reindexing of rows and columns. -/
theorem submatrix_mul_self_of_mul_self {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (M : Matrix ι ι ℂ) (e : ι' ≃ ι) (κ : ℂ) (h : M * M = κ • M) :
    M.submatrix e e * M.submatrix e e = κ • M.submatrix e e := by
  rw [Matrix.submatrix_mul_equiv, h]
  ext x y
  rfl

/-- Family I (site 1 active) satisfies `C² = κ C` with `κ = ⟨η, χ⟩/√2`. -/
theorem familyIMat_mul_self (f₁ f₂ : Fin 3 → ℂ) (χ η : Fin 3 × Fin 3 → ℂ)
    (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1) (h12 : braket f₁ f₂ = 0) :
    familyIMat f₁ f₂ χ η * familyIMat f₁ f₂ χ η =
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * braket η χ) • familyIMat f₁ f₂ χ η := by
  unfold familyIMat
  simp only [tensor₂_eq_kronecker, Matrix.smul_kronecker, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_kronecker_mul, proj_mul_proj f₁ f₂ h1 h2 h12, ketBra_mul_ketBra,
    Matrix.kronecker_smul, smul_smul]
  congr 1
  ring

/-- Eq. (24) on family I with site 1 active, for every factorization `C = X B`. -/
theorem zeroRelations_familyIMat (f₁ f₂ : Fin 3 → ℂ) (χ η : Fin 3 × Fin 3 → ℂ)
    (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1) (h12 : braket f₁ f₂ = 0)
    (hχ : vecNormSq χ = 1) (hη : vecNormSq η = 1)
    (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (hXB : familyIMat f₁ f₂ χ η = X * B) :
    ZeroRelations (hFeature (familyIMat f₁ f₂ χ η) (bivecMat X)) (bivecMat X) :=
  zeroRelations_of_sq_of_rank _ (rank_eq_two_of_isQutritZeroFamilyMember
    ⟨1, by simp, familyIMat f₁ f₂ χ η, (one_smul ℂ _).symm,
      Or.inl ⟨f₁, f₂, χ, η, h1, h2, h12, hχ, hη, Or.inl rfl⟩⟩) _
    (familyIMat_mul_self f₁ f₂ χ η h1 h2 h12) X B hXB

/-- Eq. (24) on family I with site 2 active. -/
theorem zeroRelations_familyIMat_site₂ (f₁ f₂ : Fin 3 → ℂ) (χ η : Fin 3 × Fin 3 → ℂ)
    (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1) (h12 : braket f₁ f₂ = 0)
    (hχ : vecNormSq χ = 1) (hη : vecNormSq η = 1)
    (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (hXB : (familyIMat f₁ f₂ χ η).submatrix siteEquiv₂.symm siteEquiv₂.symm = X * B) :
    ZeroRelations (hFeature ((familyIMat f₁ f₂ χ η).submatrix siteEquiv₂.symm siteEquiv₂.symm)
      (bivecMat X)) (bivecMat X) :=
  zeroRelations_of_sq_of_rank _ (rank_eq_two_of_isQutritZeroFamilyMember
    ⟨1, by simp, _, (one_smul ℂ _).symm,
      Or.inl ⟨f₁, f₂, χ, η, h1, h2, h12, hχ, hη, Or.inr (Or.inl rfl)⟩⟩) _
    (submatrix_mul_self_of_mul_self _ _ _ (familyIMat_mul_self f₁ f₂ χ η h1 h2 h12)) X B hXB

/-- Eq. (24) on family I with site 3 active. -/
theorem zeroRelations_familyIMat_site₃ (f₁ f₂ : Fin 3 → ℂ) (χ η : Fin 3 × Fin 3 → ℂ)
    (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1) (h12 : braket f₁ f₂ = 0)
    (hχ : vecNormSq χ = 1) (hη : vecNormSq η = 1)
    (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (hXB : (familyIMat f₁ f₂ χ η).submatrix siteEquiv₃.symm siteEquiv₃.symm = X * B) :
    ZeroRelations (hFeature ((familyIMat f₁ f₂ χ η).submatrix siteEquiv₃.symm siteEquiv₃.symm)
      (bivecMat X)) (bivecMat X) :=
  zeroRelations_of_sq_of_rank _ (rank_eq_two_of_isQutritZeroFamilyMember
    ⟨1, by simp, _, (one_smul ℂ _).symm,
      Or.inl ⟨f₁, f₂, χ, η, h1, h2, h12, hχ, hη, Or.inr (Or.inr rfl)⟩⟩) _
    (submatrix_mul_self_of_mul_self _ _ _ (familyIMat_mul_self f₁ f₂ χ η h1 h2 h12)) X B hXB

end Families

section FamilyIII

open scoped Kronecker

/-- `ε² = -1`. -/
theorem epsMat_mul_self : epsMat * epsMat = -1 := by
  have h := epsMat_transpose_mul_transpose
  rw [epsMat_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_neg] at h
  exact h

/-- `J₃ᵀ = -J₃`. -/
theorem epsJ₃_transpose_eq_neg : epsJ₃ᵀ = -epsJ₃ := by
  rw [epsJ₃_transpose, epsMat_transpose]
  ext x y
  simp only [epsJ₃, Matrix.kroneckerMap_apply, Matrix.neg_apply]
  ring

/-- An antisymmetric `2 × 2` matrix is a multiple of `ε`. -/
theorem eq_smul_epsMat_of_transpose_eq_neg (M : Matrix (Fin 2) (Fin 2) ℂ) (h : Mᵀ = -M) :
    M = M 0 1 • epsMat := by
  have e : ∀ i j, M j i = -M i j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa [Matrix.transpose_apply] using this
  have h00 : M 0 0 = 0 := by have := e 0 0; linear_combination this / 2
  have h11 : M 1 1 = 0 := by have := e 1 1; linear_combination this / 2
  have h10 : M 1 0 = -M 0 1 := e 0 1
  ext i j
  fin_cases i <;> fin_cases j
  · simp [epsMat, h00]
  · simp [epsMat]
  · simp [epsMat, h10]
  · simp [epsMat, h11]

/-- `Uᵀ J₃ᵀ U` is antisymmetric. -/
theorem transpose_conj_epsJ₃_transpose (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) :
    (Uᵀ * epsJ₃ᵀ * U)ᵀ = -(Uᵀ * epsJ₃ᵀ * U) := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, epsJ₃_transpose_eq_neg, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
    Matrix.mul_assoc]

/-- `B₃(U)² = κ B₃(U)` with `κ = -(Uᵀ J₃ᵀ U)₀₁/√2`. -/
theorem binaryB₃_mul_self (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) :
    binaryB₃ U * binaryB₃ U =
      (-(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (Uᵀ * epsJ₃ᵀ * U) 0 1) • binaryB₃ U := by
  have hM := eq_smul_epsMat_of_transpose_eq_neg (Uᵀ * epsJ₃ᵀ * U)
    (transpose_conj_epsJ₃_transpose U)
  have hTW : Uᵀ * epsJ₃ᵀ * (U * epsMat) =
      (-(Uᵀ * epsJ₃ᵀ * U) 0 1) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [← Matrix.mul_assoc]
    conv_lhs => rw [hM]
    rw [Matrix.smul_mul, epsMat_mul_self, smul_neg, ← neg_smul]
  have hB : U * epsMat * Uᵀ * epsJ₃ᵀ = U * epsMat * (Uᵀ * epsJ₃ᵀ) := by
    simp only [Matrix.mul_assoc]
  have key : U * epsMat * Uᵀ * epsJ₃ᵀ * (U * epsMat * Uᵀ * epsJ₃ᵀ) =
      (-(Uᵀ * epsJ₃ᵀ * U) 0 1) • (U * epsMat * Uᵀ * epsJ₃ᵀ) := by
    rw [hB, Matrix.mul_assoc, ← Matrix.mul_assoc (Uᵀ * epsJ₃ᵀ), hTW, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul]
  unfold binaryB₃
  rw [epsJ₃_inv, Matrix.smul_mul, Matrix.mul_smul, key]
  simp only [smul_smul]
  congr 1
  ring

/-- `V₁ ⊗ V₂ ⊗ V₃` is an isometry when each `Vᵢ` is. -/
theorem kron_three_isometry (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) (h₁ : V₁ᴴ * V₁ = 1)
    (h₂ : V₂ᴴ * V₂ = 1) (h₃ : V₃ᴴ * V₃ = 1) :
    (V₁ ⊗ₖ (V₂ ⊗ₖ V₃))ᴴ * (V₁ ⊗ₖ (V₂ ⊗ₖ V₃)) = 1 := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, h₁, h₂, h₃, Matrix.one_kronecker_one, Matrix.one_kronecker_one]

/-- Family III satisfies `C² = κ C`. -/
theorem familyIII_mul_self (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) (h₁ : V₁ᴴ * V₁ = 1) (h₂ : V₂ᴴ * V₂ = 1)
    (h₃ : V₃ᴴ * V₃ = 1) :
    familyIII U V₁ V₂ V₃ * familyIII U V₁ V₂ V₃ =
      (-(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (Uᵀ * epsJ₃ᵀ * U) 0 1) • familyIII U V₁ V₂ V₃ := by
  unfold familyIII
  rw [conj_mul_conj _ (kron_three_isometry V₁ V₂ V₃ h₁ h₂ h₃), binaryB₃_mul_self, Matrix.mul_smul,
    Matrix.smul_mul]

/-- Eq. (24) on family III, for every factorization `C = X B`. -/
theorem zeroRelations_familyIII (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (h₁ : V₁ᴴ * V₁ = 1)
    (h₂ : V₂ᴴ * V₂ = 1) (h₃ : V₃ᴴ * V₃ = 1)
    (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (hXB : familyIII U V₁ V₂ V₃ = X * B) :
    ZeroRelations (hFeature (familyIII U V₁ V₂ V₃) (bivecMat X)) (bivecMat X) :=
  zeroRelations_of_sq_of_rank _ (rank_eq_two_of_isQutritZeroFamilyMember
    ⟨1, by simp, _, (one_smul ℂ _).symm,
      Or.inr (Or.inr ⟨U, V₁, V₂, V₃, hU, h₁, h₂, h₃, rfl⟩)⟩) _
    (familyIII_mul_self U V₁ V₂ V₃ h₁ h₂ h₃) X B hXB

end FamilyIII

end ThreeCopyQutritWerner

end
