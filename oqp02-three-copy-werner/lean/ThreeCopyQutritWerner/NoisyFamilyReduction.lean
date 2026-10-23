module

public import ThreeCopyQutritWerner.NoisyFamily
public import ThreeCopyQutritWerner.TwoCutMain
public import ThreeCopyQutritWerner.Overlap
public import ThreeCopyQutritWerner.Physical
public import ThreeCopyQutritWerner.RankBridge
public import ThreeCopyQutritWerner.Distillation
public import ThreeCopyQutritWerner.WernerState

@[expose] public section


/-!
# S6-d3: three-copy nondistillability of the qutrit-seed family from T2.1a

Manuscript Corollary 6.2: the family of eq. (27), written here `τ_{d,p} = p σ_d + (1 - p) I/d²`
with `σ_d = (J ⊗ J) ρ_{3,1/2} (J ⊗ J)†` (`noisyFamily J p`), is three-copy nondistillable. The
manuscript's argument expands the tensor cube and resolves the white noise into product projectors.
This file writes the white noise
as local conjugations
of the seed itself, `I_{d²} = 15 Σ_{a,b} (K_a ⊗ K_b) ρ_{3,1/2} (K_a ⊗ K_b)†` with `K_a = e_a e₀ᵀ`
(`sum_conj_basisCol`; `ρ_{3,1/2}((0,0),(0,0)) = 1/15`), so that `τ_{d,p}` is a nonnegative
combination of local conjugations of `ρ_{3,1/2}` (`noisyFamily_eq_sum_conj`). A certificate-free
monotonicity lemma then applies: three-copy rank-two non-detectability survives nonnegative
mixtures of local conjugations (`not_isThreeCopyRankTwoDetectable_sum_conj`).

The result is the implication from T2.1a (`QutritEndpointInequality`) to the nondistillability part
of claim S6-d3. It holds for every `J` and every `0 ≤ p ≤ 1`; the isometry and the threshold
`15/(d² + 15) < p` enter the NPT part (`noisyFamily_isNPT`), and `p < 1` full rank.
-/

noncomputable section

open scoped Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

section LocalMaps

variable {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']

/-- `((A ⊗ B) X (A ⊗ B)†)^Γ = (A ⊗ B̄) X^Γ (A ⊗ B̄)†` for arbitrary local maps `A`, `B`. -/
theorem partialTranspose_conj_kron_gen (A : Matrix m' m ℂ) (B : Matrix n' n ℂ)
    (X : Matrix (m × n) (m × n) ℂ) :
    partialTranspose ((A ⊗ₖ B) * X * (A ⊗ₖ B)ᴴ) =
      (A ⊗ₖ B.map star) * partialTranspose X * (A ⊗ₖ B.map star)ᴴ := by
  ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
  simp only [partialTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.map_apply, Fintype.sum_prod_type, Finset.sum_mul,
    star_mul', star_star]
  refine Finset.sum_congr rfl fun t₁ _ => ?_
  exact (sum_reverse_three _).trans (Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

/-- `(P ⊗ Q̄)† vec C = vec (P† C Q)`. -/
theorem conjTranspose_kron_mulVec_vec_gen (P : Matrix m' m ℂ) (Q : Matrix n' n ℂ)
    (C : Matrix m' n' ℂ) :
    (P ⊗ₖ Q.map star)ᴴ *ᵥ vec C = vec (Pᴴ * C * Q) := by
  funext p
  obtain ⟨r, s⟩ := p
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.map_apply, star_mul', star_star, vec, Matrix.mul_apply, Fintype.sum_prod_type,
    Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring)

/-- `⟨vec C, ((A ⊗ B) X (A ⊗ B)†)^Γ vec C⟩ = ⟨vec (A† C B), X^Γ vec (A† C B)⟩`. -/
theorem expectation_partialTranspose_conj_kron_gen (A : Matrix m' m ℂ) (B : Matrix n' n ℂ)
    (X : Matrix (m × n) (m × n) ℂ) (C : Matrix m' n' ℂ) :
    expectation (partialTranspose ((A ⊗ₖ B) * X * (A ⊗ₖ B)ᴴ)) (vec C) =
      expectation (partialTranspose X) (vec (Aᴴ * C * B)) := by
  rw [partialTranspose_conj_kron_gen, ← conjTranspose_kron_mulVec_vec_gen,
    expectation_mulVec_conj, Matrix.conjTranspose_conjTranspose]

end LocalMaps

section Copies

variable {m n : Type*}

/-- `M₁ ⊗ M₂ ⊗ M₃` regrouped along `A₁A₂A₃ | B₁B₂B₃` (`tripleCopy M = tripleProd M M M`). -/
def tripleProd (M₁ M₂ M₃ : Matrix (m × n) (m × n) ℂ) :
    Matrix ((m × m × m) × (n × n × n)) ((m × m × m) × (n × n × n)) ℂ :=
  fun x y =>
    M₁ (x.1.1, x.2.1) (y.1.1, y.2.1) * M₂ (x.1.2.1, x.2.2.1) (y.1.2.1, y.2.2.1) *
      M₃ (x.1.2.2, x.2.2.2) (y.1.2.2, y.2.2.2)

theorem tripleProd_self (M : Matrix (m × n) (m × n) ℂ) : tripleProd M M M = tripleCopy M := rfl

/-- Three copies of a finite sum. -/
theorem tripleCopy_sum {κ : Type*} [Fintype κ] (M : κ → Matrix (m × n) (m × n) ℂ) :
    tripleCopy (∑ k, M k) = ∑ k₁, ∑ k₂, ∑ k₃, tripleProd (M k₁) (M k₂) (M k₃) := by
  ext x y
  simp only [tripleCopy, tripleProd, Matrix.sum_apply]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k₁ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k₂ _ => ?_
  rw [Finset.mul_sum]

theorem tripleProd_smul (a b c : ℂ) (M₁ M₂ M₃ : Matrix (m × n) (m × n) ℂ) :
    tripleProd (a • M₁) (b • M₂) (c • M₃) = (a * b * c) • tripleProd M₁ M₂ M₃ := by
  ext x y
  simp only [tripleProd, Matrix.smul_apply, smul_eq_mul]
  ring

theorem tripleProd_eq_submatrix_kronecker (M₁ M₂ M₃ : Matrix (m × n) (m × n) ℂ) :
    tripleProd M₁ M₂ M₃ = (M₁ ⊗ₖ (M₂ ⊗ₖ M₃)).submatrix (copyEquiv m n) (copyEquiv m n) := by
  ext x y
  simp only [tripleProd, Matrix.submatrix_apply, copyEquiv, Equiv.coe_fn_mk,
    Matrix.kroneckerMap_apply]
  ring

/-- Regrouping `(A₁ ⊗ B₁) ⊗ (A₂ ⊗ B₂) ⊗ (A₃ ⊗ B₃)` as `(A₁ ⊗ A₂ ⊗ A₃) ⊗ (B₁ ⊗ B₂ ⊗ B₃)`. -/
theorem kron_three_submatrix {m' n' : Type*} (A₁ A₂ A₃ : Matrix m' m ℂ)
    (B₁ B₂ B₃ : Matrix n' n ℂ) :
    ((A₁ ⊗ₖ B₁) ⊗ₖ ((A₂ ⊗ₖ B₂) ⊗ₖ (A₃ ⊗ₖ B₃))).submatrix (copyEquiv m' n') (copyEquiv m n) =
      (A₁ ⊗ₖ (A₂ ⊗ₖ A₃)) ⊗ₖ (B₁ ⊗ₖ (B₂ ⊗ₖ B₃)) := by
  ext x y
  simp only [Matrix.submatrix_apply, copyEquiv, Equiv.coe_fn_mk, Matrix.kroneckerMap_apply]
  ring

/-- Three locally conjugated factors are one local conjugation of their regrouped product. -/
theorem tripleProd_conj {m' n' : Type*} [Fintype m] [Fintype n] (A₁ A₂ A₃ : Matrix m' m ℂ)
    (B₁ B₂ B₃ : Matrix n' n ℂ) (X₁ X₂ X₃ : Matrix (m × n) (m × n) ℂ) :
    tripleProd ((A₁ ⊗ₖ B₁) * X₁ * (A₁ ⊗ₖ B₁)ᴴ) ((A₂ ⊗ₖ B₂) * X₂ * (A₂ ⊗ₖ B₂)ᴴ)
        ((A₃ ⊗ₖ B₃) * X₃ * (A₃ ⊗ₖ B₃)ᴴ) =
      ((A₁ ⊗ₖ (A₂ ⊗ₖ A₃)) ⊗ₖ (B₁ ⊗ₖ (B₂ ⊗ₖ B₃))) * tripleProd X₁ X₂ X₃ *
        ((A₁ ⊗ₖ (A₂ ⊗ₖ A₃)) ⊗ₖ (B₁ ⊗ₖ (B₂ ⊗ₖ B₃)))ᴴ := by
  calc tripleProd ((A₁ ⊗ₖ B₁) * X₁ * (A₁ ⊗ₖ B₁)ᴴ) ((A₂ ⊗ₖ B₂) * X₂ * (A₂ ⊗ₖ B₂)ᴴ)
          ((A₃ ⊗ₖ B₃) * X₃ * (A₃ ⊗ₖ B₃)ᴴ)
        = (((A₁ ⊗ₖ B₁) ⊗ₖ ((A₂ ⊗ₖ B₂) ⊗ₖ (A₃ ⊗ₖ B₃))) * (X₁ ⊗ₖ (X₂ ⊗ₖ X₃)) *
            ((A₁ ⊗ₖ B₁) ⊗ₖ ((A₂ ⊗ₖ B₂) ⊗ₖ (A₃ ⊗ₖ B₃)))ᴴ).submatrix (copyEquiv m' n')
              (copyEquiv m' n') := by
          rw [tripleProd_eq_submatrix_kronecker]
          congr 1
          simp only [Matrix.mul_kronecker_mul, Matrix.conjTranspose_kronecker]
      _ = ((A₁ ⊗ₖ B₁) ⊗ₖ ((A₂ ⊗ₖ B₂) ⊗ₖ (A₃ ⊗ₖ B₃))).submatrix (copyEquiv m' n')
              (copyEquiv m n) *
            (X₁ ⊗ₖ (X₂ ⊗ₖ X₃)).submatrix (copyEquiv m n) (copyEquiv m n) *
            ((A₁ ⊗ₖ B₁) ⊗ₖ ((A₂ ⊗ₖ B₂) ⊗ₖ (A₃ ⊗ₖ B₃)))ᴴ.submatrix (copyEquiv m n)
              (copyEquiv m' n') := by
          rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
      _ = ((A₁ ⊗ₖ (A₂ ⊗ₖ A₃)) ⊗ₖ (B₁ ⊗ₖ (B₂ ⊗ₖ B₃))) * tripleProd X₁ X₂ X₃ *
            ((A₁ ⊗ₖ (A₂ ⊗ₖ A₃)) ⊗ₖ (B₁ ⊗ₖ (B₂ ⊗ₖ B₃)))ᴴ := by
          rw [← Matrix.conjTranspose_submatrix, kron_three_submatrix,
            ← tripleProd_eq_submatrix_kronecker]

end Copies

/-- Monotonicity (certificate-free): three-copy rank-two non-detectability survives nonnegative
mixtures of local conjugations. -/
theorem not_isThreeCopyRankTwoDetectable_sum_conj {m n m' n' κ : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n'] [Fintype κ] {ρ : Matrix (m × n) (m × n) ℂ}
    (hρ : ¬ IsThreeCopyRankTwoDetectable ρ) (μ : κ → ℝ) (hμ : ∀ k, 0 ≤ μ k)
    (A : κ → Matrix m' m ℂ) (B : κ → Matrix n' n ℂ) :
    ¬ IsThreeCopyRankTwoDetectable
      (∑ k, ((μ k : ℝ) : ℂ) • ((A k ⊗ₖ B k) * ρ * (A k ⊗ₖ B k)ᴴ)) := by
  rintro ⟨ψ, hψ, hneg⟩
  obtain ⟨C, rfl⟩ : ∃ C : Matrix (m' × m' × m') (n' × n' × n') ℂ, ψ = vec C :=
    ⟨_, eq_vec_of ψ⟩
  have hC : C.rank ≤ 2 := (schmidtRankLE_vec_iff C 2).mp hψ
  have hterm : ∀ k₁ k₂ k₃ : κ, 0 ≤ (expectation (partialTranspose
      (tripleProd ((A k₁ ⊗ₖ B k₁) * ρ * (A k₁ ⊗ₖ B k₁)ᴴ) ((A k₂ ⊗ₖ B k₂) * ρ * (A k₂ ⊗ₖ B k₂)ᴴ)
        ((A k₃ ⊗ₖ B k₃) * ρ * (A k₃ ⊗ₖ B k₃)ᴴ))) (vec C)).re := by
    intro k₁ k₂ k₃
    rw [tripleProd_conj, tripleProd_self, expectation_partialTranspose_conj_kron_gen]
    by_contra hlt
    apply hρ
    unfold IsThreeCopyRankTwoDetectable
    refine ⟨_, ?_, not_le.mp hlt⟩
    exact (schmidtRankLE_vec_iff _ 2).mpr
      (((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hC)
  simp only [tripleCopy_sum, tripleProd_smul, partialTranspose_sum, partialTranspose_smul',
    expectation_sum, expectation_smul', Complex.re_sum] at hneg
  refine absurd hneg (not_lt.mpr (Finset.sum_nonneg fun k₁ _ => Finset.sum_nonneg fun k₂ _ =>
    Finset.sum_nonneg fun k₃ _ => ?_))
  rw [show ((μ k₁ : ℂ) * (μ k₂ : ℂ) * (μ k₃ : ℂ)) = ((μ k₁ * μ k₂ * μ k₃ : ℝ) : ℂ) by
    push_cast; ring, Complex.re_ofReal_mul]
  exact mul_nonneg (mul_nonneg (mul_nonneg (hμ k₁) (hμ k₂)) (hμ k₃)) (hterm k₁ k₂ k₃)

section Noise

variable {d : ℕ}

/-- `K_a = e_a e₀ᵀ : ℂ³ → ℂᵈ`. -/
def basisCol (a : Fin d) : Matrix (Fin d) (Fin 3) ℂ :=
  Matrix.of fun i s => if i = a ∧ s = 0 then 1 else 0

set_option maxHeartbeats 2000000 in
/-- `(K_a ⊗ K_b) M (K_a ⊗ K_b)† = M((0,0),(0,0)) |ab⟩⟨ab|`. -/
theorem conj_basisCol (a b : Fin d) (M : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    (basisCol a ⊗ₖ basisCol b) * M * (basisCol a ⊗ₖ basisCol b)ᴴ =
      Matrix.of fun x y => if x = (a, b) ∧ y = (a, b) then M (0, 0) (0, 0) else 0 := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, basisCol,
    Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_three, Prod.mk.injEq]
  by_cases hi : i = a <;> by_cases hj : j = b <;> by_cases hi' : i' = a <;>
    by_cases hj' : j' = b <;> simp [hi, hj, hi', hj']

/-- `Σ_{a,b} (K_a ⊗ K_b) M (K_a ⊗ K_b)† = M((0,0),(0,0)) I`. -/
theorem sum_conj_basisCol (M : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    ∑ ab : Fin d × Fin d,
        (basisCol ab.1 ⊗ₖ basisCol ab.2) * M * (basisCol ab.1 ⊗ₖ basisCol ab.2)ᴴ =
      M (0, 0) (0, 0) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
  ext x y
  rw [Matrix.sum_apply]
  simp only [conj_basisCol, Matrix.of_apply, Prod.mk.eta, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases h : x = y
  · subst h
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  · simp only [if_neg h, mul_zero]
    exact Finset.sum_eq_zero fun ab _ => if_neg fun hab => h (hab.1.trans hab.2.symm)

theorem werner_three_half_zero_zero :
    werner 3 (1 / 2) ((0 : Fin 3), (0 : Fin 3)) ((0 : Fin 3), (0 : Fin 3)) = 1 / 15 := by
  rw [werner_apply_prod]
  push_cast
  norm_num

/-- Weights of the decomposition of `τ_{d,p}` into local conjugations of `ρ_{3,1/2}`. -/
def noiseWeight (d : ℕ) (p : ℝ) : Option (Fin d × Fin d) → ℝ
  | none => p
  | some _ => 15 * (1 - p) / (d : ℝ) ^ 2

/-- Left local maps of the decomposition: `J`, then `K_a`. -/
def noiseL (J : Matrix (Fin d) (Fin 3) ℂ) : Option (Fin d × Fin d) → Matrix (Fin d) (Fin 3) ℂ
  | none => J
  | some ab => basisCol ab.1

/-- Right local maps of the decomposition: `J`, then `K_b`. -/
def noiseR (J : Matrix (Fin d) (Fin 3) ℂ) : Option (Fin d × Fin d) → Matrix (Fin d) (Fin 3) ℂ
  | none => J
  | some ab => basisCol ab.2

/-- `τ_{d,p} = p (J ⊗ J) ρ (J ⊗ J)† + Σ_{a,b} 15 (1 - p)/d² (K_a ⊗ K_b) ρ (K_a ⊗ K_b)†`. -/
theorem noisyFamily_eq_sum_conj (J : Matrix (Fin d) (Fin 3) ℂ) (p : ℝ) :
    noisyFamily J p = ∑ k : Option (Fin d × Fin d), ((noiseWeight d p k : ℝ) : ℂ) •
      ((noiseL J k ⊗ₖ noiseR J k) * werner 3 (1 / 2) * (noiseL J k ⊗ₖ noiseR J k)ᴴ) := by
  rw [Fintype.sum_option]
  simp only [noiseWeight, noiseL, noiseR]
  rw [← Finset.smul_sum, sum_conj_basisCol, smul_smul, werner_three_half_zero_zero]
  unfold noisyFamily embedPair
  congr 2
  push_cast
  ring

/-- REDUCTION (not claim S6-d3): T2.1a implies that `τ_{d,p}` is three-copy nondistillable, for
every `J` and every `0 ≤ p ≤ 1`. -/
theorem not_isThreeCopyFilterDistillable_noisyFamily_of_endpoint
    (hq : QutritEndpointInequality) (J : Matrix (Fin d) (Fin 3) ℂ) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : ¬ IsThreeCopyFilterDistillable (noisyFamily J p) := by
  rw [isThreeCopyFilterDistillable_iff _ (noisyFamily_posSemidef J hp0 hp1).isHermitian,
    noisyFamily_eq_sum_conj]
  refine not_isThreeCopyRankTwoDetectable_sum_conj
    (not_isThreeCopyRankTwoDetectable_werner_three_of_endpoint (by norm_num) (by norm_num) hq)
    (noiseWeight d p) (fun k => ?_) (noiseL J) (noiseR J)
  cases k with
  | none => exact hp0
  | some _ =>
    show 0 ≤ 15 * (1 - p) / (d : ℝ) ^ 2
    exact div_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)

end Noise

/-- REDUCTION (not claim S6-d3): T2.1a implies the open proposition
`NoisyFamilyThreeCopyNondistillable d` for every `d`. -/
theorem noisyFamilyThreeCopyNondistillable_of_endpoint (hq : QutritEndpointInequality) (d : ℕ) :
    NoisyFamilyThreeCopyNondistillable d := by
  unfold NoisyFamilyThreeCopyNondistillable
  intro J _ p hp hp1
  exact not_isThreeCopyFilterDistillable_noisyFamily_of_endpoint hq J
    (le_trans (by positivity) hp.le) hp1.le

end ThreeCopyQutritWerner

end
