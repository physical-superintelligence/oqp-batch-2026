module

public import ThreeCopyQutritWerner.Corollaries
public import ThreeCopyQutritWerner.PPTRegion

@[expose] public section


/-!
# The full-rank family with the qutrit seed (manuscript Section 6.2, claim S6-d3)

Manuscript eq. (27) and Corollary 6.2: the full-rank family built from the qutrit seed, written
here `σ_d = (J ⊗ J) ρ_{3,1/2} (J ⊗ J)†` for `J : ℂ³ → ℂ^d` and `τ_{d,p} = p σ_d + (1 - p) I/d²`
(`noisyFamily J p`): for `15/(d² + 15) < p < 1`, `τ_{d,p}` is full rank, NPT, and nondistillable
through three copies. (`Jᴴ J = 1` forces `d ≥ 3`.)

Proved here:
* `noisyFamily_posDef`: `τ_{d,p}` is positive definite (full rank) for `0 ≤ p < 1`;
* `noisyFamily_isNPT`: `τ_{d,p}` is NPT for `15/(d² + 15) < p ≤ 1`, witnessed by
  `ψ = vec (J J†)` with `⟨ψ, τ^Γ ψ⟩ = -p/5 + 3(1 - p)/d²` (`noisyFamily_expectation`), through the
  identity `⟨vec C, ((J ⊗ J) ρ (J ⊗ J)†)^Γ vec C⟩ = ⟨vec (J† C J), ρ^Γ vec (J† C J)⟩`
  (`expectation_partialTranspose_conj_kron`).

Stated as a proposition (`NoisyFamilyThreeCopyNondistillable`): three-copy nondistillability,
which the manuscript derives from the qutrit endpoint T2.1a; `NoisyFamilyReduction` proves it from
T2.1a (`noisyFamilyThreeCopyNondistillable_of_endpoint`).
-/

noncomputable section

open scoped Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

variable {d : ℕ}

/-- Claim S6-d3, nondistillability part (statement): three copies of `τ_{d,p}` are not distillable
for `15/(d² + 15) < p < 1`. It follows from T2.1a (`noisyFamilyThreeCopyNondistillable_of_endpoint`). -/
def NoisyFamilyThreeCopyNondistillable (d : ℕ) : Prop :=
  ∀ (J : Matrix (Fin d) (Fin 3) ℂ), Jᴴ * J = 1 → ∀ p : ℝ, 15 / ((d : ℝ) ^ 2 + 15) < p → p < 1 →
    ¬ IsThreeCopyFilterDistillable (noisyFamily J p)

/-! ### Positivity -/

theorem embedPair_posSemidef (J : Matrix (Fin d) (Fin 3) ℂ) :
    (embedPair J (werner 3 (1 / 2))).PosSemidef :=
  (werner_posSemidef 3 (1 / 2) (by norm_num) (by norm_num)).mul_mul_conjTranspose_same (J ⊗ₖ J)

/-- `τ_{d,p}` is positive semidefinite for `0 ≤ p ≤ 1`. -/
theorem noisyFamily_posSemidef (J : Matrix (Fin d) (Fin 3) ℂ) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : (noisyFamily J p).PosSemidef := by
  have hσ := (embedPair_posSemidef J).smul (Complex.zero_le_real.mpr hp0)
  have hc : (0 : ℂ) ≤ (((1 - p) / (d : ℝ) ^ 2 : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (div_nonneg (by linarith) (by positivity))
  exact hσ.add (Matrix.PosSemidef.one.smul hc)

/-- Manuscript Corollary 6.2: `noisyFamily J p` is full rank (positive definite) for `0 ≤ p < 1`. -/
theorem noisyFamily_posDef (J : Matrix (Fin d) (Fin 3) ℂ) (hd : 0 < d) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p < 1) : (noisyFamily J p).PosDef := by
  have hσ := (embedPair_posSemidef J).smul (Complex.zero_le_real.mpr hp0)
  have hc : (0 : ℂ) < (((1 - p) / (d : ℝ) ^ 2 : ℝ) : ℂ) :=
    Complex.zero_lt_real.mpr (div_pos (by linarith) (pow_pos (Nat.cast_pos.mpr hd) 2))
  have hI := (Matrix.PosDef.one (n := Fin d × Fin d) (R := ℂ)).smul hc
  unfold noisyFamily
  rw [add_comm]
  exact hI.add_posSemidef hσ

/-! ### The partial transpose of the embedded state -/

theorem sum_reverse_three {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M] (f : α → β → γ → M) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c :=
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, f a b c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, f a b c := Finset.sum_comm

/-- `((J ⊗ J) ρ (J ⊗ J)†)^Γ = (J ⊗ J̄) ρ^Γ (J ⊗ J̄)†`. -/
theorem partialTranspose_conj_kron (J : Matrix (Fin d) (Fin 3) ℂ)
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    partialTranspose ((J ⊗ₖ J) * ρ * (J ⊗ₖ J)ᴴ) =
      (J ⊗ₖ J.map star) * partialTranspose ρ * (J ⊗ₖ J.map star)ᴴ := by
  ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
  simp only [partialTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.map_apply, Fintype.sum_prod_type, Finset.sum_mul,
    star_mul', star_star]
  refine Finset.sum_congr rfl fun t₁ _ => ?_
  exact (sum_reverse_three _).trans (Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

/-- `⟨M (W v), ·⟩`: `expectation M (W v) = expectation (W† M W) v`. -/
theorem expectation_mulVec_conj {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι ι ℂ)
    (W : Matrix ι κ ℂ) (v : κ → ℂ) :
    expectation M (W *ᵥ v) = expectation (Wᴴ * M * W) v := by
  rw [expectation_eq_dotProduct, expectation_eq_dotProduct, Matrix.star_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- `(J ⊗ J̄)† vec C = vec (J† C J)`. -/
theorem conjTranspose_kron_mulVec_vec (J : Matrix (Fin d) (Fin 3) ℂ)
    (C : Matrix (Fin d) (Fin d) ℂ) :
    (J ⊗ₖ J.map star)ᴴ *ᵥ vec C = vec (Jᴴ * C * J) := by
  funext p
  obtain ⟨r, s⟩ := p
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.map_apply, star_mul', star_star, vec, Matrix.mul_apply, Fintype.sum_prod_type,
    Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring)

/-- `⟨vec C, ((J ⊗ J) ρ (J ⊗ J)†)^Γ vec C⟩ = ⟨vec (J† C J), ρ^Γ vec (J† C J)⟩`. -/
theorem expectation_partialTranspose_conj_kron (J : Matrix (Fin d) (Fin 3) ℂ)
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (C : Matrix (Fin d) (Fin d) ℂ) :
    expectation (partialTranspose ((J ⊗ₖ J) * ρ * (J ⊗ₖ J)ᴴ)) (vec C) =
      expectation (partialTranspose ρ) (vec (Jᴴ * C * J)) := by
  rw [partialTranspose_conj_kron, ← conjTranspose_kron_mulVec_vec, expectation_mulVec_conj,
    Matrix.conjTranspose_conjTranspose]

/-! ### The NPT witness -/

theorem partialTranspose_add' {m n : Type*} (A B : Matrix (m × n) (m × n) ℂ) :
    partialTranspose (A + B) = partialTranspose A + partialTranspose B := by
  ext x y
  rfl

theorem partialTranspose_smul' {m n : Type*} (z : ℂ) (A : Matrix (m × n) (m × n) ℂ) :
    partialTranspose (z • A) = z • partialTranspose A := by
  ext x y
  rfl

theorem partialTranspose_one' {m n : Type*} [DecidableEq m] [DecidableEq n] :
    partialTranspose (1 : Matrix (m × n) (m × n) ℂ) = 1 := by
  ext ⟨a, b⟩ ⟨c, e⟩
  simp only [partialTranspose, Matrix.one_apply, Prod.mk.injEq, @eq_comm _ e b]

theorem expectation_add' {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v : ι → ℂ) :
    expectation (A + B) v = expectation A v + expectation B v := by
  simp only [expectation, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem expectation_smul' {ι : Type*} [Fintype ι] (z : ℂ) (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    expectation (z • A) v = z * expectation A v := by
  simp only [expectation, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem expectation_one_vec {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (C : Matrix m n ℂ) :
    expectation (1 : Matrix (m × n) (m × n) ℂ) (vec C) = ((frobSq C : ℝ) : ℂ) := by
  rw [ofReal_frobSq]
  first
    | (simp only [expectation, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, vec,
        Fintype.sum_prod_type]; done)
    | simp [expectation, Matrix.one_apply, vec, Fintype.sum_prod_type]

/-- `‖J J†‖_F² = 3` for an isometry `J : ℂ³ → ℂ^d`. -/
theorem frobSq_mul_conjTranspose_isometry (J : Matrix (Fin d) (Fin 3) ℂ) (hJ : Jᴴ * J = 1) :
    frobSq (J * Jᴴ) = 3 := by
  have h : ((frobSq (J * Jᴴ) : ℝ) : ℂ) = 3 := by
    rw [ofReal_frobSq_eq_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ J, hJ, Matrix.one_mul, Matrix.trace_mul_comm, hJ,
      Matrix.trace_one]
    simp
  exact_mod_cast h

theorem werner_three_half_expectation_one :
    expectation (partialTranspose (werner 3 (1 / 2))) (vec (1 : Matrix (Fin 3) (Fin 3) ℂ)) =
      -(1 / 5 : ℂ) := by
  have h1 : frobSq (1 : Matrix (Fin 3) (Fin 3) ℂ) = 3 := by
    norm_num [frobSq, Fin.sum_univ_three, Matrix.one_apply]
  have h2 : Complex.normSq (1 : Matrix (Fin 3) (Fin 3) ℂ).trace = 9 := by
    rw [Matrix.trace_one, Fintype.card_fin]
    norm_num [Complex.normSq_apply]
  rw [expectation_partialTranspose_werner, h1, h2]
  norm_num

/-- `⟨vec (J J†), τ_{d,p}^Γ vec (J J†)⟩ = -p/5 + 3(1 - p)/d²`. -/
theorem noisyFamily_expectation (J : Matrix (Fin d) (Fin 3) ℂ) (hJ : Jᴴ * J = 1) (p : ℝ) :
    expectation (partialTranspose (noisyFamily J p)) (vec (J * Jᴴ)) =
      (p : ℂ) * (-(1 / 5 : ℂ)) + (((1 - p) / (d : ℝ) ^ 2 : ℝ) : ℂ) * 3 := by
  have hD : Jᴴ * (J * Jᴴ) * J = 1 := by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul, hJ]
  unfold noisyFamily embedPair
  rw [partialTranspose_add', partialTranspose_smul', partialTranspose_smul', partialTranspose_one',
    expectation_add', expectation_smul', expectation_smul', expectation_partialTranspose_conj_kron,
    hD, werner_three_half_expectation_one, expectation_one_vec,
    frobSq_mul_conjTranspose_isometry J hJ]
  first
    | (simp only [Complex.ofReal_ofNat]; done)
    | (push_cast; ring)
    | norm_num

/-- Manuscript Corollary 6.2: `noisyFamily J p` is NPT for `15/(d² + 15) < p ≤ 1`. -/
theorem noisyFamily_isNPT (J : Matrix (Fin d) (Fin 3) ℂ) (hJ : Jᴴ * J = 1) (hd : 0 < d) {p : ℝ}
    (hp : 15 / ((d : ℝ) ^ 2 + 15) < p) (hp1 : p ≤ 1) : IsNPT (noisyFamily J p) := by
  have hp0 : 0 ≤ p := le_trans (by positivity) hp.le
  rw [isNPT_iff_exists_expectation_re_neg _ (noisyFamily_posSemidef J hp0 hp1).isHermitian]
  refine ⟨vec (J * Jᴴ), ?_⟩
  rw [noisyFamily_expectation J hJ p]
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hd) 2
  have key : 15 < p * ((d : ℝ) ^ 2 + 15) := by
    rwa [div_lt_iff₀ (by positivity)] at hp
  have hval : (p : ℂ) * (-(1 / 5 : ℂ)) + (((1 - p) / (d : ℝ) ^ 2 : ℝ) : ℂ) * 3 =
      ((-(p / 5) + (1 - p) / (d : ℝ) ^ 2 * 3 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hval, Complex.ofReal_re]
  have h3 : (1 - p) / (d : ℝ) ^ 2 * 3 < p / 5 := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ hd2 (by norm_num)]
    nlinarith
  linarith

end ThreeCopyQutritWerner

end
