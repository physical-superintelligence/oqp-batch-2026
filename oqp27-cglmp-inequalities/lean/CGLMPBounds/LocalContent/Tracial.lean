module

public import CGLMPBounds.LocalContent.Core
public import CGLMPBounds.Quantum.Tracial

@[expose] public section


/-!
# Theorem F.3 for projective measurements on `Φ_n`

Supplement, Appendix F.4, Theorem F.3 (local-component bound), in the projective-measurement scope
of the manuscript's conjecture: for projective measurements on the maximally entangled state `Φ_n`,
in the tracial form `q(a,b|x,y) = n⁻¹ Tr(A_x(a) B_y(b))` of `tracialTable`, and `|α|` outcomes for
each of Alice's two measurements,
`LF(q) ≥ (m_A - √(m_A² - 4))/2` with `m_A = 2|α|`; for `d` outcomes this is
`LF(q) ≥ γ_d = d - √(d² - 1)` (F.10).

The vectors of the proof are realised in the Hilbert–Schmidt space `EuclideanSpace ℂ (Fin n × Fin n)`:
`ψ = n^{-1/2} 𝟙`, Alice acts by left and Bob by right multiplication, so
`u^y_{ab} = n^{-1/2} A_0(a) B_y(b)` and `v^y_{cb} = n^{-1/2} A_1(c) B_y(b)` (`vecS`). No purification
or dilation is needed in this scope.

* `IsPVM.mul_eq_zero` : the elements of a PVM are mutually orthogonal;
* `vecM`, `inner_vecM`, `vecS`, `inner_vecS` : the Hilbert–Schmidt inner product `n⁻¹ Tr(Xᴴ Y)`;
* `lowRoot_le_localFraction_tracialTable`, `gamma_le_localFraction_tracialTable` : Theorem F.3;
* `statStrength_le_gamma_tracialTable` : (F.13), `S_μ(q) ≤ (1 - γ_d) Ξ(μ)`.
-/

open scoped ComplexOrder
open Matrix

namespace CGLMPBounds

noncomputable section

variable {n : ℕ}

/-- `Tr(PQ) = Tr((PQ)ᴴ PQ)` for orthogonal projections `P`, `Q`. -/
theorem trace_proj_mul_eq {P Q : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (hP2 : P * P = P) (hQ : Q.IsHermitian) (hQ2 : Q * Q = Q) :
    Matrix.trace (P * Q) = Matrix.trace ((P * Q)ᴴ * (P * Q)) := by
  rw [Matrix.conjTranspose_mul, hP.eq, hQ.eq, Matrix.mul_assoc, ← Matrix.mul_assoc P P Q, hP2,
    Matrix.trace_mul_comm Q (P * Q), Matrix.mul_assoc, hQ2]

/-- `Tr(B X B) = Tr(X B)` for an idempotent `B`. -/
theorem trace_sandwich {B X : Matrix (Fin n) (Fin n) ℂ} (hB2 : B * B = B) :
    Matrix.trace (B * X * B) = Matrix.trace (X * B) := by
  rw [Matrix.trace_mul_comm (B * X) B, ← Matrix.mul_assoc, hB2, Matrix.trace_mul_comm]

/-- The elements of a projective measurement are mutually orthogonal. -/
theorem IsPVM.mul_eq_zero {α : Type*} [Fintype α] [DecidableEq α]
    {P : α → Matrix (Fin n) (Fin n) ℂ} (hP : IsPVM P) {a a' : α} (h : a ≠ a') :
    P a' * P a = 0 := by
  have hnn : ∀ b, 0 ≤ (Matrix.trace (P b * P a)).re := fun b =>
    re_trace_mul_nonneg (hP.isHermitian b) (hP.mul_self b) (hP.isHermitian a) (hP.mul_self a)
  have hsum : ∑ b, (Matrix.trace (P b * P a)).re = (Matrix.trace (P a)).re :=
    sum_left_re_trace_mul hP.sum_eq_one
  have hself : (Matrix.trace (P a * P a)).re = (Matrix.trace (P a)).re := by
    rw [hP.mul_self a]
  have hsplit : (Matrix.trace (P a * P a)).re
      + ∑ x ∈ Finset.univ.erase a, (Matrix.trace (P x * P a)).re
      = ∑ x, (Matrix.trace (P x * P a)).re :=
    Finset.add_sum_erase Finset.univ (fun x => (Matrix.trace (P x * P a)).re) (Finset.mem_univ a)
  have hle : (Matrix.trace (P a' * P a)).re
      ≤ ∑ x ∈ Finset.univ.erase a, (Matrix.trace (P x * P a)).re :=
    Finset.single_le_sum (fun b _ => hnn b)
      (Finset.mem_erase.mpr ⟨fun e => h e.symm, Finset.mem_univ a'⟩)
  have hre : (Matrix.trace (P a' * P a)).re = 0 :=
    le_antisymm (by linarith) (hnn a')
  have hX : Matrix.trace ((P a' * P a)ᴴ * (P a' * P a)) = 0 := by
    have e := trace_proj_mul_eq (hP.isHermitian a') (hP.mul_self a') (hP.isHermitian a)
      (hP.mul_self a)
    have h0 := Complex.nonneg_iff.mp
      (Matrix.posSemidef_conjTranspose_mul_self (P a' * P a)).trace_nonneg
    apply Complex.ext
    · rw [← e, hre, Complex.zero_re]
    · rw [Complex.zero_im, ← h0.2]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hX

/-- The vectorisation of a matrix, with the Hilbert–Schmidt inner product. -/
def vecM (X : Matrix (Fin n) (Fin n) ℂ) : EuclideanSpace ℂ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun ij : Fin n × Fin n => X ij.1 ij.2)

theorem inner_vecM (X Y : Matrix (Fin n) (Fin n) ℂ) :
    inner ℂ (vecM X) (vecM Y) = Matrix.trace (Xᴴ * Y) := by
  unfold vecM
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct, Fintype.sum_prod_type, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- The vector `X ψ` for `ψ = n^{-1/2} 𝟙` in the Hilbert–Schmidt picture of `Φ_n`. -/
def vecS (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) : EuclideanSpace ℂ (Fin n × Fin n) :=
  vecM ((Real.sqrt n)⁻¹ • X)

theorem inner_vecS (X Y : Matrix (Fin n) (Fin n) ℂ) :
    inner ℂ (vecS n X) (vecS n Y) = (((n : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace (Xᴴ * Y) := by
  unfold vecS
  rw [inner_vecM, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul, Complex.real_smul, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg n)]

theorem norm_vecS_sq (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖vecS n X‖ ^ 2 = (n : ℝ)⁻¹ * (Matrix.trace (Xᴴ * X)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_vecS, RCLike.re_to_complex, Complex.re_ofReal_mul]

theorem norm_vecS_proj_sq {P Q : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (hP2 : P * P = P) (hQ : Q.IsHermitian) (hQ2 : Q * Q = Q) :
    ‖vecS n (P * Q)‖ ^ 2 = (n : ℝ)⁻¹ * (Matrix.trace (P * Q)).re := by
  rw [norm_vecS_sq, ← trace_proj_mul_eq hP hP2 hQ hQ2]

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The Gram data of the Hilbert–Schmidt vectors `u^y_{ab} = n^{-1/2} A_0(a) B_y(b)` and
`v^y_{cb} = n^{-1/2} A_1(c) B_y(b)` of a tracial behaviour of projective measurements on `Φ_n`. -/
theorem tracial_gram [NeZero n]
    {A : Fin 2 → α → Matrix (Fin n) (Fin n) ℂ} {B : Fin 2 → β → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ x, IsPVM (A x)) (hB : ∀ y, IsPVM (B y)) :
    (∀ y a b, tracialTable A B 0 y a b = ‖vecS n (A 0 a * B y b)‖ ^ 2) ∧
    (∀ y c b, tracialTable A B 1 y c b = ‖vecS n (A 1 c * B y b)‖ ^ 2) ∧
    (∀ (x y : Fin 2) (b : β) (a a' : α), a ≠ a' →
      inner ℂ (vecS n (A x a * B y b)) (vecS n (A x a' * B y b)) = 0) ∧
    (∀ y a c, ∑ b, inner ℂ (vecS n (A 0 a * B y b)) (vecS n (A 1 c * B y b))
      = (((n : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace (A 0 a * A 1 c)) ∧
    (∀ y a, ∑ b, ‖vecS n (A 0 a * B y b)‖ ^ 2 = (n : ℝ)⁻¹ * (Matrix.trace (A 0 a)).re) ∧
    (∀ y c, ∑ b, ‖vecS n (A 1 c * B y b)‖ ^ 2 = (n : ℝ)⁻¹ * (Matrix.trace (A 1 c)).re) ∧
    (∀ a c, ‖(((n : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace (A 0 a * A 1 c)‖ ^ 2
      ≤ ((n : ℝ)⁻¹ * (Matrix.trace (A 0 a)).re) * ((n : ℝ)⁻¹ * (Matrix.trace (A 1 c)).re)) ∧
    ∑ a, ∑ c, (((n : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace (A 0 a * A 1 c) = 1 := by
  have hq0 : ∀ y a b, tracialTable A B 0 y a b = ‖vecS n (A 0 a * B y b)‖ ^ 2 := by
    intro y a b
    rw [norm_vecS_proj_sq ((hA 0).isHermitian a) ((hA 0).mul_self a) ((hB y).isHermitian b)
      ((hB y).mul_self b)]
    show (Matrix.trace (A 0 a * B y b)).re / n = _
    ring
  have hq1 : ∀ y c b, tracialTable A B 1 y c b = ‖vecS n (A 1 c * B y b)‖ ^ 2 := by
    intro y c b
    rw [norm_vecS_proj_sq ((hA 1).isHermitian c) ((hA 1).mul_self c) ((hB y).isHermitian b)
      ((hB y).mul_self b)]
    show (Matrix.trace (A 1 c * B y b)).re / n = _
    ring
  have horth : ∀ (x : Fin 2) (y : Fin 2) (b : β) (a a' : α), a ≠ a' →
      inner ℂ (vecS n (A x a * B y b)) (vecS n (A x a' * B y b)) = 0 := by
    intro x y b a a' h
    rw [inner_vecS, Matrix.conjTranspose_mul, ((hB y).isHermitian b).eq,
      ((hA x).isHermitian a).eq,
      show B y b * A x a * (A x a' * B y b) = B y b * (A x a * A x a') * B y b by
        simp only [Matrix.mul_assoc],
      (hA x).mul_eq_zero (fun e => h e.symm), Matrix.mul_zero, Matrix.zero_mul,
      Matrix.trace_zero, mul_zero]
  have hk : ∀ y a c, ∑ b, inner ℂ (vecS n (A 0 a * B y b)) (vecS n (A 1 c * B y b))
      = (((n : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace (A 0 a * A 1 c) := by
    intro y a c
    have h1 : ∀ b, inner ℂ (vecS n (A 0 a * B y b)) (vecS n (A 1 c * B y b))
        = (((n : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace (A 0 a * A 1 c * B y b) := by
      intro b
      rw [inner_vecS, Matrix.conjTranspose_mul, ((hB y).isHermitian b).eq,
        ((hA 0).isHermitian a).eq,
        show B y b * A 0 a * (A 1 c * B y b) = B y b * (A 0 a * A 1 c) * B y b by
          simp only [Matrix.mul_assoc],
        trace_sandwich ((hB y).mul_self b)]
    rw [Finset.sum_congr rfl (fun b _ => h1 b), ← Finset.mul_sum, ← Matrix.trace_sum,
      ← Finset.mul_sum, (hB y).sum_eq_one, Matrix.mul_one]
  have hpA : ∀ y a, ∑ b, ‖vecS n (A 0 a * B y b)‖ ^ 2 = (n : ℝ)⁻¹ * (Matrix.trace (A 0 a)).re := by
    intro y a
    rw [Finset.sum_congr rfl (fun b _ => norm_vecS_proj_sq ((hA 0).isHermitian a)
      ((hA 0).mul_self a) ((hB y).isHermitian b) ((hB y).mul_self b)), ← Finset.mul_sum,
      sum_right_re_trace_mul (hB y).sum_eq_one]
  have hpC : ∀ y c, ∑ b, ‖vecS n (A 1 c * B y b)‖ ^ 2 = (n : ℝ)⁻¹ * (Matrix.trace (A 1 c)).re := by
    intro y c
    rw [Finset.sum_congr rfl (fun b _ => norm_vecS_proj_sq ((hA 1).isHermitian c)
      ((hA 1).mul_self c) ((hB y).isHermitian b) ((hB y).mul_self b)), ← Finset.mul_sum,
      sum_right_re_trace_mul (hB y).sum_eq_one]
  have hkCS : ∀ a c, ‖(((n : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace (A 0 a * A 1 c)‖ ^ 2
      ≤ ((n : ℝ)⁻¹ * (Matrix.trace (A 0 a)).re) * ((n : ℝ)⁻¹ * (Matrix.trace (A 1 c)).re) := by
    intro a c
    have e1 : (((n : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace (A 0 a * A 1 c)
        = inner ℂ (vecS n (A 0 a)) (vecS n (A 1 c)) := by
      rw [inner_vecS, ((hA 0).isHermitian a).eq]
    have e2 : ‖vecS n (A 0 a)‖ ^ 2 = (n : ℝ)⁻¹ * (Matrix.trace (A 0 a)).re := by
      rw [norm_vecS_sq, ((hA 0).isHermitian a).eq, (hA 0).mul_self a]
    have e3 : ‖vecS n (A 1 c)‖ ^ 2 = (n : ℝ)⁻¹ * (Matrix.trace (A 1 c)).re := by
      rw [norm_vecS_sq, ((hA 1).isHermitian c).eq, (hA 1).mul_self c]
    rw [e1, ← e2, ← e3]
    exact norm_inner_sq_le _ _
  have hk1 : ∑ a, ∑ c, (((n : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace (A 0 a * A 1 c) = 1 := by
    have h : ∀ a, ∑ c, (((n : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace (A 0 a * A 1 c)
        = (((n : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace (A 0 a) := by
      intro a
      rw [← Finset.mul_sum, ← Matrix.trace_sum, ← Finset.mul_sum, (hA 1).sum_eq_one,
        Matrix.mul_one]
    rw [Finset.sum_congr rfl (fun a _ => h a), ← Finset.mul_sum, ← Matrix.trace_sum,
      (hA 0).sum_eq_one, Matrix.trace_one, Fintype.card_fin, Complex.ofReal_inv,
      Complex.ofReal_natCast, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n))]
  exact ⟨hq0, hq1, horth, hk, hpA, hpC, hkCS, hk1⟩

/-- **Theorem F.3 (local-component bound), projective measurements on `Φ_n`.** If each of Alice's
two measurements has `|α|` outcomes, then `LF(q) ≥ (m_A - √(m_A² - 4))/2` with `m_A = 2|α|`. -/
theorem lowRoot_le_localFraction_tracialTable [NeZero n]
    {A : Fin 2 → α → Matrix (Fin n) (Fin n) ℂ} {B : Fin 2 → β → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ x, IsPVM (A x)) (hB : ∀ y, IsPVM (B y)) :
    lowRoot (2 * Fintype.card α) 1 ≤ localFraction (tracialTable A B) := by
  obtain ⟨hq0, hq1, horth, hk, hpA, hpC, hkCS, hk1⟩ := tracial_gram hA hB
  exact lowRoot_le_localFraction (u := fun y a b => vecS n (A 0 a * B y b))
    (v := fun y c b => vecS n (A 1 c * B y b))
    (k := fun a c => (((n : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace (A 0 a * A 1 c))
    (pA := fun a => (n : ℝ)⁻¹ * (Matrix.trace (A 0 a)).re)
    (pC := fun c => (n : ℝ)⁻¹ * (Matrix.trace (A 1 c)).re)
    (tracialTable_isNoSignalling hA hB) hq0 hq1 (horth 0) (horth 1) hk hpA hpC hkCS hk1

/-- **Theorem F.3, general form, projective measurements on `Φ_n`.** If the nonzero elements of
Alice's measurement `0` have outcomes in `S₀` and those of measurement `1` in `S₁` (so the two
measurements have `m₀ = |S₀|` and `m₁ = |S₁|` outcomes), then `LF(q) ≥ (m_A - √(m_A² - 4))/2` with
`m_A = m₀ + m₁`. -/
theorem lowRoot_le_localFraction_tracialTable_support [NeZero n]
    {A : Fin 2 → α → Matrix (Fin n) (Fin n) ℂ} {B : Fin 2 → β → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ x, IsPVM (A x)) (hB : ∀ y, IsPVM (B y)) (S₀ S₁ : Finset α)
    (h₀ : ∀ a ∉ S₀, A 0 a = 0) (h₁ : ∀ c ∉ S₁, A 1 c = 0) :
    lowRoot (S₀.card + S₁.card) 1 ≤ localFraction (tracialTable A B) := by
  obtain ⟨hq0, hq1, horth, hk, hpA, hpC, hkCS, hk1⟩ := tracial_gram hA hB
  exact lowRoot_le_localFraction_support (u := fun y a b => vecS n (A 0 a * B y b))
    (v := fun y c b => vecS n (A 1 c * B y b))
    (k := fun a c => (((n : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace (A 0 a * A 1 c))
    (pA := fun a => (n : ℝ)⁻¹ * (Matrix.trace (A 0 a)).re)
    (pC := fun c => (n : ℝ)⁻¹ * (Matrix.trace (A 1 c)).re)
    (tracialTable_isNoSignalling hA hB) hq0 hq1 (horth 0) (horth 1) hk hpA hpC hkCS hk1 S₀ S₁
    (fun a ha => by
      show (n : ℝ)⁻¹ * (Matrix.trace (A 0 a)).re = 0
      rw [h₀ a ha, Matrix.trace_zero, Complex.zero_re, mul_zero])
    (fun c hc => by
      show (n : ℝ)⁻¹ * (Matrix.trace (A 1 c)).re = 0
      rw [h₁ c hc, Matrix.trace_zero, Complex.zero_re, mul_zero])

/-- **Theorem F.3, (F.10), projective measurements on `Φ_n`.** With `d` outcomes per measurement,
`LF(q) ≥ γ_d = d - √(d² - 1)`. -/
theorem gamma_le_localFraction_tracialTable [NeZero n] {d : ℕ}
    {A : Fin 2 → Fin d → Matrix (Fin n) (Fin n) ℂ} {B : Fin 2 → Fin d → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ x, IsPVM (A x)) (hB : ∀ y, IsPVM (B y)) :
    (d : ℝ) - Real.sqrt ((d : ℝ) ^ 2 - 1) ≤ localFraction (tracialTable A B) := by
  have h := lowRoot_le_localFraction_tracialTable hA hB
  rwa [Fintype.card_fin, lowRoot_two_mul_one] at h

/-- **(F.13), projective measurements on `Φ_n`.** `S_μ(q) ≤ (1 - γ_d) Ξ(μ)` for every input law. -/
theorem statStrength_le_gamma_tracialTable [NeZero n] {d : ℕ}
    {A : Fin 2 → Fin d → Matrix (Fin n) (Fin n) ℂ} {B : Fin 2 → Fin d → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ x, IsPVM (A x)) (hB : ∀ y, IsPVM (B y)) {μ : Fin 2 → Fin 2 → ℝ}
    (hμ : ∀ x y, 0 ≤ μ x y) (hμ1 : ∑ x, ∑ y, μ x y = 1) :
    statStrength μ (tracialTable A B)
      ≤ ENNReal.ofReal (1 - ((d : ℝ) - Real.sqrt ((d : ℝ) ^ 2 - 1))) * xiMin μ := by
  refine (statStrength_le_localFraction (tracialTable_isNoSignalling hA hB) hμ hμ1).trans ?_
  have hγ := gamma_le_localFraction_tracialTable hA hB
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) zero_le

end

end CGLMPBounds
