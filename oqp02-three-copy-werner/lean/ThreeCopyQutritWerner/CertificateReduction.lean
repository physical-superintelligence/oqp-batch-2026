module

public import ThreeCopyQutritWerner.HFeature
public import ThreeCopyQutritWerner.NoisyFamily
public import ThreeCopyQutritWerner.RankOne
public import ThreeCopyQutritWerner.RankTwo
public import ThreeCopyQutritWerner.TwoCutFactor
public import ThreeCopyQutritWerner.Physical
public import ThreeCopyQutritWerner.Distillation

@[expose] public section


/-!
# T2.1a: the certificate-free part of the endpoint soundness argument (Section 4.1)

This module proves the soundness step of Section 4.1: T2.1a (`QutritEndpointInequality`) follows
from an exact endpoint certificate, that is, a Hermitian `Ph` (the manuscript's carrier projector
`Π_h`) fixing every feature `z_h` (Appendix B), and positive semidefinite `G_h, G_m, G_a` with
`Π_h (T ⊗ I) Π_h = G_h + Π_h Γ₃₄(G_m) Π_h + Π_h Γ₁₂₃₄(G_a) Π_h` (eq. (14)). These hypotheses are the
certificate data of claims AppB, S4.1, L4.1, S4.3, Tab1-d3, D1-spectral and D4-packaging.

Register layout. One copy of `H = (ℂ³)^{⊗3}` is indexed by `Fin 3 × Fin 3 × Fin 3`; the six
registers are indexed by `SixRegisters = ((H × H) × (H × H)) × (H × H)`, read as
`(((row, col), (p₁, p₂)), (p₃, p₄))`. The manuscript orders them `(row, p₁, p₂, p₃, p₄, col)`;
this is a relabelling. `T = ∏ᵢ (I - Ωᵢ/2)` acts on `(row, col)`. Since
`ρ_{d,α}^Γ = (I - α Ω)/(d (d - α))`, it equals `(15/2)³ (ρ_{3,1/2}^{⊗3})^Γ`, which is its
definition here (`endpointOperator`, in `Basic.lean`), so `⟨vec C, T vec C⟩ = q(C)` is eq. (6)
(`expectation_endpointOperator`). `Γ₃₄` (`partialTranspose`) transposes the last pair
`(p₃, p₄)`; `Γ₁₂₃₄` (`minorTranspose`) transposes both pairs.

Contents:
* `expectation_partialTranspose_prod`, `expectation_minorTranspose_prod`: on product vectors, a
  partial transpose inside an expectation conjugates the transposed factors (note, steps 2–3);
* `expectation_liftRowCol`: `⟨u ⊗ v ⊗ w, (T ⊗ I ⊗ I)(u ⊗ v ⊗ w)⟩ = ⟨u, T u⟩ ‖v‖² ‖w‖²`;
* `expectation_featureH`: `⟨z_h, (T ⊗ I) z_h⟩ = ‖p‖⁴ q(C)` (step 1);
* `featureH_soundness`: eq. (15),
  `‖p‖⁴ q(C) = ⟨z_h, G_h z_h⟩ + ⟨z_m, G_m z_m⟩ + ⟨z_a, G_a z_a⟩` (step 4);
* `rank_le_one_of_frobSq_bivecMat_eq_zero`: `p = 0` forces `rank (X B) ≤ 1`;
* `qutritEndpointInequality_of_certificate`: the reduction (rank at most one by
  `endpointEnergy_ketBra_ge`; rank two because then `p ≠ 0`).

The manuscript also has `Π_s G_s Π_s = G_s` and `Π_h` a projector; soundness needs neither, so
neither is assumed.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace ThreeCopyQutritWerner

section ProductVectors

/-- For a product vector, transposing the second factor inside an expectation conjugates that
factor: `⟨u ⊗ v, G^Γ (u ⊗ v)⟩ = ⟨u ⊗ v̄, G (u ⊗ v̄)⟩`. -/
theorem expectation_partialTranspose_prod {m n : Type*} [Fintype m] [Fintype n]
    (G : Matrix (m × n) (m × n) ℂ) (u : m → ℂ) (v : n → ℂ) :
    expectation (partialTranspose G) (fun x => u x.1 * v x.2) =
      expectation G (fun x => u x.1 * star (v x.2)) := by
  unfold expectation
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    ⟨fun p => ((p.1.1, p.2.2), (p.2.1, p.1.2)), fun p => ((p.1.1, p.2.2), (p.2.1, p.1.2)),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => ?_
  simp only [Equiv.coe_fn_mk, partialTranspose, star_mul', star_star]
  ring

/-- `⟨u ⊗ v ⊗ w, Γ₁₂₃₄(G) (u ⊗ v ⊗ w)⟩ = ⟨u ⊗ v̄ ⊗ w̄, G (u ⊗ v̄ ⊗ w̄)⟩`. -/
theorem expectation_minorTranspose_prod {r b c : Type*} [Fintype r] [Fintype b] [Fintype c]
    (G : Matrix ((r × b) × c) ((r × b) × c) ℂ) (u : r → ℂ) (v : b → ℂ) (w : c → ℂ) :
    expectation (minorTranspose G) (fun x => u x.1.1 * v x.1.2 * w x.2) =
      expectation G (fun x => u x.1.1 * star (v x.1.2) * star (w x.2)) := by
  unfold expectation
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    ⟨fun p => (((p.1.1.1, p.2.1.2), p.2.2), ((p.2.1.1, p.1.1.2), p.1.2)),
      fun p => (((p.1.1.1, p.2.1.2), p.2.2), ((p.2.1.1, p.1.1.2), p.1.2)),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => ?_
  simp only [Equiv.coe_fn_mk, minorTranspose, star_mul', star_star]
  ring

/-- `⟨φ ⊗ χ, (A ⊗ B)(φ ⊗ χ)⟩ = ⟨φ, A φ⟩ ⟨χ, B χ⟩`. -/
theorem expectation_prod_prod {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m m ℂ)
    (B : Matrix n n ℂ) (φ : m → ℂ) (χ : n → ℂ) :
    expectation (fun x y : m × n => A x.1 y.1 * B x.2 y.2 : Matrix (m × n) (m × n) ℂ)
        (fun x => φ x.1 * χ x.2) =
      expectation A φ * expectation B χ := by
  unfold expectation
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [star_mul']
  ring

/-- `⟨w, I w⟩ = ‖w‖²`. -/
theorem expectation_one_eq_vecNormSq {n : Type*} [Fintype n] [DecidableEq n] (w : n → ℂ) :
    expectation (1 : Matrix n n ℂ) w = (vecNormSq w : ℂ) := by
  unfold expectation vecNormSq
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x, Matrix.one_apply_eq, mul_one, Complex.normSq_eq_conj_mul_self,
    starRingEnd_apply]
  · intro y _ hy
    rw [Matrix.one_apply_ne' hy, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- `⟨u ⊗ v ⊗ w, (T ⊗ I ⊗ I)(u ⊗ v ⊗ w)⟩ = ⟨u, T u⟩ ‖v‖² ‖w‖²`. -/
theorem expectation_liftRowCol {r b c : Type*} [Fintype r] [Fintype b] [Fintype c]
    [DecidableEq b] [DecidableEq c] (T : Matrix r r ℂ) (u : r → ℂ) (v : b → ℂ) (w : c → ℂ) :
    expectation (liftRowCol T) (fun x => u x.1.1 * v x.1.2 * w x.2) =
      expectation T u * (vecNormSq v : ℂ) * (vecNormSq w : ℂ) := by
  have h1 : expectation (liftRowCol T) (fun x => u x.1.1 * v x.1.2 * w x.2) =
      expectation (fun x y : r × b => T x.1 y.1 * (1 : Matrix b b ℂ) x.2 y.2 :
          Matrix (r × b) (r × b) ℂ) (fun x => u x.1 * v x.2) *
        expectation (1 : Matrix c c ℂ) w :=
    expectation_prod_prod (fun x y : r × b => T x.1 y.1 * (1 : Matrix b b ℂ) x.2 y.2)
      (1 : Matrix c c ℂ) (fun x => u x.1 * v x.2) w
  have h2 : expectation (fun x y : r × b => T x.1 y.1 * (1 : Matrix b b ℂ) x.2 y.2 :
        Matrix (r × b) (r × b) ℂ) (fun x => u x.1 * v x.2) =
      expectation T u * expectation (1 : Matrix b b ℂ) v :=
    expectation_prod_prod T (1 : Matrix b b ℂ) u v
  rw [h1, h2, expectation_one_eq_vecNormSq, expectation_one_eq_vecNormSq]

/-- `‖vec P‖² = ‖P‖_F²`. -/
theorem vecNormSq_vec {m n : Type*} [Fintype m] [Fintype n] (P : Matrix m n ℂ) :
    vecNormSq (vec P) = frobSq P := by
  simp only [vecNormSq, frobSq, vec, Fintype.sum_prod_type]

/-- A positive semidefinite matrix has nonnegative real expectations. -/
theorem expectation_re_nonneg_of_posSemidef {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) (φ : ι → ℂ) : 0 ≤ (expectation M φ).re := by
  have h1 : 0 ≤ star φ ⬝ᵥ (M *ᵥ φ) := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hM).2 φ
  rw [← expectation_eq_dotProduct] at h1
  exact (Complex.nonneg_iff.mp h1).1

end ProductVectors

/-- `⟨vec C, T vec C⟩ = q(C)`: the built eq. (6) at `d = 3`, `α = 1/2`. -/
theorem expectation_endpointOperator
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    expectation endpointOperator (vec C) = (endpointEnergy C : ℂ) := by
  rw [endpointOperator, expectation_smul', expectation_partialTranspose_tripleCopy_werner]
  unfold endpointEnergy
  push_cast
  ring

/-- The feature `z_m = vec C ⊗ p ⊗ p̄`. -/
def featureM (C P : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    SixRegisters → ℂ :=
  fun x => vec C x.1.1 * vec P x.1.2 * star (vec P x.2)

/-- The feature `z_a = vec C ⊗ p̄ ⊗ p̄`. -/
def featureA (C P : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    SixRegisters → ℂ :=
  fun x => vec C x.1.1 * star (vec P x.1.2) * star (vec P x.2)

/-- Step 1: `⟨z_h, (T ⊗ I) z_h⟩ = ‖p‖⁴ q(C)`. -/
theorem expectation_featureH (C P : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    expectation sixRegisterOperator (featureH C P) =
      ((frobSq P ^ 2 * endpointEnergy C : ℝ) : ℂ) := by
  have h : expectation sixRegisterOperator (featureH C P) =
      expectation endpointOperator (vec C) * (vecNormSq (vec P) : ℂ) *
        (vecNormSq (vec P) : ℂ) :=
    expectation_liftRowCol endpointOperator (vec C) (vec P) (vec P)
  rw [h, expectation_endpointOperator, vecNormSq_vec]
  push_cast
  ring

/-- Eq. (15): a Hermitian `Ph` fixing `z_h` and a Gram decomposition (eq. (14)) give
`‖p‖⁴ q(C) = ⟨z_h, G_h z_h⟩ + ⟨z_m, G_m z_m⟩ + ⟨z_a, G_a z_a⟩`. -/
theorem featureH_soundness (C P : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (Ph Gh Gm Ga : Matrix SixRegisters SixRegisters ℂ) (hPh : Phᴴ = Ph)
    (hz : Ph *ᵥ featureH C P = featureH C P)
    (hgram : Ph * sixRegisterOperator * Ph =
      Gh + Ph * partialTranspose Gm * Ph + Ph * minorTranspose Ga * Ph) :
    ((frobSq P ^ 2 * endpointEnergy C : ℝ) : ℂ) =
      expectation Gh (featureH C P) + expectation Gm (featureM C P) +
        expectation Ga (featureA C P) := by
  have hconj : ∀ M : Matrix SixRegisters SixRegisters ℂ,
      expectation (Ph * M * Ph) (featureH C P) = expectation M (featureH C P) := by
    intro M
    have h := expectation_mulVec_conj M Ph (featureH C P)
    rw [hz, hPh] at h
    exact h.symm
  have hm : expectation (partialTranspose Gm) (featureH C P) = expectation Gm (featureM C P) :=
    expectation_partialTranspose_prod Gm (fun y => vec C y.1 * vec P y.2) (vec P)
  have ha : expectation (minorTranspose Ga) (featureH C P) = expectation Ga (featureA C P) :=
    expectation_minorTranspose_prod Ga (vec C) (vec P) (vec P)
  rw [← expectation_featureH, ← hconj sixRegisterOperator, hgram, expectation_add',
    expectation_add', hconj, hconj, hm, ha]

/-- Soundness for one `C`: with `p ≠ 0`, the certificate gives `q(C) ≥ 0`. -/
theorem endpointEnergy_nonneg_of_certificate
    (C P : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (Ph Gh Gm Ga : Matrix SixRegisters SixRegisters ℂ) (hPh : Phᴴ = Ph)
    (hz : Ph *ᵥ featureH C P = featureH C P)
    (hgram : Ph * sixRegisterOperator * Ph =
      Gh + Ph * partialTranspose Gm * Ph + Ph * minorTranspose Ga * Ph)
    (hpsd : Gh.PosSemidef ∧ Gm.PosSemidef ∧ Ga.PosSemidef) (hP : 0 < frobSq P) :
    0 ≤ endpointEnergy C := by
  have hre := congrArg Complex.re (featureH_soundness C P Ph Gh Gm Ga hPh hz hgram)
  rw [Complex.ofReal_re, Complex.add_re, Complex.add_re] at hre
  have h1 := expectation_re_nonneg_of_posSemidef hpsd.1 (featureH C P)
  have h2 := expectation_re_nonneg_of_posSemidef hpsd.2.1 (featureM C P)
  have h3 := expectation_re_nonneg_of_posSemidef hpsd.2.2 (featureA C P)
  have hsq : 0 < frobSq P ^ 2 := pow_pos hP 2
  by_contra hneg
  have := mul_neg_of_pos_of_neg hsq (not_le.mp hneg)
  linarith

/-- If the bivector of `X = [x, y]` vanishes, then `x` and `y` are dependent and
`rank (X B) ≤ 1`. -/
theorem rank_le_one_of_frobSq_bivecMat_eq_zero {n : Type*} [Fintype n] (X : Matrix n (Fin 2) ℂ)
    (B : Matrix (Fin 2) n ℂ) (h : frobSq (bivecMat X) = 0) : (X * B).rank ≤ 1 := by
  have hP : ∀ i j, X i 0 * X j 1 - X i 1 * X j 0 = 0 := by
    intro i j
    have h0 : bivecMat X i j = 0 :=
      eq_zero_of_vecNormSq_eq_zero (vec (bivecMat X)) (by rw [vecNormSq_vec]; exact h) (i, j)
    rw [bivecMat_apply] at h0
    rcases mul_eq_zero.mp h0 with h2 | h2
    · exact absurd (Complex.ofReal_eq_zero.mp h2)
        (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num)))
    · exact h2
  by_cases hx : ∀ i, X i 0 = 0
  · refine (rank_le_iff_exists_mul (X * B) 1).mpr
      ⟨Matrix.of fun i _ => X i 1, Matrix.of fun _ j => B 1 j, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.of_apply, hx i,
      zero_mul, zero_add]
  · push_neg at hx
    obtain ⟨i₀, hi₀⟩ := hx
    refine (rank_le_iff_exists_mul (X * B) 1).mpr
      ⟨Matrix.of fun i _ => X i 0, Matrix.of fun _ j => B 0 j + X i₀ 1 / X i₀ 0 * B 1 j, ?_⟩
    ext i j
    have hrel := hP i₀ i
    have hw : X i₀ 0 * (X i₀ 0)⁻¹ = 1 := mul_inv_cancel₀ hi₀
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.of_apply]
    linear_combination B 1 j * (X i₀ 0)⁻¹ * hrel - B 1 j * X i 1 * hw

/-- THE REDUCTION (not a proof of T2.1a): an exact endpoint certificate (a Hermitian `Ph`
fixing every feature `z_h`, eq. (14), and positive semidefinite blocks) implies the qutrit
endpoint inequality. -/
theorem qutritEndpointInequality_of_certificate
    (Ph Gh Gm Ga : Matrix SixRegisters SixRegisters ℂ) (hPh : Phᴴ = Ph)
    (hcarrier : ∀ (X : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 2) ℂ)
      (B : Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ),
      Ph *ᵥ featureH (X * B) (bivecMat X) = featureH (X * B) (bivecMat X))
    (hgram : Ph * sixRegisterOperator * Ph =
      Gh + Ph * partialTranspose Gm * Ph + Ph * minorTranspose Ga * Ph)
    (hpsd : Gh.PosSemidef ∧ Gm.PosSemidef ∧ Ga.PosSemidef) :
    QutritEndpointInequality := by
  unfold QutritEndpointInequality
  intro C hC
  by_cases h1 : C.rank ≤ 1
  · obtain ⟨u, v, rfl⟩ := exists_eq_ketBra_of_rank_le_one C h1
    exact le_trans (div_nonneg (mul_nonneg (vecNormSq_nonneg u) (vecNormSq_nonneg v))
      (by norm_num)) (endpointEnergy_ketBra_ge u v)
  · obtain ⟨X, B, rfl⟩ := (rank_le_iff_exists_mul C 2).mp hC
    have hP : 0 < frobSq (bivecMat X) := by
      rcases (frobSq_nonneg (bivecMat X)).lt_or_eq with h | h
      · exact h
      · exact absurd (rank_le_one_of_frobSq_bivecMat_eq_zero X B h.symm) h1
    exact endpointEnergy_nonneg_of_certificate (X * B) (bivecMat X) Ph Gh Gm Ga hPh
      (hcarrier X B) hgram hpsd hP

end ThreeCopyQutritWerner

end
