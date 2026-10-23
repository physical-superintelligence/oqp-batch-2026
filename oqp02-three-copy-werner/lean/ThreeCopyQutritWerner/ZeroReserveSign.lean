module

public import ThreeCopyQutritWerner.SharpPartialTrace
public import ThreeCopyQutritWerner.ZeroReserveCauchy
public import ThreeCopyQutritWerner.PositiveRankTwo

@[expose] public section


/-!
# The sharp three-cut cross inequality and nonnegative positive-source reserve

Each reduced transition is trace zero for orthogonal rays. The literal sharp
partial-trace bound combines with the proved exterior-transition estimate at
all three cuts, then the exact finite Cauchy inequality. This proves the reserve
sign for every nonnegative two-ray spectral combination. Equality rigidity is
not assumed and remains a separate obligation.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace ThreeCopyQutritWerner

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- The three original one-site linear entropy deficits, in site order 1,2,3. -/
def zeroReserveLocalDeficit (u : a × b × c → ℂ) : Fin 3 → ℝ :=
  ![1 - frobSq (ptrace₂₃ (ketBra u u)),
    1 - frobSq (ptrace₁₃ (ketBra u u)),
    1 - frobSq (ptrace₁₂ (ketBra u u))]

/-- The cut cross quantities count each double partial trace exactly twice on summation. -/
def zeroReserveCutCross (u v : a × b × c → ℂ) : Fin 3 → ℝ :=
  ![frobSq (ptrace₁₂ (ketBra u v)) + frobSq (ptrace₁₃ (ketBra u v)) -
      frobSq (ptrace₁ (ketBra u v)),
    frobSq (ptrace₁₂ (ketBra u v)) + frobSq (ptrace₂₃ (ketBra u v)) -
      frobSq (ptrace₂ (ketBra u v)),
    frobSq (ptrace₁₃ (ketBra u v)) + frobSq (ptrace₂₃ (ketBra u v)) -
      frobSq (ptrace₃ (ketBra u v))]

theorem zeroReserveLocalDeficit_nonneg (u : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (i : Fin 3) : 0 ≤ zeroReserveLocalDeficit u i := by
  obtain ⟨h1, h2, h3⟩ := zeroReserveLocalEntropy_deficits_nonneg u hu
  fin_cases i
  · exact h1
  · exact h2
  · exact h3

theorem zeroReserveLocalDeficit_sum (u : a × b × c → ℂ) :
    (∑ i : Fin 3, zeroReserveLocalDeficit u i) = zeroReserveLocalEntropy u := by
  rw [zeroReserveLocalEntropy_eq]
  simp [zeroReserveLocalDeficit, Fin.sum_univ_three]

theorem zeroReserveCutCross_sum (u v : a × b × c → ℂ) :
    (∑ i : Fin 3, zeroReserveCutCross u v i) = 2 * invB (ketBra u v) - invA (ketBra u v) := by
  simp only [zeroReserveCutCross, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, invA, invB]
  ring

variable [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- The sharp cutwise geometric-mean inequality with all contractions retained. -/
theorem zeroReserveCutCross_le (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0) (i : Fin 3) :
    zeroReserveCutCross u v i ≤ Real.sqrt (zeroReserveLocalDeficit u i * zeroReserveLocalDeficit v i) := by
  have h1 := nuclearTrace_partialTrace_bound_of_trace_zero (ptrace₁ (ketBra u v))
    (zeroReserveTransition_site1_trace_zero u v huv)
  have h2 := nuclearTrace_partialTrace_bound_of_trace_zero (ptrace₂ (ketBra u v))
    (zeroReserveTransition_site2_trace_zero u v huv)
  have h3 := nuclearTrace_partialTrace_bound_of_trace_zero (ptrace₃ (ketBra u v))
    (zeroReserveTransition_site3_trace_zero u v huv)
  rw [(zeroReserveTransition_site1_traces _).1, (zeroReserveTransition_site1_traces _).2] at h1
  rw [(zeroReserveTransition_site2_traces _).1, (zeroReserveTransition_site2_traces _).2] at h2
  rw [(zeroReserveTransition_site3_traces _).1, (zeroReserveTransition_site3_traces _).2] at h3
  have e1 := zeroReserveTransition_site1 u v hu hv
  have e2 := zeroReserveTransition_site2 u v hu hv
  have e3 := zeroReserveTransition_site3 u v hu hv
  fin_cases i
  · change frobSq (ptrace₁₂ (ketBra u v)) + frobSq (ptrace₁₃ (ketBra u v)) -
      frobSq (ptrace₁ (ketBra u v)) ≤ _
    change _ ≤ Real.sqrt ((1 - frobSq (ptrace₂₃ (ketBra u u))) *
      (1 - frobSq (ptrace₂₃ (ketBra v v))))
    linarith
  · change frobSq (ptrace₁₂ (ketBra u v)) + frobSq (ptrace₂₃ (ketBra u v)) -
      frobSq (ptrace₂ (ketBra u v)) ≤ _
    change _ ≤ Real.sqrt ((1 - frobSq (ptrace₁₃ (ketBra u u))) *
      (1 - frobSq (ptrace₁₃ (ketBra v v))))
    linarith
  · change frobSq (ptrace₁₃ (ketBra u v)) + frobSq (ptrace₂₃ (ketBra u v)) -
      frobSq (ptrace₃ (ketBra u v)) ≤ _
    change _ ≤ Real.sqrt ((1 - frobSq (ptrace₁₂ (ketBra u u))) *
      (1 - frobSq (ptrace₁₂ (ketBra v v))))
    linarith

/-- Wu--Zou's sharp Plücker cross bound in the manuscript's literal A/B contractions. -/
theorem zeroReserve_sharp_cross_bound (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0) :
    2 * invB (ketBra u v) - invA (ketBra u v) ≤
      Real.sqrt (zeroReserveLocalEntropy u * zeroReserveLocalEntropy v) := by
  calc
    2 * invB (ketBra u v) - invA (ketBra u v) =
        ∑ i : Fin 3, zeroReserveCutCross u v i := (zeroReserveCutCross_sum u v).symm
    _ ≤ ∑ i : Fin 3, Real.sqrt (zeroReserveLocalDeficit u i * zeroReserveLocalDeficit v i) :=
      Finset.sum_le_sum (fun i _ => zeroReserveCutCross_le u v hu hv huv i)
    _ ≤ Real.sqrt ((∑ i : Fin 3, zeroReserveLocalDeficit u i) *
        (∑ i : Fin 3, zeroReserveLocalDeficit v i)) :=
      zeroReserve_sum_sqrt_mul_le _ _ (zeroReserveLocalDeficit_nonneg u hu)
        (zeroReserveLocalDeficit_nonneg v hv)
    _ = Real.sqrt (zeroReserveLocalEntropy u * zeroReserveLocalEntropy v) := by
      rw [zeroReserveLocalDeficit_sum, zeroReserveLocalDeficit_sum]

/-- The reserve dominates the exact weighted entropy square for nonnegative spectral coefficients. -/
theorem zeroReserve_two_ray_square_bound (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    (lam * Real.sqrt (zeroReserveLocalEntropy u) - mu * Real.sqrt (zeroReserveLocalEntropy v)) ^ 2 ≤
      4 * zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) := by
  rw [zeroReserve_two_ray_square_identity u v hu hv huv]
  have hgap := sub_nonneg.mpr (zeroReserve_sharp_cross_bound u v hu hv huv)
  have hc : 0 ≤ 2 * lam * mu := mul_nonneg (mul_nonneg (by norm_num) hlam) hmu
  linarith [mul_nonneg hc hgap]

/-- Nonnegative two-ray spectral combinations have nonnegative actual reserve. -/
theorem zeroReserve_two_ray_nonneg (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    0 ≤ zeroReserve ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) := by
  have h := zeroReserve_two_ray_square_bound u v hu hv huv lam mu hlam hmu
  nlinarith [sq_nonneg (lam * Real.sqrt (zeroReserveLocalEntropy u) -
    mu * Real.sqrt (zeroReserveLocalEntropy v))]

/-- The endpoint form consequently retains the exact positive spectral-gap lower bound. -/
theorem zeroReserve_two_ray_endpoint_bound (u v : a × b × c → ℂ)
    (hu : vecNormSq u = 1) (hv : vecNormSq v = 1) (huv : braket u v = 0)
    (lam mu : ℝ) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    (lam - mu) ^ 2 / 8 ≤ endpointEnergy ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) := by
  have hn : invN ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = lam ^ 2 + mu ^ 2 := by
    simp only [invN, zeroReserve_frobSq_real_mix, frobSq_ketBra_vecNormSq,
      hsInner_ketBra, hu, hv, huv, map_zero, zero_mul, Complex.zero_re,
      mul_one, mul_zero, add_zero]
  have ht : invT ((lam : ℂ) • ketBra u u + (mu : ℂ) • ketBra v v) = (lam + mu) ^ 2 := by
    simp only [invT, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
      trace_ketBra, braket_self, hu, hv, Complex.ofReal_one, mul_one,
      ← Complex.ofReal_add, Complex.normSq_ofReal]
    ring
  have h := zeroReserve_two_ray_nonneg u v hu hv huv lam mu hlam hmu
  rw [zeroReserve_eq_endpoint, hn, ht] at h
  nlinarith

/-- The actual positive rank-at-most-two source has nonnegative reserve.
The ambient cardinality only allows a second spectral ray with zero weight. -/
theorem zeroReserve_posSemidef_rank_le_two
    (P : Matrix (a × b × c) (a × b × c) ℂ) (hP : P.PosSemidef)
    (hr : P.rank ≤ 2) (hn : 2 ≤ Fintype.card (a × b × c)) :
    0 ≤ zeroReserve P := by
  obtain ⟨u, v, lam, mu, hu, hv, huv, hlam, hmu, hdecomp⟩ :=
    posSemidef_rank_le_two_exists_rays P hP hr hn
  rw [hdecomp]
  exact zeroReserve_two_ray_nonneg u v hu hv huv lam mu hlam hmu

/-- The reserve sign on the literal three-qutrit physical space, including
rank zero and rank one, has no spectral-decomposition premise. -/
theorem zeroReserve_qutrit_posSemidef_rank_le_two
    (P : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (hP : P.PosSemidef) (hr : P.rank ≤ 2) : 0 ≤ zeroReserve P :=
  zeroReserve_posSemidef_rank_le_two P hP hr (by decide)

end ThreeCopyQutritWerner
