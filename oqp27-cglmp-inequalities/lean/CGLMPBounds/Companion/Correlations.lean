module

public import CGLMPBounds.Companion.FourierTrace
public import CGLMPBounds.Companion.ScalarAssembly
public import CGLMPBounds.Companion.ClockCost

@[expose] public section


/-!
# Normalized unitary correlations and the phase-scaled frequency blocks

The diagonal correlation is one only when the multiplicity space is nonempty.
The adjoint symmetry and the phase-scaled trace formula keep the source convention
`z_jk=τ(V_j†V_k)` explicit before assembling the Bell-gap identity.
-/

open Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace CGLMPBounds.Companion
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

def unitaryCorrelation (V : α → Matrix.unitaryGroup ι ℂ) (j k : α) : ℂ :=
  Matrix.trace ((V j : Matrix ι ι ℂ)ᴴ * (V k : Matrix ι ι ℂ)) /
    (Fintype.card ι : ℂ)

lemma unitaryCorrelation_diagonal [Nonempty ι]
    (V : α → Matrix.unitaryGroup ι ℂ) (j : α) : unitaryCorrelation V j j = 1 := by
  unfold unitaryCorrelation
  have hv : (V j : Matrix ι ι ℂ)ᴴ * (V j : Matrix ι ι ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (V j).property.1
  rw [hv, Matrix.trace_one]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

lemma unitaryCorrelation_star (V : α → Matrix.unitaryGroup ι ℂ) (j k : α) :
    unitaryCorrelation V k j = star (unitaryCorrelation V j k) := by
  unfold unitaryCorrelation
  rw [star_div₀, star_natCast, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

variable {d : ℕ} [NeZero d]

lemma sourcePhase_star (j : Fin d) : star (sourcePhase j) = (sourcePhase j)⁻¹ :=
  eq_inv_of_mul_eq_one_left (sourcePhase_star_mul j)

lemma outcomeRoot_etaD (j : Fin d) : outcomeRoot j = (etaD d ^ 4) ^ j.val := by
  rw [← sourcePhase_fourth, sourcePhase, ← pow_mul, ← pow_mul, Nat.mul_comm]

lemma outcomeRoot_star (j : Fin d) :
    star (outcomeRoot j) = (etaD d ^ 4)⁻¹ ^ j.val := by
  rw [← sourcePhase_fourth, star_pow, sourcePhase_star, sourcePhase,
    inv_pow, ← pow_mul, Nat.mul_comm, pow_mul, ← inv_pow]

lemma phase_scaled_cross_trace (V : Fin d → Matrix.unitaryGroup ι ℂ) (j k : Fin d) :
    Matrix.trace ((sourcePhase j • (V j : Matrix ι ι ℂ)) *
        (sourcePhase k • (V k : Matrix ι ι ℂ))ᴴ) / (Fintype.card ι : ℂ) =
      (etaD d ^ j.val * (etaD d)⁻¹ ^ k.val) * unitaryCorrelation V k j := by
  rw [Matrix.conjTranspose_smul, smul_mul_smul_comm, Matrix.trace_smul, smul_eq_mul,
    sourcePhase_star, sourcePhase, sourcePhase, inv_pow]
  rw [Matrix.trace_mul_comm (V j : Matrix ι ι ℂ) (V k : Matrix ι ι ℂ)ᴴ]
  exact mul_div_assoc _ _ _

lemma val_finEquiv (j : Fin d) : ((ZMod.finEquiv d) j).val = j.val := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d => rfl

/-- Replace the complete residue system by the exact range used in weighted geometric sums. -/
lemma sum_zmod_val (f : ℕ → ℂ) :
    (∑ r : ZMod d, f r.val) = ∑ r ∈ Finset.range d, f r := by
  have h : (∑ r : Fin d, f r.val) = ∑ r : ZMod d, f r.val := by
    exact Fintype.sum_equiv (ZMod.finEquiv d).toEquiv _ _
      (fun r => congrArg f (val_finEquiv r).symm)
  rw [← h, Fin.sum_univ_eq_sum_range]

/-- Extend a finite tuple to naturals only for use under bounded `range d` sums. -/
def extendUnitary (V : Fin d → Matrix.unitaryGroup ι ℂ) (j : ℕ) : Matrix.unitaryGroup ι ℂ :=
  if hj : j < d then V ⟨j, hj⟩ else 1

lemma extendUnitary_fin (V : Fin d → Matrix.unitaryGroup ι ℂ) (j : Fin d) :
    extendUnitary V j.val = V j := by
  simp [extendUnitary, j.isLt]

lemma finite_correlation_scalar_formula [Nonempty ι]
    (V : Fin d → Matrix.unitaryGroup ι ℂ) :
    ((∑ j ∈ Finset.range d, ∑ k ∈ Finset.range d,
        weightedKernel d j k * unitaryCorrelation (extendUnitary V) k j) / (d : ℂ) ^ 2) =
      ((((d : ℝ) - 1) / 2 - (1 / (2 * (d : ℝ))) *
        ∑ k ∈ Finset.range d, ∑ j ∈ Finset.range k,
          pairedCorrelation d j k (unitaryCorrelation (extendUnitary V) j k) : ℝ) : ℂ) := by
  apply normalized_weightedKernel_sum d (NeZero.ne d)
  · intro j _
    exact unitaryCorrelation_diagonal _ j
  · intro j k _ _
    exact unitaryCorrelation_star _ j k

lemma sum_residue_frequency_swap (f : ZMod d → Fin d → Fin d → ℂ) :
    (∑ r, ∑ j, ∑ k, f r j k) = ∑ j, ∑ k, ∑ r, f r j k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

lemma normalized_frequency_trace_sum (V : Fin d → Matrix.unitaryGroup ι ℂ) :
    ((∑ r : ZMod d, (r.val : ℂ) *
        ∑ j, ∑ k, (outcomeRoot j * star (outcomeRoot k)) ^ r.val *
          Matrix.trace ((sourcePhase j • (V j : Matrix ι ι ℂ)) *
            (sourcePhase k • (V k : Matrix ι ι ℂ))ᴴ)) / (Fintype.card ι : ℂ)) =
      ∑ j : Fin d, ∑ k : Fin d, weightedKernel d j.val k.val * unitaryCorrelation V k j := by
  simp only [Finset.mul_sum, Finset.sum_div, mul_div_assoc, phase_scaled_cross_trace]
  simp_rw [outcomeRoot_star, outcomeRoot_etaD]
  rw [sum_residue_frequency_swap]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_zmod_val (fun r : ℕ => (r : ℂ) *
    (((etaD d ^ 4) ^ j.val * (etaD d ^ 4)⁻¹ ^ k.val) ^ r *
      (etaD d ^ j.val * (etaD d)⁻¹ ^ k.val * unitaryCorrelation V k j)))]
  simp only [weightedKernel, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The normalized trace cost of the actual phase-scaled Fourier blocks equals the kernel sum. -/
theorem normalized_trace_to_kernels (V : Fin d → Matrix.unitaryGroup ι ℂ) :
    ((∑ a : ZMod d, ∑ b : ZMod d, ((a - b).val : ℂ) *
        Matrix.trace (outcomeProjector a *
          blockFourierOperator (fun j => sourcePhase j • (V j : Matrix ι ι ℂ)) *
          outcomeProjector b *
          (blockFourierOperator (fun j => sourcePhase j • (V j : Matrix ι ι ℂ)))ᴴ)) /
      ((d : ℂ) * (Fintype.card ι : ℂ))) =
      (∑ j : Fin d, ∑ k : Fin d, weightedKernel d j.val k.val * unitaryCorrelation V k j) /
        (d : ℂ) ^ 2 := by
  rw [normalized_weighted_trace_blockFourierOperator,
    mul_comm ((d : ℂ) ^ 2) (Fintype.card ι : ℂ), ← div_div,
    normalized_frequency_trace_sum]

lemma finite_kernel_sum_eq_range (V : Fin d → Matrix.unitaryGroup ι ℂ) :
    (∑ j : Fin d, ∑ k : Fin d, weightedKernel d j.val k.val * unitaryCorrelation V k j) =
      ∑ j ∈ Finset.range d, ∑ k ∈ Finset.range d,
        weightedKernel d j k * unitaryCorrelation (extendUnitary V) k j := by
  calc
    _ = ∑ j : Fin d, ∑ k : Fin d, weightedKernel d j.val k.val *
        unitaryCorrelation (extendUnitary V) k.val j.val := by
      simp only [unitaryCorrelation, extendUnitary_fin]
    _ = ∑ j ∈ Finset.range d, ∑ k : Fin d, weightedKernel d j k.val *
        unitaryCorrelation (extendUnitary V) k.val j :=
      Fin.sum_univ_eq_sum_range (fun j : ℕ => ∑ k : Fin d,
        weightedKernel d j k.val * unitaryCorrelation (extendUnitary V) k.val j) d
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact Fin.sum_univ_eq_sum_range (fun k : ℕ =>
        weightedKernel d j k * unitaryCorrelation (extendUnitary V) k j) d

/-- The source's one-edge formula for an actual unitary tuple, with its full matrix trace input. -/
theorem unitary_tuple_one_edge_formula [Nonempty ι]
    (V : Fin d → Matrix.unitaryGroup ι ℂ) :
    ((∑ a : ZMod d, ∑ b : ZMod d, ((a - b).val : ℂ) *
        Matrix.trace (outcomeProjector a *
          blockFourierOperator (fun j => sourcePhase j • (V j : Matrix ι ι ℂ)) *
          outcomeProjector b *
          (blockFourierOperator (fun j => sourcePhase j • (V j : Matrix ι ι ℂ)))ᴴ)) /
      ((d : ℂ) * (Fintype.card ι : ℂ))) =
      ((((d : ℝ) - 1) / 2 - (1 / (2 * (d : ℝ))) *
        ∑ k ∈ Finset.range d, ∑ j ∈ Finset.range k,
          pairedCorrelation d j k (unitaryCorrelation (extendUnitary V) j k) : ℝ) : ℂ) := by
  rw [normalized_trace_to_kernels, finite_kernel_sum_eq_range]
  exact finite_correlation_scalar_formula V

lemma re_normalized_trace_cost (X : Matrix (ZMod d × ι) (ZMod d × ι) ℂ) :
    (((∑ a : ZMod d, ∑ b : ZMod d, ((a - b).val : ℂ) *
        Matrix.trace (outcomeProjector a * X * outcomeProjector b * Xᴴ)) /
      ((d : ℂ) * (Fintype.card ι : ℂ))).re) =
      outcomeCost outcomeProjector (fun b => X * outcomeProjector b * Xᴴ) := by
  simp only [outcomeCost, meanTraceReal, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
    Complex.div_ofReal_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Fintype.card_prod, ZMod.card, Nat.cast_mul,
    Finset.sum_div, mul_div_assoc, Matrix.mul_assoc]

/-- The real one-edge cost formula, ready to compare with the original `S_d/4`. -/
theorem unitary_tuple_outcomeCost [Nonempty ι] (V : Fin d → Matrix.unitaryGroup ι ℂ) :
    outcomeCost outcomeProjector
        (fun b => blockFourierOperator (fun j => sourcePhase j • (V j : Matrix ι ι ℂ)) *
          outcomeProjector b *
          (blockFourierOperator (fun j => sourcePhase j • (V j : Matrix ι ι ℂ)))ᴴ) =
      ((d : ℝ) - 1) / 2 - (1 / (2 * (d : ℝ))) *
        ∑ k ∈ Finset.range d, ∑ j ∈ Finset.range k,
          pairedCorrelation d j k (unitaryCorrelation (extendUnitary V) j k) := by
  have h := congrArg Complex.re (unitary_tuple_one_edge_formula V)
  simpa only [re_normalized_trace_cost, Complex.ofReal_re] using h

end
end CGLMPBounds.Companion
