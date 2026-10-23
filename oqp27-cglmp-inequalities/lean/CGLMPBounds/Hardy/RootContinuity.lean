module

public import CGLMPBounds.Hardy.RootEnumeration
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Sequences

@[expose] public section


/-!
# Continuity of symmetric sums over all characteristic roots

A chosen enumeration need not be continuous. Every sequence of bounded root
vectors has a convergent subsequence; evaluation of the monic factorization
identifies its limit, retaining every algebraic multiplicity. This gives
continuity of a sum of any continuous real function over the literal root
multiset, for arbitrary complex matrices including defective matrices.
-/

namespace CGLMPBounds.Hardy
noncomputable section
open Filter Polynomial
open scoped Topology Matrix.Norms.Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma continuous_charpoly_eval (z : ℂ) :
    Continuous (fun A : Matrix ι ι ℂ => A.charpoly.eval z) := by
  simp_rw [Matrix.eval_charpoly]
  exact (continuous_const.sub continuous_id).matrix_det

lemma continuous_rootVectorPolynomial_eval (z : ℂ) :
    Continuous (fun v : ι → ℂ => (rootVectorPolynomial v).eval z) := by
  simp_rw [rootVectorPolynomial_eval]
  exact continuous_finsetProd _ fun i _ => continuous_const.sub (continuous_apply i)

lemma norm_charpolyRootVector_le (A : Matrix ι ι ℂ) :
    ‖charpolyRootVector A‖ ≤ ‖A‖ * ‖(1 : Matrix ι ι ℂ)‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro i
  exact spectrum.norm_le_norm_mul_of_mem
    (Matrix.mem_spectrum_of_isRoot_charpoly
      (Polynomial.isRoot_of_mem_roots (charpolyRootVector_mem A i)))

/-- A convergent enumeration still factors the limiting characteristic polynomial.
This is a multiplicity statement, stronger than membership of each limit in the
limiting spectrum. -/
theorem charpoly_eq_rootVectorPolynomial_of_tendsto
    {A : ℕ → Matrix ι ι ℂ} {B : Matrix ι ι ℂ} {v : ι → ℂ}
    (hA : Tendsto A atTop (𝓝 B))
    (hv : Tendsto (fun n => charpolyRootVector (A n)) atTop (𝓝 v)) :
    B.charpoly = rootVectorPolynomial v := by
  apply Polynomial.funext
  intro z
  have hleft := ((continuous_charpoly_eval (ι := ι) z).tendsto B).comp hA
  have hright := ((continuous_rootVectorPolynomial_eval (ι := ι) z).tendsto v).comp hv
  have hright' : Tendsto (fun n => (A n).charpoly.eval z) atTop
      (𝓝 ((rootVectorPolynomial v).eval z)) := by
    simpa only [Function.comp_def, ← charpoly_eq_rootVectorPolynomial] using hright
  exact tendsto_nhds_unique hleft hright'

/-- Compactness of enumerated roots for a convergent sequence of arbitrary
complex matrices. The limit enumeration retains the exact characteristic polynomial. -/
theorem exists_rootVector_subseq_of_tendsto
    {A : ℕ → Matrix ι ι ℂ} {B : Matrix ι ι ℂ}
    (hA : Tendsto A atTop (𝓝 B)) :
    ∃ (v : ι → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n => charpolyRootVector (A (φ n))) atTop (𝓝 v) ∧
      B.charpoly = rootVectorPolynomial v := by
  obtain ⟨R, hR, hbound⟩ :=
    (Metric.isBounded_range_of_tendsto A hA).exists_pos_norm_le
  let r := R * ‖(1 : Matrix ι ι ℂ)‖
  have hb : ∀ n, charpolyRootVector (A n) ∈ Metric.closedBall (0 : ι → ℂ) r := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_charpolyRootVector_le (A n)).trans
      (mul_le_mul_of_nonneg_right (hbound (A n) ⟨n, rfl⟩) (norm_nonneg _))
  obtain ⟨v, _, φ, hφ, hv⟩ := (isCompact_closedBall (0 : ι → ℂ) r).tendsto_subseq hb
  refine ⟨v, φ, hφ, hv, ?_⟩
  exact charpoly_eq_rootVectorPolynomial_of_tendsto (hA.comp hφ.tendsto_atTop) hv

/-- A continuous observable summed over every characteristic root, counting
algebraic multiplicities, varies continuously with an arbitrary complex matrix. -/
theorem continuous_charpoly_root_sum (f : ℂ → ℝ) (hf : Continuous f) :
    Continuous (fun A : Matrix ι ι ℂ => (A.charpoly.roots.map f).sum) := by
  letI : FirstCountableTopology (Matrix ι ι ℂ) :=
    inferInstanceAs (FirstCountableTopology (ι → ι → ℂ))
  letI : SequentialSpace (Matrix ι ι ℂ) :=
    FrechetUrysohnSpace.to_sequentialSpace
  apply continuous_iff_seqContinuous.mpr
  intro A B hA
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨v, φ, hφ, hv, hfactor⟩ := exists_rootVector_subseq_of_tendsto (hA.comp hns)
  refine ⟨φ, ?_⟩
  have hsum : Continuous (fun w : ι → ℂ => ∑ i, f (w i)) :=
    continuous_finsetSum _ fun i _ => hf.comp (continuous_apply i)
  have hlim := (hsum.tendsto v).comp hv
  change Tendsto (fun n => ((A (ns (φ n))).charpoly.roots.map f).sum) atTop
    (𝓝 ((B.charpoly.roots.map f).sum))
  rw [root_sum_eq_vector_sum_of_factorization B v hfactor f]
  simpa only [Function.comp_def, charpoly_root_sum_eq_vector_sum] using hlim

end
end CGLMPBounds.Hardy
