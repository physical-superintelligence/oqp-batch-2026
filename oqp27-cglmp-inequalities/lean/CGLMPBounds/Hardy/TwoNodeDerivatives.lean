module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

@[expose] public section


/-!
# The exact derivative calculation behind source C.9

For `q >= 1`, the `n`th derivative of `z^(n+q-1)/(z-b)^q` is
`q.ascFactorial n * (-b)^n * z^(q-1)/(z-b)^(q+n)`.
The proof uses the two surviving terms in Leibniz's rule for multiplication
by `z`, a local derivative congruence, and rational algebra. No residue or
coefficient identity is assumed. The local statement excludes `0,b`; this
contains the evaluation point `a > 0 > b` needed by source C.9.
-/

open Complex Filter Set
open scoped Topology

namespace CGLMPBounds.Hardy
noncomputable section

def twoNodeRegularFactor (n q : ℕ) (b z : ℂ) : ℂ :=
  z ^ (n + q - 1) / (z - b) ^ q

def twoNodeDerivativeValue (n q : ℕ) (b z : ℂ) : ℂ :=
  (q.ascFactorial n : ℂ) * (-b) ^ n * z ^ (q - 1) / (z - b) ^ (q + n)

lemma analyticAt_twoNodeRegularFactor (n q : ℕ) (b : ℂ) {z : ℂ} (hz : z ≠ b) :
    AnalyticAt ℂ (twoNodeRegularFactor n q b) z := by
  exact (analyticAt_id.pow (n + q - 1)).div
    ((analyticAt_id.sub analyticAt_const).pow q) (pow_ne_zero q (sub_ne_zero.mpr hz))

/-- Leibniz's formula for multiplication by the identity function has only
two nonzero terms. -/
lemma twoNode_iteratedDeriv_mul_id (n : ℕ) {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    iteratedDeriv (n + 1) (fun w => w * f w) z =
      z * iteratedDeriv (n + 1) f z + ((n + 1 : ℕ) : ℂ) * iteratedDeriv n f z := by
  let T : ℕ → ℂ := fun i => ((n + 1).choose i : ℂ) *
    iteratedDeriv i (fun w : ℂ => w) z * iteratedDeriv (n + 1 - i) f z
  have h := iteratedDeriv_fun_mul (n := n + 1) (f := fun w : ℂ => w) (g := f)
    (by fun_prop) hf.contDiffAt
  change iteratedDeriv (n + 1) (fun w => w * f w) z =
    ∑ i ∈ Finset.range (n + 1 + 1), T i at h
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
  have htail : (∑ i ∈ Finset.range n, T (i + 1 + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [T, iteratedDeriv_fun_id, show i + 1 + 1 ≠ 0 by omega,
      show i + 1 + 1 ≠ 1 by omega]
  rw [htail] at h
  simpa [T, iteratedDeriv_fun_id, Nat.cast_add, Nat.cast_one, add_comm] using h

/-- Logarithmic form of the ordinary power rule, proved by separating the
zero exponent. The only division introduced is by the actual nonzero value. -/
lemma twoNode_hasDerivAt_power_log (m : ℕ) {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' z) (hzero : f z ≠ 0) :
    HasDerivAt (fun w => f w ^ m) ((m : ℂ) * f z ^ m / f z * f') z := by
  convert hf.pow m using 1
  cases m with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ]
    field_simp [hzero]
    <;> ring

lemma twoNode_hasDerivAt_power_quotient (m k : ℕ) (b : ℂ) {z : ℂ}
    (hz0 : z ≠ 0) (hzb : z ≠ b) :
    HasDerivAt (fun w => w ^ m / (w - b) ^ k)
      (((m : ℂ) / z - (k : ℂ) / (z - b)) * (z ^ m / (z - b) ^ k)) z := by
  have hnum := twoNode_hasDerivAt_power_log m (hasDerivAt_id z) hz0
  have hden := twoNode_hasDerivAt_power_log k ((hasDerivAt_id z).sub_const b)
    (sub_ne_zero.mpr hzb)
  convert hnum.div hden (pow_ne_zero k (sub_ne_zero.mpr hzb)) using 1
  · rfl
  · dsimp only [id_eq]
    field_simp [hz0, sub_ne_zero.mpr hzb]
    <;> ring

/-- Euler cancellation in the induction step. -/
lemma twoNodeDerivativeValue_euler (n q : ℕ) (hq : 1 ≤ q) (b : ℂ) {z : ℂ}
    (hz0 : z ≠ 0) (hzb : z ≠ b) :
    z * deriv (twoNodeDerivativeValue n q b) z +
        ((n + 1 : ℕ) : ℂ) * twoNodeDerivativeValue n q b z =
      twoNodeDerivativeValue (n + 1) q b z := by
  let C : ℂ := (q.ascFactorial n : ℂ) * (-b) ^ n
  let V : ℂ := z ^ (q - 1) / (z - b) ^ (q + n)
  let L : ℂ := ((q - 1 : ℕ) : ℂ) / z - ((q + n : ℕ) : ℂ) / (z - b)
  have hd : HasDerivAt (twoNodeDerivativeValue n q b) (C * (L * V)) z := by
    have hfun : twoNodeDerivativeValue n q b =
        fun w => C * (w ^ (q - 1) / (w - b) ^ (q + n)) := by
      funext w
      simp only [twoNodeDerivativeValue, C, mul_div_assoc]
    rw [hfun]
    exact (twoNode_hasDerivAt_power_quotient (q - 1) (q + n) b hz0 hzb).const_mul C
  have heuler : z * L + ((n + 1 : ℕ) : ℂ) =
      ((q + n : ℕ) : ℂ) * (-b) / (z - b) := by
    dsimp only [L]
    rw [Nat.cast_sub hq]
    push_cast
    field_simp [hz0, sub_ne_zero.mpr hzb]
    <;> ring
  have hval : twoNodeDerivativeValue n q b z = C * V := by
    simp only [twoNodeDerivativeValue, C, V, mul_div_assoc]
  rw [hd.deriv, hval]
  calc
    _ = (z * L + ((n + 1 : ℕ) : ℂ)) * C * V := by ring
    _ = (((q + n : ℕ) : ℂ) * (-b) / (z - b)) * C * V := by rw [heuler]
    _ = twoNodeDerivativeValue (n + 1) q b z := by
      simp only [twoNodeDerivativeValue, C, V, Nat.ascFactorial_succ, Nat.cast_mul,
        Nat.add_succ, pow_succ]
      field_simp [sub_ne_zero.mpr hzb]
      <;> ring

lemma twoNodeRegularFactor_succ (n q : ℕ) (hq : 1 ≤ q) (b : ℂ) :
    twoNodeRegularFactor (n + 1) q b = fun z => z * twoNodeRegularFactor n q b z := by
  funext z
  unfold twoNodeRegularFactor
  rw [show n + 1 + q - 1 = (n + q - 1) + 1 by omega, pow_succ]
  ring

/-- The exact derivative value, obtained from a proved local identity at each
induction stage. Neither a residue nor a Taylor coefficient is an assumption. -/
theorem iteratedDeriv_twoNodeRegularFactor (n q : ℕ) (hq : 1 ≤ q) (b : ℂ)
    {z : ℂ} (hz0 : z ≠ 0) (hzb : z ≠ b) :
    iteratedDeriv n (twoNodeRegularFactor n q b) z = twoNodeDerivativeValue n q b z := by
  induction n generalizing z with
  | zero => simp [twoNodeRegularFactor, twoNodeDerivativeValue]
  | succ n ih =>
    have heq : iteratedDeriv n (twoNodeRegularFactor n q b) =ᶠ[𝓝 z]
        twoNodeDerivativeValue n q b := by
      filter_upwards [eventually_ne_nhds hz0, eventually_ne_nhds hzb] with w hw0 hwb
      exact ih hw0 hwb
    have hnext : iteratedDeriv (n + 1) (twoNodeRegularFactor n q b) z =
        deriv (twoNodeDerivativeValue n q b) z := by
      rw [iteratedDeriv_succ]
      exact heq.deriv_eq
    rw [twoNodeRegularFactor_succ n q hq b,
      twoNode_iteratedDeriv_mul_id n (analyticAt_twoNodeRegularFactor n q b hzb),
      hnext, ih hz0 hzb]
    exact twoNodeDerivativeValue_euler n q hq b hz0 hzb

end
end CGLMPBounds.Hardy
