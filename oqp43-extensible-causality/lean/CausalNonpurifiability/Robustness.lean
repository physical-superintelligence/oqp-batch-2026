module

public import CausalNonpurifiability.Definitions.BallCore
public import CausalNonpurifiability.Certificates.Witness
public import CausalNonpurifiability.Statement
public import CausalNonpurifiability.Linear.Positive

@[expose] public section


/-!
# `CausalNonpurifiability.Robustness`

The closed relative ball of `thm:main` (ii) / `sec:ball`, without extensible causality
(the part independent of the rectangle interface):

* `InBall D H` — `eq:ball` as PSD bounds: `H ∈ L_V`, `Tr H = 0`,
  `r·I + H ≥ 0`, `r·I - H ≥ 0` with `r = ballRadius D = 1/(300 m n)`. For Hermitian `H` this is
  `‖H‖_∞ ≤ r`; the equivalence with `‖Matrix.toEuclideanCLM H‖ ≤ r` is a separate later lemma
  (not attempted here).
* `WcC D = toC (Wc …)` — the center `eq:centers`; `wc_valid`, `wc_psd`.
* `ball_lower_bound`, `ball_posDef` — `W_c + H ≥ I/(150 m n) > 0` (`eq:ball-fullrank`);
  `ball_valid` (`eq:valid`).
* `Splus`, `Sminus` — the rational split `S_0 = S_+ - S_-`, `S_± ≥ 0`,
  `Tr(S_+ + S_-) = 4(n + 14)` (rational alternative to `eq:witness-size`:
  nonnegative diagonal kept, each off-diagonal `±3` split with `(1, ±1)` and coefficient `3/2`).
* `abs_re_trace_S0_mul_le` — `|Re Tr(S_0 H)| ≤ 4(n+14)/(300 m n) ≤ 4/75` on the ball
  (the manuscript's `√10/75 ≈ 0.0422` is sharper; ours is `4/75 ≈ 0.0533`).
* `trace_S0_mul_Wc` — `Tr(S_0 W_c) = -99/500 + (n+8)/(25 m n) ≤ -49/500` (`eq:center-margin`).
* `ball_witness_negative` — `Re Tr(S_0 (W_c + H)) ≤ -49/500 + 4/75 = -67/1500 < 0`
  (`eq:ball-negative`, rational form) and `ball_not_causallySeparable`, `ball_kernel`.

Also: `genLV_add`, `genLV_smul`, `genLV_one` — the process space `L_V` is a real subspace
containing the identity (`sec:ball`: "the process equations ... are preserved").
-/

set_option autoImplicit false

namespace CausalNonpurifiability

open Matrix
open scoped Kronecker ComplexOrder

/-! ### Algebra of the homogeneous process space (`eq:LV`) -/

section GenLVAlgebra
variable {AI AO BI BO : Type} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
  [DecidableEq AI] [DecidableEq AO] [DecidableEq BI] [DecidableEq BO]

theorem genLV_add {W W' : Op (LabIdx AI AO BI BO)} (h : GenLV W) (h' : GenLV W') :
    GenLV (W + W') := by
  obtain ⟨hH, ha, hb, hc⟩ := h
  obtain ⟨hH', ha', hb', hc'⟩ := h'
  refine ⟨hH.add hH', ?_, ?_, ?_⟩
  · have e : R_BIBO (W + W') - R_AO (R_BIBO (W + W'))
        = (R_BIBO W - R_AO (R_BIBO W)) + (R_BIBO W' - R_AO (R_BIBO W')) := by
      simp only [map_add]; abel
    rw [e, ha, ha', add_zero]
  · have e : R_AIAO (W + W') - R_BO (R_AIAO (W + W'))
        = (R_AIAO W - R_BO (R_AIAO W)) + (R_AIAO W' - R_BO (R_AIAO W')) := by
      simp only [map_add]; abel
    rw [e, hb, hb', add_zero]
  · have e : (W + W') - R_AO (W + W') - R_BO (W + W') + R_AO (R_BO (W + W'))
        = (W - R_AO W - R_BO W + R_AO (R_BO W)) + (W' - R_AO W' - R_BO W' + R_AO (R_BO W')) := by
      simp only [map_add]; abel
    rw [e, hc, hc', add_zero]

theorem genLV_smul {c : ℂ} (hc : IsSelfAdjoint c) {W : Op (LabIdx AI AO BI BO)} (h : GenLV W) :
    GenLV (c • W) := by
  obtain ⟨hH, ha, hb, hc'⟩ := h
  refine ⟨hH.smul hc, ?_, ?_, ?_⟩
  · have e : R_BIBO (c • W) - R_AO (R_BIBO (c • W)) = c • (R_BIBO W - R_AO (R_BIBO W)) := by
      simp only [map_smul, smul_sub]
    rw [e, ha, smul_zero]
  · have e : R_AIAO (c • W) - R_BO (R_AIAO (c • W)) = c • (R_AIAO W - R_BO (R_AIAO W)) := by
      simp only [map_smul, smul_sub]
    rw [e, hb, smul_zero]
  · have e : c • W - R_AO (c • W) - R_BO (c • W) + R_AO (R_BO (c • W))
        = c • (W - R_AO W - R_BO W + R_AO (R_BO W)) := by
      simp only [map_smul, smul_sub, smul_add]
    rw [e, hc', smul_zero]

theorem genLV_one [Nonempty AI] [Nonempty AO] [Nonempty BI] [Nonempty BO] :
    GenLV (1 : Op (LabIdx AI AO BI BO)) := by
  refine ⟨isHermitian_one, ?_, ?_, ?_⟩
  · rw [R_BIBO_one, R_AO_one, sub_self]
  · rw [R_AIAO_one, R_BO_one, sub_self]
  · rw [R_BO_one, R_AO_one]; abel

theorem genLV_zero : GenLV (0 : Op (LabIdx AI AO BI BO)) := by
  refine ⟨isHermitian_zero, ?_, ?_, ?_⟩ <;> simp

end GenLVAlgebra

lemma isSelfAdjoint_ratCast (q : ℚ) : IsSelfAdjoint (q : ℂ) :=
  isSelfAdjoint_iff.mpr (star_ratCast_complex q)

lemma ratCast_nonneg_complex {q : ℚ} (hq : 0 ≤ q) : (0 : ℂ) ≤ (q : ℂ) := by
  rw [Complex.nonneg_iff]; simp [hq]

lemma ratCast_pos_complex {q : ℚ} (hq : 0 < q) : (0 : ℂ) < (q : ℂ) := by
  rw [Complex.pos_iff]; simp [hq]

/-! ### The center, the radius and the ball (`eq:centers`, `eq:ball`) -/

section Ball
variable (D : Ports)

lemma ballRadius_eq : ballRadius D = ((1 / (300 * D.m * D.n) : ℚ) : ℂ) := by
  rw [ballRadius]; push_cast; ring

lemma lowerBound_eq : lowerBound D = ((1 / (150 * D.m * D.n) : ℚ) : ℂ) := by
  rw [lowerBound]; push_cast; ring

/-- `ballRadius D` as the cast of the real number `1/(300 m n)`. -/
lemma ballRadius_eq_ofReal : ballRadius D = ((1 / (300 * D.m * D.n) : ℝ) : ℂ) := by
  rw [ballRadius]; push_cast; ring

lemma m_pos_rat : (0 : ℚ) < D.m := by exact_mod_cast D.m_pos
lemma n_pos_rat : (0 : ℚ) < D.n := by exact_mod_cast D.n_pos

lemma ballRadius_nonneg : 0 ≤ ballRadius D := by
  rw [ballRadius_eq]
  exact ratCast_nonneg_complex (by have := m_pos_rat D; have := n_pos_rat D; positivity)

lemma lowerBound_pos : 0 < lowerBound D := by
  rw [lowerBound_eq]
  exact ratCast_pos_complex (by have := m_pos_rat D; have := n_pos_rat D; positivity)

/-- `W_c = (99/100) W_0 + (1/(100 m n)) I` in the complex process space. -/
theorem WcC_eq :
    WcC D = ((99 / 100 : ℚ) : ℂ) • toC (W0 D.m D.d D.n D.e)
      + (1 / (100 * D.m * D.n) : ℂ) • (1 : PMat D) := by
  rw [WcC, Wc, toC_add, toC_smul, toC_smul, toC_smul, toC_one, smul_smul]
  congr 2
  push_cast
  ring

/-- `W_c ∈ L_V` (`eq:LV`). -/
theorem wc_inLV (h : AllPortsGE2 D) : InLV D (WcC D) := by
  rw [WcC, Wc, toC_add, toC_smul, toC_smul, toC_smul, toC_one]
  exact genLV_add (genLV_smul (isSelfAdjoint_ratCast _) (w0_inLV D h))
    (genLV_smul (isSelfAdjoint_ratCast _) (genLV_smul (isSelfAdjoint_ratCast _) genLV_one))

/-- `W_c ≥ 0`. -/
theorem wc_psd : (WcC D).PosSemidef := by
  rw [WcC_eq]
  refine (posSemidef_complex_smul (w0_psd _ _ _ _) (ratCast_nonneg_complex (by norm_num))).add
    (posSemidef_complex_smul PosSemidef.one ?_)
  rw [show (1 / (100 * D.m * D.n) : ℂ) = ((1 / (100 * D.m * D.n) : ℚ) : ℂ) by push_cast; ring]
  exact ratCast_nonneg_complex (by have := m_pos_rat D; have := n_pos_rat D; positivity)

/-- **The center is a valid process** (`eq:valid`). -/
theorem wc_valid (h : AllPortsGE2 D) : Valid D (WcC D) :=
  ⟨wc_inLV D h, wc_psd D, by rw [WcC, trace_toC, trace_Wc h.1 h.2.2.1, Rat.cast_natCast]⟩

variable {D}

/-- `W_c + H - I/(150 m n) = (99/100) W_0 + (r I + H) ≥ 0` (`eq:ball-fullrank`). -/
theorem ball_lower_bound {H : PMat D} (hH : InBall D H) :
    (WcC D + H - lowerBound D • (1 : PMat D)).PosSemidef := by
  have e : WcC D + H - lowerBound D • (1 : PMat D)
      = ((99 / 100 : ℚ) : ℂ) • toC (W0 D.m D.d D.n D.e) + (ballRadius D • (1 : PMat D) + H) := by
    rw [WcC_eq, lowerBound, ballRadius]
    module
  rw [e]
  exact (posSemidef_complex_smul (w0_psd _ _ _ _) (ratCast_nonneg_complex (by norm_num))).add
    hH.2.2.1

/-- **Full rank throughout the closed ball** (`eq:ball-fullrank`). -/
theorem ball_posDef {H : PMat D} (hH : InBall D H) : (WcC D + H).PosDef := by
  have hpos : (lowerBound D • (1 : PMat D)).PosDef := by
    rw [smul_one_eq_diagonal]
    exact PosDef.diagonal fun _ => lowerBound_pos D
  have := Matrix.PosDef.posSemidef_add (ball_lower_bound hH) hpos
  rwa [sub_add_cancel] at this

/-- **Validity throughout the closed ball** (`eq:valid`). -/
theorem ball_valid (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) : Valid D (WcC D + H) :=
  ⟨genLV_add (wc_inLV D h) hH.1, (ball_posDef hH).posSemidef, by
    rw [trace_add, hH.2.1, add_zero, WcC, trace_toC, trace_Wc h.1 h.2.2.1, Rat.cast_natCast]⟩

/-- The center itself lies in the ball (`H = 0`). -/
theorem inBall_zero : InBall D 0 :=
  ⟨genLV_zero, trace_zero _ _, by simpa using posSemidef_complex_smul PosSemidef.one (ballRadius_nonneg D),
    by simpa using posSemidef_complex_smul PosSemidef.one (ballRadius_nonneg D)⟩

end Ball

/-! ### The rational split of the witness -/

section Split
variable {m d n e : ℕ}

/-- `(1, 1, 0, …)` on `B_I`. -/
def wsum (n : ℕ) : Fin n → ℚ := fun i => if i.val = 0 ∨ i.val = 1 then 1 else 0

/-- `(1, -1, 0, …)` on `B_I`. -/
def wdiff (n : ℕ) : Fin n → ℚ := fun i => if i.val = 0 then 1 else if i.val = 1 then -1 else 0

lemma P_add_X_eq : P n + X n = vecMulVec (wsum n) (wsum n) := by
  ext i j
  simp only [P_eq, X_apply, wsum, Matrix.add_apply, diagonal_apply, vecMulVec_apply]
  split_ifs <;> first | omega | norm_num

lemma P_sub_X_eq : P n - X n = vecMulVec (wdiff n) (wdiff n) := by
  ext i j
  simp only [P_eq, X_apply, wdiff, Matrix.sub_apply, diagonal_apply, vecMulVec_apply]
  split_ifs <;> first | omega | norm_num

lemma psd_toC_P (r : ℕ) : (toC (P r)).PosSemidef := by
  rw [P_eq]; exact diagonal_nonneg_sound _ fun i => by split_ifs <;> norm_num

lemma psd_toC_P_add_X : (toC (P n + X n)).PosSemidef := by
  rw [P_add_X_eq]; exact vecMulVec_self_sound _

lemma psd_toC_P_sub_X : (toC (P n - X n)).PosSemidef := by
  rw [P_sub_X_eq]; exact vecMulVec_self_sound _

/-- Off-diagonal split, positive part: `P_1 ⊗ P_d ⊗ [(1,1)(1,1)ᵀ ⊗ |0⟩⟨0| + (1,-1)(1,-1)ᵀ ⊗ |1⟩⟨1|]`. -/
def Gplus (m d n e : ℕ) : Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  kron4 (proj m 1) (P d) (P n + X n) (proj e 0) + kron4 (proj m 1) (P d) (P n - X n) (proj e 1)

/-- Off-diagonal split, negative part. -/
def Gminus (m d n e : ℕ) : Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  kron4 (proj m 1) (P d) (P n - X n) (proj e 0) + kron4 (proj m 1) (P d) (P n + X n) (proj e 1)

/-- `S_+` : the (nonnegative) diagonal part of `S_0` plus `(3/2) G_+`. -/
def Splus (m d n e : ℕ) : Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  kron4 (proj m 1) (P d) (Dw n) (P e) - kron4 (proj m 1) (Z d) (Dw n * Zplus n) (P e)
    + (3 / 2 : ℚ) • Gplus m d n e

/-- `S_-` : `(3/2) G_-`. -/
def Sminus (m d n e : ℕ) : Matrix (Lab m d n e) (Lab m d n e) ℚ := (3 / 2 : ℚ) • Gminus m d n e

/-- `S_0 = S_+ - S_-`. -/
theorem S0_eq_split : S0 m d n e = Splus m d n e - Sminus m d n e := by
  simp only [S0, Splus, Sminus, Gplus, Gminus, kron4_add₃, kron4_sub₃, Z, kron4_sub₄]
  module

/-- The diagonal part of `S_0` in block form (`eq:witness-replacements` blocks with `P_e`). -/
theorem diag_part_eq :
    kron4 (proj m 1) (P d) (Dw n) (P e) - kron4 (proj m 1) (Z d) (Dw n * Zplus n) (P e)
      = kron4 (proj m 1) (proj d 0) ((18 : ℚ) • proj n 1) (P e)
        + kron4 (proj m 1) (proj d 1) ((2 : ℚ) • (1 - proj n 1)) (P e) := by
  rw [← Dw_mul_one_sub_Zplus, ← Dw_mul_one_add_Zplus]
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, kron4_sub₃, kron4_add₃, P, Z,
    kron4_add₂, kron4_sub₂]
  module

lemma two_smul_one_sub_proj_eq :
    (2 : ℚ) • ((1 : Matrix (Fin n) (Fin n) ℚ) - proj n 1)
      = diagonal fun i : Fin n => if i.val = 1 then (0 : ℚ) else 2 := by
  rw [proj_eq, ← diagonal_one, diagonal_sub, ← diagonal_smul]
  congr 1; funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs <;> norm_num

theorem psd_Gplus : (toC (Gplus m d n e)).PosSemidef := by
  rw [Gplus, toC_add]
  exact (psd_toC_kron4 (psd_toC_proj _ _) (psd_toC_P _) psd_toC_P_add_X (psd_toC_proj _ _)).add
    (psd_toC_kron4 (psd_toC_proj _ _) (psd_toC_P _) psd_toC_P_sub_X (psd_toC_proj _ _))

theorem psd_Gminus : (toC (Gminus m d n e)).PosSemidef := by
  rw [Gminus, toC_add]
  exact (psd_toC_kron4 (psd_toC_proj _ _) (psd_toC_P _) psd_toC_P_sub_X (psd_toC_proj _ _)).add
    (psd_toC_kron4 (psd_toC_proj _ _) (psd_toC_P _) psd_toC_P_add_X (psd_toC_proj _ _))

/-- `S_+ ≥ 0`. -/
theorem psd_Splus : (toC (Splus m d n e)).PosSemidef := by
  rw [Splus, diag_part_eq, toC_add, toC_add, toC_smul]
  refine PosSemidef.add (PosSemidef.add ?_ ?_)
    (posSemidef_complex_smul psd_Gplus (ratCast_nonneg_complex (by norm_num)))
  · exact psd_toC_kron4 (psd_toC_proj _ _) (psd_toC_proj _ _) (psd_toC_smul_proj _ _ (by norm_num))
      (psd_toC_P _)
  · refine psd_toC_kron4 (psd_toC_proj _ _) (psd_toC_proj _ _) ?_ (psd_toC_P _)
    rw [two_smul_one_sub_proj_eq]
    exact diagonal_nonneg_sound _ fun i => by split_ifs <;> norm_num

/-- `S_- ≥ 0`. -/
theorem psd_Sminus : (toC (Sminus m d n e)).PosSemidef := by
  rw [Sminus, toC_smul]
  exact posSemidef_complex_smul psd_Gminus (ratCast_nonneg_complex (by norm_num))

/-- `Tr(S_+ + S_-) = 4(n + 14)`: the four distinguished blocks contribute `64`, every extra
`B_I` index `4`. -/
theorem trace_Splus_add_Sminus (hm : 2 ≤ m) (hd : 2 ≤ d) (hn : 2 ≤ n) (he : 2 ≤ e) :
    trace (Splus m d n e + Sminus m d n e) = 4 * (n + 14) := by
  have h1 : trace (proj m 1) = 1 := trace_proj1 hm
  have h0e : trace (proj e 0) = 1 := trace_proj0 he
  have h1e : trace (proj e 1) = 1 := trace_proj1 he
  simp only [Splus, Sminus, Gplus, Gminus, trace_add, trace_sub, trace_smul, trace_kron4, h1, h0e,
    h1e, trace_P hd, trace_P he, trace_P hn, trace_Z hd, trace_Dw hn, trace_X, smul_eq_mul,
    zero_mul, mul_zero, sub_zero, add_zero]
  ring

end Split

/-! ### Pairing bounds on the ball -/

section Pairing
variable (D : Ports)

/-- For rational `S ≥ 0` and `H` in the ball: `-r Tr S ≤ Re Tr(S H) ≤ r Tr S`, `r = 1/(300 m n)`. -/
theorem re_trace_mul_bounds {S : Matrix (Lab D.m D.d D.n D.e) (Lab D.m D.d D.n D.e) ℚ}
    (hS : (toC S).PosSemidef) {H : PMat D} (hH : InBall D H) :
    (trace (toC S * H)).re ≤ (1 / (300 * D.m * D.n) : ℝ) * ((trace S : ℚ) : ℝ) ∧
      -((1 / (300 * D.m * D.n) : ℝ) * ((trace S : ℚ) : ℝ)) ≤ (trace (toC S * H)).re := by
  have h1 := trace_mul_nonneg hS hH.2.2.1
  have h2 := trace_mul_nonneg hS hH.2.2.2
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, trace_add, trace_smul, smul_eq_mul,
    trace_toC, ballRadius_eq, ← Rat.cast_mul] at h1
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, trace_sub, trace_smul, smul_eq_mul,
    trace_toC, ballRadius_eq, ← Rat.cast_mul] at h2
  have h1' := (Complex.nonneg_iff.mp h1).1
  have h2' := (Complex.nonneg_iff.mp h2).1
  rw [Complex.add_re, Complex.ratCast_re] at h1'
  rw [Complex.sub_re, Complex.ratCast_re] at h2'
  push_cast at h1' h2'
  constructor <;> linarith

/-- `|Re Tr(S_0 H)| ≤ 4(n+14)/(300 m n)` on the ball (rational `eq:witness-size` bound). -/
theorem abs_re_trace_S0_mul_le (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    |(trace (toC (S0 D.m D.d D.n D.e) * H)).re| ≤ 4 * (D.n + 14) / (300 * D.m * D.n) := by
  obtain ⟨hp1, hp2⟩ := re_trace_mul_bounds D psd_Splus hH
  obtain ⟨hm1, hm2⟩ := re_trace_mul_bounds D psd_Sminus hH
  have e : (trace (toC (S0 D.m D.d D.n D.e) * H)).re
      = (trace (toC (Splus D.m D.d D.n D.e) * H)).re
        - (trace (toC (Sminus D.m D.d D.n D.e) * H)).re := by
    rw [S0_eq_split, toC_sub, Matrix.sub_mul, trace_sub, Complex.sub_re]
  have ht : ((trace (Splus D.m D.d D.n D.e) : ℚ) : ℝ) + ((trace (Sminus D.m D.d D.n D.e) : ℚ) : ℝ)
      = 4 * (D.n + 14) := by
    have := trace_Splus_add_Sminus h.1 h.2.1 h.2.2.1 h.2.2.2
    rw [trace_add] at this
    exact_mod_cast this
  have key : (1 / (300 * D.m * D.n) : ℝ) * ((trace (Splus D.m D.d D.n D.e) : ℚ) : ℝ)
      + (1 / (300 * D.m * D.n) : ℝ) * ((trace (Sminus D.m D.d D.n D.e) : ℚ) : ℝ)
      = 4 * (D.n + 14) / (300 * D.m * D.n) := by
    rw [← mul_add, ht]; ring
  rw [e, abs_le]
  constructor <;> linarith

/-- `4(n+14)/(300 m n) ≤ 4/75` for `m, n ≥ 2` (tight at `m = n = 2`). -/
theorem margin_bound (hm : 2 ≤ D.m) (hn : 2 ≤ D.n) :
    (4 * (D.n + 14) / (300 * D.m * D.n) : ℝ) ≤ 4 / 75 := by
  have hm' : (2 : ℝ) ≤ D.m := by exact_mod_cast hm
  have hn' : (2 : ℝ) ≤ D.n := by exact_mod_cast hn
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hm') (by linarith : (0 : ℝ) ≤ (D.n : ℝ))]

end Pairing

/-! ### The center margin (`eq:center-margin`) and the ball theorem -/

section Margin
variable {m d n e : ℕ}

/-- `Tr(S_0 W_c) = -99/500 + (n+8)/(25 m n)` (`eq:center-margin`). -/
theorem trace_S0_mul_Wc (hm : 2 ≤ m) (hd : 2 ≤ d) (hn : 2 ≤ n) (he : 2 ≤ e) :
    trace (S0 m d n e * Wc m d n e) = -99 / 500 + (n + 8) / (25 * m * n) := by
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Wc, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
    trace_add, trace_smul, trace_smul, trace_smul, witness_negative hm hd hn he,
    trace_S0 hm hd hn he, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- `Tr(S_0 W_c) ≤ -49/500` for `m, n ≥ 2` (`eq:center-margin`). -/
theorem trace_S0_mul_Wc_le (hm : 2 ≤ m) (hd : 2 ≤ d) (hn : 2 ≤ n) (he : 2 ≤ e) :
    trace (S0 m d n e * Wc m d n e) ≤ -49 / 500 := by
  rw [trace_S0_mul_Wc hm hd hn he]
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hn' : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have key : ((n : ℚ) + 8) / (25 * m * n) ≤ 1 / 10 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm') (by linarith : (0 : ℚ) ≤ (n : ℚ))]
  linarith

end Margin

section BallTheorem
variable (D : Ports)

/-- **The witness is negative throughout the closed ball**:
`Re Tr(S_0 (W_c + H)) ≤ -49/500 + 4/75 = -67/1500 < 0` (`eq:ball-negative`, rational form). -/
theorem ball_witness_negative (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    (trace (toC (S0 D.m D.d D.n D.e) * (WcC D + H))).re ≤ -67 / 1500 := by
  rw [Matrix.mul_add, trace_add, Complex.add_re, WcC, ← Matrix.map_mul, trace_toC,
    Complex.ratCast_re]
  have h1 : ((trace (S0 D.m D.d D.n D.e * Wc D.m D.d D.n D.e) : ℚ) : ℝ) ≤ -49 / 500 := by
    exact_mod_cast trace_S0_mul_Wc_le h.1 h.2.1 h.2.2.1 h.2.2.2
  have h2 := (abs_le.mp (abs_re_trace_S0_mul_le D h hH)).2
  have h3 := margin_bound D h.1 h.2.2.1
  linarith

/-- **No point of the closed ball is causally separable** (`eq:ball-negative` + `sec:witness`). -/
theorem ball_not_causallySeparable (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    ¬ CausallySeparable D (WcC D + H) := by
  intro hCS
  have h0 := (Complex.nonneg_iff.mp (witness_nonneg_on_cs D h.2.1 h.2.2.2 _ hCS)).1
  have h1 := ball_witness_negative D h hH
  linarith

/-- **Closed-ball kernel** (`thm:main` (ii) without extensible causality): every point of the
ball is a valid, full-rank, causally nonseparable process. -/
theorem ball_kernel (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    Valid D (WcC D + H) ∧ (WcC D + H).PosDef ∧ ¬ CausallySeparable D (WcC D + H) :=
  ⟨ball_valid h hH, ball_posDef hH, ball_not_causallySeparable D h hH⟩

/-- The center itself: valid, full rank, not causally separable. -/
theorem wc_kernel (h : AllPortsGE2 D) :
    Valid D (WcC D) ∧ (WcC D).PosDef ∧ ¬ CausallySeparable D (WcC D) := by
  have := ball_kernel D h (inBall_zero (D := D))
  simpa using this

end BallTheorem

/-! ### The exact (spectral) split of the witness (`eq:witness-size`, `eq:center-margin`,
`eq:ball-negative` with the manuscript's radical constants)

On `A_I = |1⟩` and the distinguished two-dimensional output subspaces the `B_I` blocks of `S_0`
are `(0, ±3; ±3, 18)` (eigenvalues `9 ± 3√10`) and `(2, ±3; ±3, 0)` (eigenvalues `1 ± √10`),
each twice; every extra `B_I` basis vector contributes two eigenvalues `2`. The positive and
negative spectral parts are the rank-one matrices `λ₊(B - λ₋I)/(λ₊-λ₋)` and
`-λ₋(λ₊I - B)/(λ₊-λ₋)`; with `r = √10` their entries are rational-linear in `r`:
`A₊ = (3r/20, 9 + 57r/20, ±3(10+3r)/20)`, `A₋ = (3r/20, 57r/20 - 9, ∓3(10-3r)/20)`,
`B₊ = (1 + 11r/20, 9r/20, ±3(10+r)/20)`, `B₋ = (11r/20 - 1, 9r/20, ∓3(10-r)/20)`.
Hence `‖S_0‖₁ = Tr(S_+ + S_-) = 16√10 + 4(n-2)` (`eq:witness-size`). -/

section ExactSplit
variable {m d n e : ℕ}

lemma sq10_sq : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
lemma three_le_sqrt10 : 3 ≤ Real.sqrt 10 := by nlinarith [sq10_sq, Real.sqrt_nonneg 10]
lemma sqrt10_lt_four : Real.sqrt 10 < 4 := by nlinarith [sq10_sq, Real.sqrt_nonneg 10]

/-- Positive spectral part of `(0, 3z; 3z, 18)`, `z = ±1` (eigenvalue `9 + 3√10`). -/
noncomputable def Ap (n : ℕ) (z : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  blkC n (3 * Real.sqrt 10 / 20) (9 + 57 * Real.sqrt 10 / 20) (3 * z * (10 + 3 * Real.sqrt 10) / 20)

/-- Negative spectral part of `(0, 3z; 3z, 18)` (eigenvalue `9 - 3√10`, sign flipped). -/
noncomputable def Am (n : ℕ) (z : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  blkC n (3 * Real.sqrt 10 / 20) (57 * Real.sqrt 10 / 20 - 9) (-(3 * z * (10 - 3 * Real.sqrt 10) / 20))

/-- Positive spectral part of `(2, 3z; 3z, 0)` (eigenvalue `1 + √10`). -/
noncomputable def Bp (n : ℕ) (z : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  blkC n (1 + 11 * Real.sqrt 10 / 20) (9 * Real.sqrt 10 / 20) (3 * z * (10 + Real.sqrt 10) / 20)

/-- Negative spectral part of `(2, 3z; 3z, 0)` (eigenvalue `1 - √10`, sign flipped). -/
noncomputable def Bm (n : ℕ) (z : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  blkC n (11 * Real.sqrt 10 / 20 - 1) (9 * Real.sqrt 10 / 20) (-(3 * z * (10 - Real.sqrt 10) / 20))

lemma Ap_psd {z : ℝ} (hz : z ^ 2 = 1) : (Ap n z).PosSemidef := by
  refine blkC_psd (by nlinarith [three_le_sqrt10]) (le_of_eq ?_)
  linear_combination (-(9 / 40) : ℝ) * sq10_sq
    + (9 / 400) * (100 + 60 * Real.sqrt 10 + 9 * Real.sqrt 10 ^ 2) * hz

lemma Am_psd {z : ℝ} (hz : z ^ 2 = 1) : (Am n z).PosSemidef := by
  refine blkC_psd (by nlinarith [three_le_sqrt10]) (le_of_eq ?_)
  linear_combination (-(9 / 40) : ℝ) * sq10_sq
    + (9 / 400) * (100 - 60 * Real.sqrt 10 + 9 * Real.sqrt 10 ^ 2) * hz

lemma Bp_psd {z : ℝ} (hz : z ^ 2 = 1) : (Bp n z).PosSemidef := by
  refine blkC_psd (by nlinarith [three_le_sqrt10]) (le_of_eq ?_)
  linear_combination (-(9 / 40) : ℝ) * sq10_sq
    + (9 / 400) * (100 + 20 * Real.sqrt 10 + Real.sqrt 10 ^ 2) * hz

lemma Bm_psd {z : ℝ} (hz : z ^ 2 = 1) : (Bm n z).PosSemidef := by
  refine blkC_psd (by nlinarith [three_le_sqrt10]) (le_of_eq ?_)
  linear_combination (-(9 / 40) : ℝ) * sq10_sq
    + (9 / 400) * (100 - 20 * Real.sqrt 10 + Real.sqrt 10 ^ 2) * hz

lemma Ap_sub_Am_one : Ap n 1 - Am n 1 = blkC n 0 18 3 := by
  rw [Ap, Am, blkC_sub]; congr 1 <;> ring

lemma Ap_sub_Am_neg : Ap n (-1) - Am n (-1) = blkC n 0 18 (-3) := by
  rw [Ap, Am, blkC_sub]; congr 1 <;> ring

lemma Bp_sub_Bm_one : Bp n 1 - Bm n 1 = blkC n 2 0 3 := by
  rw [Bp, Bm, blkC_sub]; congr 1 <;> ring

lemma Bp_sub_Bm_neg : Bp n (-1) - Bm n (-1) = blkC n 2 0 (-3) := by
  rw [Bp, Bm, blkC_sub]; congr 1 <;> ring

/-- `S_0` as four `(o, t)`-blocks: `18|1⟩⟨1| ± 3X` on `A_O = |0⟩` and `2|0⟩⟨0| ± 3X` plus the
`2(I - P_n)` tail on `A_O = |1⟩`. -/
theorem S0_eq_four_blocks :
    S0 m d n e
      = kron4 (proj m 1) (proj d 0) (blk n 0 18 3) (proj e 0)
        + kron4 (proj m 1) (proj d 0) (blk n 0 18 (-3)) (proj e 1)
        + kron4 (proj m 1) (proj d 1) (blk n 2 0 3 + (2 : ℚ) • (1 - P n)) (proj e 0)
        + kron4 (proj m 1) (proj d 1) (blk n 2 0 (-3) + (2 : ℚ) • (1 - P n)) (proj e 1) := by
  rw [S0, diag_part_eq]
  simp only [blk, P, Z, kron4_add₂, kron4_add₃, kron4_sub₃, kron4_add₄, kron4_sub₄, kron4_smul₃,
    zero_smul, zero_add, add_zero]
  module

lemma two_smul_one_sub_P_eq :
    (2 : ℚ) • ((1 : Matrix (Fin n) (Fin n) ℚ) - P n)
      = diagonal fun i : Fin n => if i.val = 0 ∨ i.val = 1 then (0 : ℚ) else 2 := by
  rw [P_eq, ← diagonal_one, diagonal_sub, ← diagonal_smul]
  congr 1; funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs <;> norm_num

lemma psd_toC_tail : (toC ((2 : ℚ) • ((1 : Matrix (Fin n) (Fin n) ℚ) - P n))).PosSemidef := by
  rw [two_smul_one_sub_P_eq]
  exact diagonal_nonneg_sound _ fun i => by split_ifs <;> norm_num

lemma trace_tail (hn : 2 ≤ n) :
    trace ((2 : ℚ) • ((1 : Matrix (Fin n) (Fin n) ℚ) - P n)) = 2 * (n - 2) := by
  rw [trace_smul, trace_sub, trace_one, Fintype.card_fin, trace_P hn, smul_eq_mul]

/-- The positive spectral part `S_+` of `S_0` (`eq:witness-size`). -/
noncomputable def SplusX (m d n e : ℕ) : Matrix (Lab m d n e) (Lab m d n e) ℂ :=
  (toC (proj m 1) ⊗ₖ toC (proj d 0)) ⊗ₖ (Ap n 1 ⊗ₖ toC (proj e 0))
    + (toC (proj m 1) ⊗ₖ toC (proj d 0)) ⊗ₖ (Ap n (-1) ⊗ₖ toC (proj e 1))
    + (toC (proj m 1) ⊗ₖ toC (proj d 1)) ⊗ₖ
        ((Bp n 1 + toC ((2 : ℚ) • ((1 : Matrix (Fin n) (Fin n) ℚ) - P n))) ⊗ₖ toC (proj e 0))
    + (toC (proj m 1) ⊗ₖ toC (proj d 1)) ⊗ₖ
        ((Bp n (-1) + toC ((2 : ℚ) • ((1 : Matrix (Fin n) (Fin n) ℚ) - P n))) ⊗ₖ toC (proj e 1))

/-- The negative spectral part `S_-` of `S_0` (`eq:witness-size`), sign flipped. -/
noncomputable def SminusX (m d n e : ℕ) : Matrix (Lab m d n e) (Lab m d n e) ℂ :=
  (toC (proj m 1) ⊗ₖ toC (proj d 0)) ⊗ₖ (Am n 1 ⊗ₖ toC (proj e 0))
    + (toC (proj m 1) ⊗ₖ toC (proj d 0)) ⊗ₖ (Am n (-1) ⊗ₖ toC (proj e 1))
    + (toC (proj m 1) ⊗ₖ toC (proj d 1)) ⊗ₖ (Bm n 1 ⊗ₖ toC (proj e 0))
    + (toC (proj m 1) ⊗ₖ toC (proj d 1)) ⊗ₖ (Bm n (-1) ⊗ₖ toC (proj e 1))

/-- **Spectral split** `S_0 = S_+ - S_-` (`eq:witness-size`). -/
theorem toC_S0_eq_split : toC (S0 m d n e) = SplusX m d n e - SminusX m d n e := by
  rw [S0_eq_four_blocks]
  simp only [toC_add, toC_kron4, toC_blk, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_neg,
    ← Ap_sub_Am_one, ← Ap_sub_Am_neg, ← Bp_sub_Bm_one, ← Bp_sub_Bm_neg]
  unfold SplusX SminusX
  simp only [kron_sub_right, kron_sub_left, kronecker_add, add_kronecker]
  abel

theorem SplusX_psd : (SplusX m d n e).PosSemidef := by
  unfold SplusX
  refine PosSemidef.add (PosSemidef.add (PosSemidef.add ?_ ?_) ?_) ?_
  · exact ((psd_toC_proj _ _).kronecker (psd_toC_proj _ _)).kronecker
      ((Ap_psd (by norm_num)).kronecker (psd_toC_proj _ _))
  · exact ((psd_toC_proj _ _).kronecker (psd_toC_proj _ _)).kronecker
      ((Ap_psd (by norm_num)).kronecker (psd_toC_proj _ _))
  · exact ((psd_toC_proj _ _).kronecker (psd_toC_proj _ _)).kronecker
      (((Bp_psd (by norm_num)).add psd_toC_tail).kronecker (psd_toC_proj _ _))
  · exact ((psd_toC_proj _ _).kronecker (psd_toC_proj _ _)).kronecker
      (((Bp_psd (by norm_num)).add psd_toC_tail).kronecker (psd_toC_proj _ _))

theorem SminusX_psd : (SminusX m d n e).PosSemidef := by
  unfold SminusX
  refine PosSemidef.add (PosSemidef.add (PosSemidef.add ?_ ?_) ?_) ?_
  · exact ((psd_toC_proj _ _).kronecker (psd_toC_proj _ _)).kronecker
      ((Am_psd (by norm_num)).kronecker (psd_toC_proj _ _))
  · exact ((psd_toC_proj _ _).kronecker (psd_toC_proj _ _)).kronecker
      ((Am_psd (by norm_num)).kronecker (psd_toC_proj _ _))
  · exact ((psd_toC_proj _ _).kronecker (psd_toC_proj _ _)).kronecker
      ((Bm_psd (by norm_num)).kronecker (psd_toC_proj _ _))
  · exact ((psd_toC_proj _ _).kronecker (psd_toC_proj _ _)).kronecker
      ((Bm_psd (by norm_num)).kronecker (psd_toC_proj _ _))

/-- **`eq:witness-size`**: `‖S_0‖₁ = Tr(S_+ + S_-) = 16√10 + 4(n - 2)`. -/
theorem trace_SplusX_add_SminusX (hm : 2 ≤ m) (hd : 2 ≤ d) (hn : 2 ≤ n) (he : 2 ≤ e) :
    trace (SplusX m d n e + SminusX m d n e) = ((16 * Real.sqrt 10 + 4 * (n - 2) : ℝ) : ℂ) := by
  simp only [SplusX, SminusX, Ap, Am, Bp, Bm, trace_add, trace_kronecker, trace_toC, trace_blkC hn,
    trace_proj1 hm, trace_proj0 hd, trace_proj1 hd, trace_proj0 he, trace_proj1 he, trace_tail hn]
  push_cast
  ring

end ExactSplit

section ExactMargin
variable (D : Ports)

/-- PSD pairing on the ball, complex `S`: `-r Re Tr S ≤ Re Tr(S H) ≤ r Re Tr S`. -/
theorem re_trace_mul_bounds_C {S : PMat D} (hS : S.PosSemidef) {H : PMat D} (hH : InBall D H) :
    (trace (S * H)).re ≤ (1 / (300 * D.m * D.n) : ℝ) * (trace S).re ∧
      -((1 / (300 * D.m * D.n) : ℝ) * (trace S).re) ≤ (trace (S * H)).re := by
  have h1 := trace_mul_nonneg hS hH.2.2.1
  have h2 := trace_mul_nonneg hS hH.2.2.2
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, trace_add, trace_smul, smul_eq_mul,
    ballRadius_eq_ofReal] at h1
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, trace_sub, trace_smul, smul_eq_mul,
    ballRadius_eq_ofReal] at h2
  have h1' := (Complex.nonneg_iff.mp h1).1
  have h2' := (Complex.nonneg_iff.mp h2).1
  rw [Complex.add_re, Complex.re_ofReal_mul] at h1'
  rw [Complex.sub_re, Complex.re_ofReal_mul] at h2'
  constructor <;> linarith

/-- **Exact witness bound on the ball**: `|Re Tr(S_0 H)| ≤ (16√10 + 4(n-2))/(300 m n)`
(`eq:witness-size` with `|Tr(S_0 H)| ≤ ‖S_0‖₁ ‖H‖_∞`). -/
theorem abs_re_trace_S0_mul_le_exact (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    |(trace (toC (S0 D.m D.d D.n D.e) * H)).re|
      ≤ (16 * Real.sqrt 10 + 4 * (D.n - 2)) / (300 * D.m * D.n) := by
  obtain ⟨hp1, hp2⟩ := re_trace_mul_bounds_C D (SplusX_psd (m := D.m) (d := D.d) (n := D.n) (e := D.e)) hH
  obtain ⟨hm1, hm2⟩ := re_trace_mul_bounds_C D (SminusX_psd (m := D.m) (d := D.d) (n := D.n) (e := D.e)) hH
  have e : (trace (toC (S0 D.m D.d D.n D.e) * H)).re
      = (trace (SplusX D.m D.d D.n D.e * H)).re - (trace (SminusX D.m D.d D.n D.e * H)).re := by
    rw [toC_S0_eq_split, Matrix.sub_mul, trace_sub, Complex.sub_re]
  have ht : (trace (SplusX D.m D.d D.n D.e)).re + (trace (SminusX D.m D.d D.n D.e)).re
      = 16 * Real.sqrt 10 + 4 * (D.n - 2) := by
    have := trace_SplusX_add_SminusX h.1 h.2.1 h.2.2.1 h.2.2.2
    rw [trace_add] at this
    have := congrArg Complex.re this
    rwa [Complex.add_re, Complex.ofReal_re] at this
  have key : (1 / (300 * D.m * D.n) : ℝ) * (trace (SplusX D.m D.d D.n D.e)).re
      + (1 / (300 * D.m * D.n) : ℝ) * (trace (SminusX D.m D.d D.n D.e)).re
      = (16 * Real.sqrt 10 + 4 * (D.n - 2)) / (300 * D.m * D.n) := by
    rw [← mul_add, ht]; ring
  rw [e, abs_le]
  constructor <;> linarith

/-- **`eq:center-margin`, second part**: `‖S_0‖₁/(300 m n) ≤ √10/75` for `m, n ≥ 2`
(tight at `m = n = 2`). -/
theorem witness_size_margin (hm : 2 ≤ D.m) (hn : 2 ≤ D.n) :
    (16 * Real.sqrt 10 + 4 * (D.n - 2)) / (300 * D.m * D.n) ≤ Real.sqrt 10 / 75 := by
  have hm' : (2 : ℝ) ≤ D.m := by exact_mod_cast hm
  have hn' : (2 : ℝ) ≤ D.n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 300 * D.m * D.n := by positivity
  rw [div_le_iff₀ hpos]
  have h1 : 0 ≤ ((D.m : ℝ) - 2) * ((D.n : ℝ) * Real.sqrt 10) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (Real.sqrt_nonneg 10))
  have h2 : 0 ≤ ((D.n : ℝ) - 2) * (Real.sqrt 10 - 3) :=
    mul_nonneg (by linarith) (by linarith [three_le_sqrt10])
  nlinarith [h1, h2]

attribute [local instance 1100] ballNegativeExact_atLeastTwo49
  ballNegativeExact_atLeastTwo500 ballNegativeExact_atLeastTwo10
  ballNegativeExact_atLeastTwo75 in
/-- **`eq:ball-negative` verbatim**: `Re Tr(S_0 (W_c + H)) ≤ -49/500 + √10/75` on the ball. -/
theorem ball_witness_negative_exact (h : AllPortsGE2 D) {H : PMat D} (hH : InBall D H) :
    (trace (toC (S0 D.m D.d D.n D.e) * (WcC D + H))).re ≤ -49 / 500 + Real.sqrt 10 / 75 := by
  rw [Matrix.mul_add, trace_add, Complex.add_re, WcC, ← Matrix.map_mul, trace_toC,
    Complex.ratCast_re]
  have h1 : ((trace (S0 D.m D.d D.n D.e * Wc D.m D.d D.n D.e) : ℚ) : ℝ) ≤ -49 / 500 := by
    exact_mod_cast trace_S0_mul_Wc_le h.1 h.2.1 h.2.2.1 h.2.2.2
  have h2 := (abs_le.mp (abs_re_trace_S0_mul_le_exact D h hH)).2
  have h3 := witness_size_margin D h.1 h.2.2.1
  linarith

/-- `-49/500 + √10/75 = -(147 - 20√10)/1500` (`eq:ball-negative`). -/
theorem ball_negative_const : (-49 / 500 + Real.sqrt 10 / 75 : ℝ) = -(147 - 20 * Real.sqrt 10) / 1500 := by
  ring

/-- `-(147 - 20√10)/1500 < 0` (`eq:ball-negative`). -/
theorem ball_negative_lt_zero : (-49 / 500 + Real.sqrt 10 / 75 : ℝ) < 0 := by
  linarith [sqrt10_lt_four]

end ExactMargin

end CausalNonpurifiability
