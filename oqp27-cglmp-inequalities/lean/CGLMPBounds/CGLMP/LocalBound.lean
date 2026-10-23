module

public import CGLMPBounds.Defs.CGLMP
public import CGLMPBounds.Scenario.Local

@[expose] public section


/-!
# The CGLMP local bound and the uniform-noise witness threshold

Manuscript locators: Appendix B, text after (B.1) ("For a deterministic strategy, the residuals
sum to `-1` modulo `d`, so `S_d ≥ d - 1`, equivalently `I_d ≤ 2`", quoted from CGLMP and
Acín–Gill–Gisin), and the proof of Theorem A.3 (`I_d(u_d) = 0`,
`I_d(v q + (1 - v) u_d) = v I_d(q)`, hence the witness threshold `v_CGLMP = 2 / I_d(q)`).

Main results:
* `cglmp_le_two`            : `I_d(q) ≤ 2` for every Bell-local `q` (`d ≥ 2`);
* `exists_mem_localSet_cglmp_eq_two` : the bound `2` is attained by a deterministic table;
* `cglmp_uniformTable`      : `I_d(u_d) = 0`;
* `cglmp_noisy`             : `I_d(v q + (1 - v) u_d) = v I_d(q)`;
* `two_lt_cglmp_noisy_iff`  : the mixture violates the CGLMP inequality iff `v > 2 / I_d(q)`;
* `visibility_le_of_noisy_mem_localSet` : a local mixture has `v ≤ 2 / I_d(q)`.
-/

namespace CGLMPBounds

noncomputable section

section Residual

variable (d : ℕ)

@[simp] theorem residual_zero_zero (a b : ZMod d) : residual d 0 0 a b = (a - b).val :=
  rfl

@[simp] theorem residual_one_zero (a b : ZMod d) : residual d 1 0 a b = (b - a).val :=
  rfl

@[simp] theorem residual_one_one (a b : ZMod d) : residual d 1 1 a b = (a - b).val :=
  rfl

@[simp] theorem residual_zero_one (a b : ZMod d) : residual d 0 1 a b = (b - a - 1).val :=
  rfl

end Residual

variable (d : ℕ) [NeZero d]

/-- The coefficient table of the residual score, `(x, y, a, b) ↦ r_{xy}(a,b)`. -/
def residualTable : Table (ZMod d) (ZMod d) := fun x y a b => (residual d x y a b : ℝ)

theorem cglmpS_eq_bell (q : Table (ZMod d) (ZMod d)) :
    cglmpS d q = bell (residualTable d) q :=
  rfl

/-- The cyclic constraint: for a deterministic assignment the four residuals sum to `-1`
modulo `d`, hence to at least `d - 1`. -/
theorem le_sum_residual_add_one (a₀ a₁ b₀ b₁ : ZMod d) :
    d ≤ (a₀ - b₀).val + (b₁ - a₀ - 1).val + (b₀ - a₁).val + (a₁ - b₁).val + 1 := by
  refine Nat.le_of_dvd (Nat.succ_pos _) ((CharP.cast_eq_zero_iff (ZMod d) d _).mp ?_)
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  ring

theorem sub_one_le_bell_residualTable_detTable (s : Strategy (ZMod d) (ZMod d)) :
    (d : ℝ) - 1 ≤ bell (residualTable d) (detTable s) := by
  rw [bell_detTable]
  simp only [Fin.sum_univ_two, residualTable, residual_zero_zero, residual_zero_one,
    residual_one_zero, residual_one_one]
  have h : ((d : ℕ) : ℝ) ≤ (((s.1 0 - s.2 0).val + (s.2 1 - s.1 0 - 1).val
      + (s.2 0 - s.1 1).val + (s.1 1 - s.2 1).val + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (le_sum_residual_add_one d (s.1 0) (s.1 1) (s.2 0) (s.2 1))
  push_cast at h
  linarith

/-- `S_d(q) ≥ d - 1` on the local set. -/
theorem sub_one_le_cglmpS {q : Table (ZMod d) (ZMod d)}
    (hq : q ∈ localSet (ZMod d) (ZMod d)) : (d : ℝ) - 1 ≤ cglmpS d q := by
  rw [cglmpS_eq_bell]
  exact le_bell_of_mem_localSet (sub_one_le_bell_residualTable_detTable d) hq

/-- **CGLMP local bound** (Collins–Gisin–Linden–Massar–Popescu; Acín–Gill–Gisin): every
Bell-local table satisfies `I_d ≤ 2`. -/
theorem cglmp_le_two (hd : 2 ≤ d) {q : Table (ZMod d) (ZMod d)}
    (hq : q ∈ localSet (ZMod d) (ZMod d)) : cglmp d q ≤ 2 := by
  have hd' : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hS := sub_one_le_cglmpS d hq
  have h2 : 2 ≤ 2 * cglmpS d q / ((d : ℝ) - 1) := by
    rw [le_div_iff₀ hd']
    linarith
  unfold cglmp
  linarith

/-- An assignment with all four outcomes equal to `0` has `S_d = d - 1`. -/
theorem cglmpS_detTable_eq_of_zero (s : Strategy (ZMod d) (ZMod d)) (h1 : ∀ x, s.1 x = 0)
    (h2 : ∀ y, s.2 y = 0) : cglmpS d (detTable s) = (d : ℝ) - 1 := by
  apply le_antisymm
  · rw [cglmpS_eq_bell, bell_detTable]
    have h0 : ((0 : ZMod d) - 0).val = 0 := by rw [sub_self, ZMod.val_zero]
    have hlt : ((0 : ZMod d) - 0 - 1).val + 1 ≤ d := by
      have := ZMod.val_lt ((0 : ZMod d) - 0 - 1)
      omega
    have hlt' : ((((0 : ZMod d) - 0 - 1).val + 1 : ℕ) : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr hlt
    rw [Nat.cast_add, Nat.cast_one] at hlt'
    simp only [Fin.sum_univ_two, residualTable, residual_zero_zero, residual_zero_one,
      residual_one_zero, residual_one_one, h1, h2, h0, Nat.cast_zero, zero_add, add_zero]
    linarith
  · exact sub_one_le_cglmpS d (subset_convexHull ℝ _ ⟨s, rfl⟩)

/-- The local bound is attained: the constant deterministic table has `I_d = 2`. -/
theorem exists_mem_localSet_cglmp_eq_two (hd : 2 ≤ d) :
    ∃ q ∈ localSet (ZMod d) (ZMod d), cglmp d q = 2 := by
  have hd' : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    intro h0
    linarith
  refine ⟨detTable (fun _ => 0, fun _ => 0), subset_convexHull ℝ _ ⟨_, rfl⟩, ?_⟩
  unfold cglmp
  rw [cglmpS_detTable_eq_of_zero d (fun _ => 0, fun _ => 0) (fun _ => rfl) (fun _ => rfl),
    mul_div_assoc, div_self hd']
  norm_num

/-! ### Uniform noise -/

theorem sum_range_natCast (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (i : ℝ) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- `∑_{c ∈ ℤ_d} [c]_d = d (d - 1) / 2`. -/
theorem sum_val : ∑ c : ZMod d, (c.val : ℝ) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  have h : ∑ c : ZMod (n + 1), (c.val : ℝ) = ∑ i ∈ Finset.range (n + 1), (i : ℝ) :=
    Fin.sum_univ_eq_sum_range (fun i => (i : ℝ)) (n + 1)
  rw [h, sum_range_natCast]
  push_cast
  ring

/-- For a fixed outcome of Alice, each residual is a bijective function of Bob's outcome. -/
theorem sum_residual (x y : Fin 2) (a : ZMod d) :
    ∑ b : ZMod d, (residual d x y a b : ℝ) = ∑ c : ZMod d, (c.val : ℝ) := by
  unfold residual
  split_ifs
  · exact Fintype.sum_equiv (Equiv.subLeft a) _ _ (fun _ => rfl)
  · exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)
  · exact Fintype.sum_equiv ((Equiv.subRight a).trans (Equiv.subRight 1)) _ _ (fun _ => rfl)

theorem sum_sum_residual (x y : Fin 2) :
    ∑ a : ZMod d, ∑ b : ZMod d, (residual d x y a b : ℝ)
      = (d : ℝ) * ((d : ℝ) * ((d : ℝ) - 1) / 2) := by
  simp only [sum_residual, sum_val, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

/-- `S_d(u_d) = 2 (d - 1)`. -/
theorem cglmpS_uniformTable :
    cglmpS d (uniformTable (ZMod d) (ZMod d)) = 2 * ((d : ℝ) - 1) := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  unfold cglmpS uniformTable
  simp only [← Finset.sum_mul, sum_sum_residual, ZMod.card, Fin.sum_univ_two]
  rw [mul_one_div, div_eq_iff (mul_ne_zero hd hd)]
  ring

/-- `I_d(u_d) = 0`. -/
theorem cglmp_uniformTable (hd : 2 ≤ d) : cglmp d (uniformTable (ZMod d) (ZMod d)) = 0 := by
  have hd' : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    intro h0
    linarith
  unfold cglmp
  rw [cglmpS_uniformTable,
    show 2 * (2 * ((d : ℝ) - 1)) / ((d : ℝ) - 1) = 4 from by rw [div_eq_iff hd']; ring]
  norm_num

/-- `S_d` is affine along the noise line. -/
theorem cglmpS_noisy (v : ℝ) (q : Table (ZMod d) (ZMod d)) :
    cglmpS d (noisy v q)
      = v * cglmpS d q + (1 - v) * cglmpS d (uniformTable (ZMod d) (ZMod d)) := by
  simp only [cglmpS_eq_bell, noisy, map_add, map_smul, smul_eq_mul]

/-- `I_d(v q + (1 - v) u_d) = v I_d(q)` (proof of Theorem A.3). -/
theorem cglmp_noisy (hd : 2 ≤ d) (v : ℝ) (q : Table (ZMod d) (ZMod d)) :
    cglmp d (noisy v q) = v * cglmp d q := by
  have hd' : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    intro h0
    linarith
  have key : ∀ S D : ℝ, D ≠ 0 →
      4 - 2 * (v * S + (1 - v) * (2 * D)) / D = v * (4 - 2 * S / D) := by
    intro S D hD
    field_simp
    ring
  unfold cglmp
  rw [cglmpS_noisy, cglmpS_uniformTable]
  exact key _ _ hd'

/-- For `I_d(q) > 2`, the uniform-noise mixture violates the CGLMP inequality exactly above the
witness threshold `v_CGLMP(q) = 2 / I_d(q)` (Appendix B; first display of Theorem A.3). -/
theorem two_lt_cglmp_noisy_iff (hd : 2 ≤ d) {q : Table (ZMod d) (ZMod d)}
    (hq : 2 < cglmp d q) (v : ℝ) :
    2 < cglmp d (noisy v q) ↔ 2 / cglmp d q < v := by
  have hpos : 0 < cglmp d q := by linarith
  rw [cglmp_noisy d hd, div_lt_iff₀ hpos]

/-- If the uniform-noise mixture at visibility `v` is Bell-local then `v ≤ 2 / I_d(q)`:
the global critical visibility is at most the CGLMP witness threshold. -/
theorem visibility_le_of_noisy_mem_localSet (hd : 2 ≤ d) {q : Table (ZMod d) (ZMod d)}
    (hq : 2 < cglmp d q) {v : ℝ} (h : noisy v q ∈ localSet (ZMod d) (ZMod d)) :
    v ≤ 2 / cglmp d q := by
  have hpos : 0 < cglmp d q := by linarith
  have h2 := cglmp_le_two d hd h
  rw [cglmp_noisy d hd] at h2
  rwa [le_div_iff₀ hpos]

end

end CGLMPBounds
