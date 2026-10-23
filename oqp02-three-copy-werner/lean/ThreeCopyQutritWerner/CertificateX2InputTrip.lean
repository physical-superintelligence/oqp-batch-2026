module

public import ThreeCopyQutritWerner.CertificateX2InputKeys
public import ThreeCopyQutritWerner.CertificateX2InputT2

@[expose] public section


/-!
# Input stage: one sorted type triple, generically

For a sorted type triple `t = (t₀ ≤ t₁ ≤ t₂)` of a source sector and every symmetric source `N`:
* key glue (`keyOK`): every key of the triple contributes parts `(S, F, α)` with
  `3 den_c · lookup = ibIB` and bounded terms: trial keys (`trialKeyOK`), degree-2 trial keys
  with checked partner columns (`trial2KeyOK`), corrected keys in the light form `K (A / den_c) Kᵀ`
  with checked `U = GJ K` and `UA = U A` columns (`corrKeyOK`); `x2KeySum_ib` sums the keys;
* `ubSpec`: stored upper blocks in a nested table `UBT[a₀][a₁][b₀][b₁]` that pass `ibBatchOK` hold the
  input-block values;
* `ttSpecGen`: T-blocks (labels `slab t₀ i₀`, `slab t₁ i₁`) that pass `t2Check` against the stored
  blocks hold `σ · x2EmbedS` at every label triple of the type triple; `TTspecS` (rows by the second
  label) and `TCspecS` (rows by the first label) are the two table orders;
* `zspecS_of_empty`: a triple whose keys contribute no part has `x2EmbedS = 0` on its labels.
`σ = 24 den_c`, `ratio = den_c / 2^160 = 31603654656000`. All widths are `W = 256`.
-/

set_option maxRecDepth 100000
set_option exponentiation.threshold 1000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-! ### Bounded parts -/

/-- Both operands of a part in range, its weight below `2^302 / 2^255`, every term `|α S(x) F(y)| ≤ 2^227`. -/
def partBound (L : ℕ) (p : ℕ × ℕ × ℕ) : Prop :=
  p.1 < 2 ^ (256 * L) ∧ p.2.1 < 2 ^ (256 * L) ∧ p.2.2 * 2 ^ (256 - 1) ≤ 2 ^ 302 ∧
    ∀ x < L, ∀ y < L, |(p.2.2 : ℤ) * ent 256 (256 - 1) p.1 x * ent 256 (256 - 1) p.2.1 y| ≤ 2 ^ 227

theorem ibIB_abs_le_parts (L : ℕ) : ∀ (fs : List (ℕ × ℕ × ℕ)), (∀ p ∈ fs, partBound L p) →
    ∀ x < L, ∀ y < L, |ibIB 256 fs x y| ≤ fs.length * 2 ^ 227
  | [], _, x, _, y, _ => by simp [ibIB]
  | p :: fs, h, x, hx, y, hy => by
    have hp := (h p (by simp)).2.2.2 x hx y hy
    have ih := ibIB_abs_le_parts L fs (fun q hq => h q (by simp [hq])) x hx y hy
    unfold ibIB at ih ⊢
    rw [List.map_cons, List.sum_cons, List.length_cons]
    calc |(p.2.2 : ℤ) * ent 256 (256 - 1) p.1 x * ent 256 (256 - 1) p.2.1 y +
          (List.map (fun p => (p.2.2 : ℤ) * ent 256 (256 - 1) p.1 x * ent 256 (256 - 1) p.2.1 y) fs).sum|
        ≤ |(p.2.2 : ℤ) * ent 256 (256 - 1) p.1 x * ent 256 (256 - 1) p.2.1 y| +
          |(List.map (fun p => (p.2.2 : ℤ) * ent 256 (256 - 1) p.1 x * ent 256 (256 - 1) p.2.1 y) fs).sum| :=
          abs_add_le _ _
      _ ≤ 2 ^ 227 + fs.length * 2 ^ 227 := add_le_add hp ih
      _ = ((fs.length + 1 : ℕ) : ℤ) * 2 ^ 227 := by push_cast; ring

theorem mem_ibFS_single (L1 L2 : List ℕ) (α : ℕ) (p : ℕ × ℕ × ℕ) (hp : p ∈ ibFS [(L1, L2, α)]) :
    ∃ c, c < L1.length ∧ c < L2.length ∧ p = (L1.getD c 0, L2.getD c 0, α) := by
  have e : ibFS [(L1, L2, α)] = (L1.zip L2).map (fun sf => (sf.1, sf.2, α)) := by
    simp [ibFS]
  rw [e, List.mem_map] at hp
  obtain ⟨sf, hsf, rfl⟩ := hp
  obtain ⟨c, hc, hce⟩ := List.mem_iff_getElem.mp hsf
  rw [List.length_zip] at hc
  refine ⟨c, by omega, by omega, ?_⟩
  rw [← hce, List.getElem_zip, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]

/-- `ibIB` of one part `(L₁, L₂, α)` with lists of equal length. -/
theorem ibIB_pair (α : ℕ) (x y : ℕ) : ∀ L1 L2 : List ℕ, L1.length = L2.length →
    ibIB 256 (ibFS [(L1, L2, α)]) x y = ∑ c ∈ Finset.range L1.length,
      (α : ℤ) * ent 256 (256 - 1) (L1.getD c 0) x * ent 256 (256 - 1) (L2.getD c 0) y
  | [], _, _ => by simp [ibIB, ibFS]
  | _ :: _, [], h => by simp at h
  | F :: L1, G :: L2, h => by
    have ih := ibIB_pair α x y L1 L2 (by simpa using h)
    have e : ibFS [(F :: L1, G :: L2, α)] = (F, G, α) :: ibFS [(L1, L2, α)] := by
      simp [ibFS]
    rw [e]
    unfold ibIB at ih ⊢
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-! ### Key glue -/

/-- A key's input-block lookup as an `ibIB` of its parts (`3 den_c` scale). -/
def keyIB (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (fs : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ a b : Fin 3 → ℕ, a 0 < x2KeyMult s k 0 → a 1 < x2KeyMult s k 1 → a 2 < x2KeyMult s k 2 →
    b 0 < x2KeyMult s k 0 → b 1 < x2KeyMult s k 1 → b 2 < x2KeyMult s k 2 →
    (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) *
        x2Lookup (x2InputBlock x2DataConcrete s N k) a b =
      (ibIB 256 fs (kflat (x2KeyMult s k 1) (x2KeyMult s k 2) (a 0) (a 1) (a 2))
        (kflat (x2KeyMult s k 1) (x2KeyMult s k 2) (b 0) (b 1) (b 2)) : ℚ)

/-- Key glue together with the bounds of its parts. -/
def keyOK (L : ℕ) (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (fs : List (ℕ × ℕ × ℕ)) : Prop :=
  keyIB s N k fs ∧ ∀ p ∈ fs, partBound L p

/-- The checked `GJ` columns of a key are in range and bounded by `2^37`. -/
theorem gj_bounds (s : Fin 3) (k : x2Key s) (GJcols : List ℕ)
    (h0 : 1 ≤ x2KeyMult s k 0) (h1 : 1 ≤ x2KeyMult s k 1) (h2 : 1 ≤ x2KeyMult s k 2)
    (hr0 : glRowOK s (x2KeyTypes s k 0) (x2KeyMult s k 0) 512 = true)
    (hr1 : glRowOK s (x2KeyTypes s k 1) (x2KeyMult s k 1) 512 = true)
    (hr2 : glRowOK s (x2KeyTypes s k 2) (x2KeyMult s k 2) 512 = true)
    (hchk : ∀ d < x2KeySize s k, gjCheck 256 s (x2KeyTypes s k 0) (x2KeyTypes s k 1) (x2KeyTypes s k 2)
      (x2KeyMult s k 0) (x2KeyMult s k 1) (x2KeyMult s k 2) (x2JCols (x2KeyGlobal s k) d) (GJcols.getD d 0) = true) :
    ∀ d < x2KeySize s k, GJcols.getD d 0 < 2 ^ (256 * (x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2)) ∧
      ∀ t < x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2, |ent 256 (256 - 1) (GJcols.getD d 0) t| ≤ 2 ^ 37 := by
  intro d hd
  obtain ⟨hl, hb, _⟩ := gjCheck_sound 256 s _ _ _ _ _ _ _ _ (by norm_num) h0 h1 h2 hr0 hr1 hr2 (hchk d hd)
  exact ⟨hl, hb⟩

theorem keyOK_of_trial (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (n L : ℕ) (GJcols Fcols Vcols : List ℕ)
    (hL : x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2 = L)
    (h : trialKeyOK 256 s N k n GJcols Fcols Vcols) :
    keyOK L s N k (ibFS [(Vcols, Vcols, 94810963968000)]) := by
  refine ⟨fun a b ha0 ha1 ha2 hb0 hb1 hb2 =>
    x2Lookup_trial_ib' 256 s N k n GJcols Fcols Vcols (by norm_num) h a b ha0 ha1 ha2 hb0 hb1 hb2, ?_⟩
  obtain ⟨_, _, h0, h1, h2, hr0, hr1, hr2, hlen, hsz, hchk, hv, hVlen⟩ := h
  have hGJ := gj_bounds s k GJcols h0 h1 h2 hr0 hr1 hr2 hchk
  intro p hp
  obtain ⟨c, hc, _, rfl⟩ := mem_ibFS_single Vcols Vcols 94810963968000 p hp
  rw [hVlen] at hc
  obtain ⟨hl, hb, _⟩ := vCheck_sound 256 _ _ GJcols _ _ (by norm_num) hlen hsz hGJ (hv c hc)
  rw [hL] at hl hb
  refine ⟨hl, hl, by norm_num, fun x hx y hy => ?_⟩
  have e1 := hb x hx
  have e2 := hb y hy
  rw [abs_mul, abs_mul]
  calc |((94810963968000 : ℕ) : ℤ)| * |ent 256 (256 - 1) (Vcols.getD c 0) x| *
        |ent 256 (256 - 1) (Vcols.getD c 0) y|
      ≤ 94810963968000 * 2 ^ 90 * 2 ^ 90 := by
        have e0 : |((94810963968000 : ℕ) : ℤ)| = 94810963968000 := by norm_num
        rw [e0]
        exact mul_le_mul (mul_le_mul_of_nonneg_left e1 (by norm_num)) e2 (abs_nonneg _) (by positivity)
    _ ≤ 2 ^ 227 := by norm_num

/-! #### Degree-2 trial keys: partner columns -/

/-- `GJ F` of a key (`F` the integer factor with packed columns `Fcols`). -/
noncomputable def x2GF (s : Fin 3) (k : x2Key s) (n : ℕ) (Fcols : List ℕ) : Matrix (x2Amb s k) (Fin n) ℚ :=
  x2GJ x2DataConcrete s k * (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ)

/-- Flat index maps of the cyclic rotations `(y₀, y₁, y₂) ↦ (y₂, y₀, y₁)` and `↦ (y₁, y₂, y₀)`. -/
def rotA (m x : ℕ) : ℕ := kflat m m (x % m) (x / (m * m)) ((x / m) % m)

def rotB (m x : ℕ) : ℕ := kflat m m ((x / m) % m) (x % m) (x / (m * m))

theorem kflat_coords (m y0 y1 y2 : ℕ) (h1 : y1 < m) (h2 : y2 < m) :
    kflat m m y0 y1 y2 % m = y2 ∧ (kflat m m y0 y1 y2 / m) % m = y1 ∧ kflat m m y0 y1 y2 / (m * m) = y0 := by
  have hm : 0 < m := by omega
  unfold kflat
  have e1 : ((y0 * m + y1) * m + y2) / m = y0 * m + y1 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt h2, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  · rw [e1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
  · rw [← Nat.div_div_eq_div_mul, e1, Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt h1, zero_add]

theorem rot_kflat (m y0 y1 y2 : ℕ) (h1 : y1 < m) (h2 : y2 < m) :
    rotA m (kflat m m y0 y1 y2) = kflat m m y2 y0 y1 ∧ rotB m (kflat m m y0 y1 y2) = kflat m m y1 y2 y0 := by
  obtain ⟨e2, e1, e0⟩ := kflat_coords m y0 y1 y2 h1 h2
  unfold rotA rotB
  rw [e2, e1, e0]
  exact ⟨rfl, rfl⟩

theorem rot_lt (m x : ℕ) (hx : x < m * m * m) : rotA m x < m * m * m ∧ rotB m x < m * m * m := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hx
    · exact h
  have h1 : x % m < m := Nat.mod_lt _ hm
  have h2 : (x / m) % m < m := Nat.mod_lt _ hm
  have h3 : x / (m * m) < m := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc x < m * m * m := hx
      _ = m * (m * m) := by ring
  unfold rotA rotB kflat
  constructor
  · have := site_idx_lt m m m _ _ _ h1 h3 h2
    calc _ < m * (m * m) := this
      _ = m * m * m := by ring
  · have := site_idx_lt m m m _ _ _ h2 h1 h3
    calc _ < m * (m * m) := this
      _ = m * m * m := by ring

/-- Partner column check: slot `x` of `P` is `V(rotA x) - V(rotB x)` (offset `2^255` slots), plus a slot
bound `2^91`. -/
noncomputable def partnerCheck (m V P : ℕ) : Bool :=
  Nat.beq P (concatFibers 256 1 ((List.range (m * m * m)).map
      (fun x => digS 256 V (rotA m x) + 2 ^ (256 - 1) - digS 256 V (rotB m x)))) &&
    slotBoundCheck 256 91 (m * m * m) P

theorem dig_one_zero (W f : ℕ) (hf : f < 2 ^ W) : dig W f 0 = f := by
  unfold dig
  rw [mul_zero, pow_zero, Nat.div_one, Nat.mod_eq_of_lt hf]

theorem partner_slot (V a b : ℕ) (ha : |ent 256 (256 - 1) V a| ≤ 2 ^ 90) (hb : |ent 256 (256 - 1) V b| ≤ 2 ^ 90) :
    dig 256 V b ≤ dig 256 V a + 2 ^ (256 - 1) ∧
      dig 256 V a + 2 ^ (256 - 1) - dig 256 V b < 2 ^ 256 ∧
      ((dig 256 V a + 2 ^ (256 - 1) - dig 256 V b : ℕ) : ℤ) - 2 ^ (256 - 1) =
        ent 256 (256 - 1) V a - ent 256 (256 - 1) V b := by
  unfold ent at ha hb ⊢
  rw [abs_le] at ha hb
  have hle : ((dig 256 V b : ℕ) : ℤ) ≤ (dig 256 V a : ℤ) + 2 ^ (256 - 1) := by
    norm_num at ha hb ⊢; linarith [ha.1, hb.2]
  have hle' : dig 256 V b ≤ dig 256 V a + 2 ^ (256 - 1) := by exact_mod_cast hle
  refine ⟨hle', ?_, ?_⟩
  · have h2 : ((dig 256 V a + 2 ^ (256 - 1) - dig 256 V b : ℕ) : ℤ) < 2 ^ 256 := by
      rw [Nat.cast_sub hle']
      push_cast
      norm_num at ha hb ⊢
      linarith [ha.2, hb.1]
    exact_mod_cast h2
  · rw [Nat.cast_sub hle']
    push_cast
    ring

theorem partnerCheck_sound (m V P : ℕ) (hV : ∀ x < m * m * m, |ent 256 (256 - 1) V x| ≤ 2 ^ 90)
    (hc : partnerCheck m V P = true) :
    P < 2 ^ (256 * (m * m * m)) ∧ (∀ x < m * m * m, |ent 256 (256 - 1) P x| ≤ 2 ^ 91) ∧
      ∀ x < m * m * m, ent 256 (256 - 1) P x =
        ent 256 (256 - 1) V (rotA m x) - ent 256 (256 - 1) V (rotB m x) := by
  unfold partnerCheck at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨heq, hbd⟩ := hc
  obtain ⟨hlt, hb⟩ := slotBoundCheck_sound 256 91 _ P (by norm_num) hbd
  refine ⟨hlt, hb, fun x hx => ?_⟩
  have hP := Nat.eq_of_beq_eq_true heq
  have hall : ∀ f ∈ (List.range (m * m * m)).map
      (fun x => digS 256 V (rotA m x) + 2 ^ (256 - 1) - digS 256 V (rotB m x)), f < 2 ^ (256 * 1) := by
    intro f hf
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hf
    have hy' := List.mem_range.mp hy
    rw [mul_one, digS_eq, digS_eq]
    exact (partner_slot V _ _ (hV _ (rot_lt m y hy').1) (hV _ (rot_lt m y hy').2)).2.1
  have hdg := concatFibers_dig 256 1 _ hall x 0 (by simpa using hx) (by norm_num)
  rw [mul_one, add_zero, ← hP] at hdg
  rw [List.getD_eq_getElem _ _ (by simpa using hx), List.getElem_map, List.getElem_range, digS_eq, digS_eq] at hdg
  obtain ⟨_, hlt2, hval⟩ := partner_slot V _ _ (hV _ (rot_lt m x hx).1) (hV _ (rot_lt m x hx).2)
  rw [dig_one_zero 256 _ hlt2] at hdg
  unfold ent at hval ⊢
  rw [hdg]
  exact hval

/-- The hypotheses of a degree-2 trial key (equal site types), with checked partner columns. -/
def trial2KeyOK (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (n : ℕ) (GJcols Fcols Vcols Pcols : List ℕ) : Prop :=
  N k = ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ)) *
      ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ))ᵀ ∧
    x2KeyDegree s k = 2 ∧ x2KeyMult s k 0 = x2KeyMult s k 1 ∧ x2KeyMult s k 1 = x2KeyMult s k 2 ∧
    1 ≤ x2KeyMult s k 0 ∧
    glRowOK s (x2KeyTypes s k 0) (x2KeyMult s k 0) 512 = true ∧
    glRowOK s (x2KeyTypes s k 1) (x2KeyMult s k 1) 512 = true ∧
    glRowOK s (x2KeyTypes s k 2) (x2KeyMult s k 2) 512 = true ∧
    GJcols.length = x2KeySize s k ∧ x2KeySize s k ≤ 512 ∧
    (∀ d < x2KeySize s k, gjCheck 256 s (x2KeyTypes s k 0) (x2KeyTypes s k 1) (x2KeyTypes s k 2)
      (x2KeyMult s k 0) (x2KeyMult s k 1) (x2KeyMult s k 2) (x2JCols (x2KeyGlobal s k) d) (GJcols.getD d 0) = true) ∧
    (∀ c < n, vCheck 256 (x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2) (x2KeySize s k) GJcols
      (Fcols.getD c 0) (Vcols.getD c 0) = true) ∧
    Vcols.length = n ∧ Pcols.length = n ∧
    (∀ c < n, partnerCheck (x2KeyMult s k 0) (Vcols.getD c 0) (Pcols.getD c 0) = true)

/-- The lookup of a degree-2 trial key through `GJ F` and its rotations. -/
theorem x2Lookup_trial2_sum (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (n : ℕ) (Fcols : List ℕ)
    (hN : N k = ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ)) *
      ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ))ᵀ)
    (hdeg : x2KeyDegree s k = 2) (hpq : x2KeyMult s k 0 = x2KeyMult s k 1)
    (hqr : x2KeyMult s k 1 = x2KeyMult s k 2) (a b : Fin 3 → ℕ) :
    x2Lookup (x2InputBlock x2DataConcrete s N k) a b =
      (1 / 2 ^ 160 : ℚ) * ∑ c : Fin n,
        (x2Get3 (x2GF s k n Fcols) (a 0) (a 1) (a 2) c * x2Get3 (x2GF s k n Fcols) (b 0) (b 1) (b 2) c +
          (1 / 3 : ℚ) * ((x2Get3 (x2GF s k n Fcols) (a 2) (a 0) (a 1) c -
              x2Get3 (x2GF s k n Fcols) (a 1) (a 2) (a 0) c) *
            (x2Get3 (x2GF s k n Fcols) (b 2) (b 0) (b 1) c - x2Get3 (x2GF s k n Fcols) (b 1) (b 2) (b 0) c))) := by
  have hN' : N k = ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ)) *
      ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ))ᵀ +
      (0 : Matrix (x2Col s k) (Fin 0) ℚ) * (0 : Matrix (Fin 0) (Fin 0) ℚ) * (0 : Matrix (x2Col s k) (Fin 0) ℚ)ᵀ := by
    rw [hN]
    simp
  rw [x2Lookup_inputBlock_gram x2DataConcrete s N k _ _ _ hN' a b, if_pos hdeg]
  unfold x2GramPart
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, x2Get3_partner _ hpq hqr, Matrix.mul_smul,
    x2Get3_smul]
  unfold x2GF
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  ring

theorem keyOK_of_trial2 (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (n L : ℕ) (GJcols Fcols Vcols Pcols : List ℕ)
    (hL : x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2 = L)
    (h : trial2KeyOK s N k n GJcols Fcols Vcols Pcols) :
    keyOK L s N k (ibFS [(Vcols, Vcols, 94810963968000), (Pcols, Pcols, 31603654656000)]) := by
  obtain ⟨hN, hdeg, hm01, hm12, h0, hr0, hr1, hr2, hlen, hsz, hchk, hv, hVlen, hPlen, hp⟩ := h
  have h1 : 1 ≤ x2KeyMult s k 1 := by rw [← hm01]; exact h0
  have h2 : 1 ≤ x2KeyMult s k 2 := by rw [← hm12]; exact h1
  have hGJ := gj_bounds s k GJcols h0 h1 h2 hr0 hr1 hr2 hchk
  have hamb : x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2 =
      x2KeyMult s k 0 * x2KeyMult s k 0 * x2KeyMult s k 0 := by
    rw [← hm12, ← hm01]
  have hV : ∀ c < n, Vcols.getD c 0 < 2 ^ (256 * L) ∧
      ∀ x < x2KeyMult s k 0 * x2KeyMult s k 0 * x2KeyMult s k 0, |ent 256 (256 - 1) (Vcols.getD c 0) x| ≤ 2 ^ 90 := by
    intro c hc
    obtain ⟨hl, hb, _⟩ := vCheck_sound 256 _ _ GJcols _ _ (by norm_num) hlen hsz hGJ (hv c hc)
    rw [hL] at hl
    rw [hamb] at hb
    exact ⟨hl, hb⟩
  have hP : ∀ c < n, Pcols.getD c 0 < 2 ^ (256 * L) ∧
      (∀ x < x2KeyMult s k 0 * x2KeyMult s k 0 * x2KeyMult s k 0, |ent 256 (256 - 1) (Pcols.getD c 0) x| ≤ 2 ^ 91) ∧
      ∀ x < x2KeyMult s k 0 * x2KeyMult s k 0 * x2KeyMult s k 0, ent 256 (256 - 1) (Pcols.getD c 0) x =
        ent 256 (256 - 1) (Vcols.getD c 0) (rotA (x2KeyMult s k 0) x) -
          ent 256 (256 - 1) (Vcols.getD c 0) (rotB (x2KeyMult s k 0) x) := by
    intro c hc
    obtain ⟨hl, hb, hval⟩ := partnerCheck_sound (x2KeyMult s k 0) _ _ (hV c hc).2 (hp c hc)
    refine ⟨?_, hb, hval⟩
    rw [← hL, hamb]
    exact hl
  have hkf : kflat (x2KeyMult s k 1) (x2KeyMult s k 2) = kflat (x2KeyMult s k 0) (x2KeyMult s k 0) := by
    rw [← hm12, ← hm01]
  -- the factor columns at natural coordinates
  have eV : ∀ (c : Fin n) (y0 y1 y2 : ℕ), y0 < x2KeyMult s k 0 → y1 < x2KeyMult s k 0 → y2 < x2KeyMult s k 0 →
      x2Get3 (x2GF s k n Fcols) y0 y1 y2 c =
        (ent 256 (256 - 1) (Vcols.getD c 0) (kflat (x2KeyMult s k 0) (x2KeyMult s k 0) y0 y1 y2) : ℚ) := by
    intro c y0 y1 y2 hy0 hy1 hy2
    have e := x2V_get3_cols 256 s k n GJcols Fcols Vcols (by norm_num) h0 h1 h2 hr0 hr1 hr2 hlen hsz hchk hv
      y0 y1 y2 hy0 (by rw [← hm01]; exact hy1) (by rw [← hm12, ← hm01]; exact hy2) c
    unfold x2GF
    rw [e, hkf]
  constructor
  · intro a b ha0 ha1 ha2 hb0 hb1 hb2
    have ha1' : a 1 < x2KeyMult s k 0 := by rw [hm01]; exact ha1
    have ha2' : a 2 < x2KeyMult s k 0 := by rw [hm01, hm12]; exact ha2
    have hb1' : b 1 < x2KeyMult s k 0 := by rw [hm01]; exact hb1
    have hb2' : b 2 < x2KeyMult s k 0 := by rw [hm01, hm12]; exact hb2
    have hxa : kflat (x2KeyMult s k 0) (x2KeyMult s k 0) (a 0) (a 1) (a 2) <
        x2KeyMult s k 0 * x2KeyMult s k 0 * x2KeyMult s k 0 := by
      have := site_idx_lt (x2KeyMult s k 0) (x2KeyMult s k 0) (x2KeyMult s k 0) _ _ _ ha0 ha1' ha2'
      unfold kflat
      calc _ < x2KeyMult s k 0 * (x2KeyMult s k 0 * x2KeyMult s k 0) := this
        _ = _ := by ring
    have hxb : kflat (x2KeyMult s k 0) (x2KeyMult s k 0) (b 0) (b 1) (b 2) <
        x2KeyMult s k 0 * x2KeyMult s k 0 * x2KeyMult s k 0 := by
      have := site_idx_lt (x2KeyMult s k 0) (x2KeyMult s k 0) (x2KeyMult s k 0) _ _ _ hb0 hb1' hb2'
      unfold kflat
      calc _ < x2KeyMult s k 0 * (x2KeyMult s k 0 * x2KeyMult s k 0) := this
        _ = _ := by ring
    obtain ⟨ra1, ra2⟩ := rot_kflat (x2KeyMult s k 0) (a 0) (a 1) (a 2) ha1' ha2'
    obtain ⟨rb1, rb2⟩ := rot_kflat (x2KeyMult s k 0) (b 0) (b 1) (b 2) hb1' hb2'
    rw [x2Lookup_trial2_sum s N k n Fcols hN hdeg hm01 hm12 a b, hkf, ibFS_cons, ibIB_append,
      ibIB_pair _ _ _ Vcols Vcols rfl, ibIB_pair _ _ _ Pcols Pcols rfl, hVlen, hPlen, ← Finset.sum_add_distrib,
      Finset.sum_range, Int.cast_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [eV c (a 0) (a 1) (a 2) ha0 ha1' ha2', eV c (b 0) (b 1) (b 2) hb0 hb1' hb2',
      eV c (a 2) (a 0) (a 1) ha2' ha0 ha1', eV c (a 1) (a 2) (a 0) ha1' ha2' ha0,
      eV c (b 2) (b 0) (b 1) hb2' hb0 hb1', eV c (b 1) (b 2) (b 0) hb1' hb2' hb0,
      (hP c c.isLt).2.2 _ hxa, (hP c c.isLt).2.2 _ hxb, ra1, ra2, rb1, rb2]
    push_cast
    ring
  · intro p hp'
    rw [ibFS_cons, List.mem_append] at hp'
    have hLm : L = x2KeyMult s k 0 * x2KeyMult s k 0 * x2KeyMult s k 0 := by rw [← hL, hamb]
    rcases hp' with hp' | hp'
    · obtain ⟨c, hc, _, rfl⟩ := mem_ibFS_single Vcols Vcols 94810963968000 p hp'
      rw [hVlen] at hc
      obtain ⟨hl, hb⟩ := hV c hc
      refine ⟨hl, hl, by norm_num, fun x hx y hy => ?_⟩
      rw [hLm] at hx hy
      have e1 := hb x hx
      have e2 := hb y hy
      rw [abs_mul, abs_mul]
      calc |((94810963968000 : ℕ) : ℤ)| * |ent 256 (256 - 1) (Vcols.getD c 0) x| *
            |ent 256 (256 - 1) (Vcols.getD c 0) y|
          ≤ 94810963968000 * 2 ^ 90 * 2 ^ 90 := by
            have e0 : |((94810963968000 : ℕ) : ℤ)| = 94810963968000 := by norm_num
            rw [e0]
            exact mul_le_mul (mul_le_mul_of_nonneg_left e1 (by norm_num)) e2 (abs_nonneg _) (by positivity)
        _ ≤ 2 ^ 227 := by norm_num
    · obtain ⟨c, hc, _, rfl⟩ := mem_ibFS_single Pcols Pcols 31603654656000 p hp'
      rw [hPlen] at hc
      obtain ⟨hl, hb, _⟩ := hP c hc
      refine ⟨hl, hl, by norm_num, fun x hx y hy => ?_⟩
      rw [hLm] at hx hy
      have e1 := hb x hx
      have e2 := hb y hy
      rw [abs_mul, abs_mul]
      calc |((31603654656000 : ℕ) : ℤ)| * |ent 256 (256 - 1) (Pcols.getD c 0) x| *
            |ent 256 (256 - 1) (Pcols.getD c 0) y|
          ≤ 31603654656000 * 2 ^ 91 * 2 ^ 91 := by
            have e0 : |((31603654656000 : ℕ) : ℤ)| = 31603654656000 := by norm_num
            rw [e0]
            exact mul_le_mul (mul_le_mul_of_nonneg_left e1 (by norm_num)) e2 (abs_nonneg _) (by positivity)
        _ ≤ 2 ^ 227 := by norm_num

/-! #### Corrected keys (light form `K (A / den_c) Kᵀ`) -/

/-- The square integer matrix with packed columns `Acols` (256-bit slots, offset `2^255`):
entry `(c, c')` is slot `c` of column `c'`. -/
def x2AMatOf (kd : ℕ) (Acols : List ℕ) : Matrix (Fin kd) (Fin kd) ℤ :=
  Matrix.of fun c c' => ent 256 (256 - 1) (Acols.getD c' 0) c

/-- Column `c'` of `U A`: one natural linear combination of the `U` columns with the slots of column `c'` of
`A` as offset scalars; slot bounds `2^196` on `A` and `2^204` on the result. -/
noncomputable def uaCheck (L kd : ℕ) (Ucols : List ℕ) (Acol UAcol : ℕ) : Bool :=
  slotBoundCheck 256 196 kd Acol && natAxpyCheck 256 L 255 (digs 256 kd Acol) Ucols UAcol (natAxpyCorr 256 L 255 Ucols) &&
    slotBoundCheck 256 204 L UAcol

theorem uaCheck_sound (L kd : ℕ) (Ucols : List ℕ) (Acol UAcol : ℕ) (hlen : Ucols.length = kd) (hkd : kd ≤ 512)
    (hU : ∀ c < kd, Ucols.getD c 0 < 2 ^ (256 * L) ∧ ∀ x < L, |ent 256 (256 - 1) (Ucols.getD c 0) x| ≤ 2 ^ 18)
    (h : uaCheck L kd Ucols Acol UAcol = true) :
    UAcol < 2 ^ (256 * L) ∧ (∀ x < L, |ent 256 (256 - 1) UAcol x| ≤ 2 ^ 204) ∧
      ∀ x < L, ent 256 (256 - 1) UAcol x =
        ∑ c : Fin kd, ent 256 (256 - 1) Acol c * ent 256 (256 - 1) (Ucols.getD c 0) x := by
  unfold uaCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hA, hax⟩, hbd⟩ := h
  obtain ⟨_, hAb⟩ := slotBoundCheck_sound 256 196 kd Acol (by norm_num) hA
  obtain ⟨hlt, hbnd⟩ := slotBoundCheck_sound 256 204 L UAcol (by norm_num) hbd
  have hsum : ∀ x, lincomb 256 (sScalars 255 (digs 256 kd Acol)) Ucols x =
      ∑ c : Fin kd, ent 256 (256 - 1) Acol c * ent 256 (256 - 1) (Ucols.getD c 0) x := by
    intro x
    rw [lincomb_getD 256 255 kd x _ _ (digs_length 256 kd Acol) hlen]
    apply Finset.sum_congr rfl
    intro c _
    rw [digs_getD 256 kd Acol c c.isLt]
    rfl
  have hmem : ∀ E ∈ Ucols, E < 2 ^ (256 * L) := by
    intro E hE
    obtain ⟨d, hd, rfl⟩ := List.getElem_of_mem hE
    have := (hU d (by omega)).1
    rwa [List.getD_eq_getElem _ _ hd] at this
  have hlin : ∀ x < L, |lincomb 256 (sScalars 255 (digs 256 kd Acol)) Ucols x| < 2 ^ (256 - 1) := by
    intro x hx
    rw [hsum]
    calc |∑ c : Fin kd, ent 256 (256 - 1) Acol c * ent 256 (256 - 1) (Ucols.getD c 0) x|
        ≤ ∑ c : Fin kd, |ent 256 (256 - 1) Acol c * ent 256 (256 - 1) (Ucols.getD c 0) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _c : Fin kd, (2 ^ 196 * 2 ^ 18 : ℤ) := by
          apply Finset.sum_le_sum
          intro c _
          rw [abs_mul]
          have h1 := hAb c c.isLt
          norm_num at h1 ⊢
          exact mul_le_mul h1 ((hU c c.isLt).2 x hx) (abs_nonneg _) (by positivity)
      _ = (kd : ℤ) * (2 ^ 196 * 2 ^ 18) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
      _ < 2 ^ (256 - 1) := by
          have hk' : (kd : ℤ) ≤ 2 ^ 9 := by exact_mod_cast (show kd ≤ 2 ^ 9 by omega)
          have h2 : (2 : ℤ) ^ 9 * (2 ^ 196 * 2 ^ 18) < 2 ^ (256 - 1) := by norm_num
          nlinarith
  refine ⟨hlt, hbnd, ?_⟩
  intro x hx
  rw [← natAxpyCheck_sound 256 L 255 _ Ucols UAcol (by norm_num) (by rw [digs_length, hlen]) hmem hlin hax x hx, hsum]

/-- The hypotheses of a corrected key in the light form `N k = K (A / den_c) Kᵀ`, with checked `U = GJ K`
and `UA = U A` columns. -/
def corrKeyOK (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (kd : ℕ) (GJcols Kcols Ucols Acols UAcols : List ℕ) :
    Prop :=
  N k = (x2FactorOf (x2KeySize s k) kd Kcols).map (Int.cast : ℤ → ℚ) *
      ((1 / (46188793025384413423571871319830538981162952029845382496256000 : ℚ)) •
        (x2AMatOf kd Acols).map (Int.cast : ℤ → ℚ)) *
      ((x2FactorOf (x2KeySize s k) kd Kcols).map (Int.cast : ℤ → ℚ))ᵀ ∧
    x2KeyDegree s k ≠ 2 ∧
    1 ≤ x2KeyMult s k 0 ∧ 1 ≤ x2KeyMult s k 1 ∧ 1 ≤ x2KeyMult s k 2 ∧
    glRowOK s (x2KeyTypes s k 0) (x2KeyMult s k 0) 512 = true ∧
    glRowOK s (x2KeyTypes s k 1) (x2KeyMult s k 1) 512 = true ∧
    glRowOK s (x2KeyTypes s k 2) (x2KeyMult s k 2) 512 = true ∧
    GJcols.length = x2KeySize s k ∧ x2KeySize s k ≤ 512 ∧
    (∀ d < x2KeySize s k, gjCheck 256 s (x2KeyTypes s k 0) (x2KeyTypes s k 1) (x2KeyTypes s k 2)
      (x2KeyMult s k 0) (x2KeyMult s k 1) (x2KeyMult s k 2) (x2JCols (x2KeyGlobal s k) d) (GJcols.getD d 0) = true) ∧
    (∀ c < kd, vCheck 256 (x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2) (x2KeySize s k) GJcols
      (Kcols.getD c 0) (Ucols.getD c 0) = true ∧
      slotBoundCheck 256 18 (x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2) (Ucols.getD c 0) = true) ∧
    Ucols.length = kd ∧ UAcols.length = kd ∧ kd ≤ 512 ∧
    (∀ c < kd, uaCheck (x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2) kd Ucols (Acols.getD c 0)
      (UAcols.getD c 0) = true)

theorem keyOK_of_corr (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (kd L : ℕ) (GJcols Kcols Ucols Acols UAcols : List ℕ)
    (hL : x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2 = L)
    (h : corrKeyOK s N k kd GJcols Kcols Ucols Acols UAcols) :
    keyOK L s N k (ibFS [(UAcols, Ucols, 3)]) := by
  obtain ⟨hN, hdeg, h0, h1, h2, hr0, hr1, hr2, hlen, hsz, hchk, hu, hUlen, hUAlen, hkd, hua⟩ := h
  have hGJ := gj_bounds s k GJcols h0 h1 h2 hr0 hr1 hr2 hchk
  have hU : ∀ c < kd, Ucols.getD c 0 < 2 ^ (256 * (x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2)) ∧
      ∀ x < x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2, |ent 256 (256 - 1) (Ucols.getD c 0) x| ≤ 2 ^ 18 := by
    intro c hc
    obtain ⟨hl, _, _⟩ := vCheck_sound 256 _ _ GJcols _ _ (by norm_num) hlen hsz hGJ (hu c hc).1
    exact ⟨hl, (slotBoundCheck_sound 256 18 _ _ (by norm_num) (hu c hc).2).2⟩
  have hUA : ∀ c < kd, UAcols.getD c 0 < 2 ^ (256 * (x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2)) ∧
      (∀ x < x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2, |ent 256 (256 - 1) (UAcols.getD c 0) x| ≤ 2 ^ 204) ∧
      ∀ x < x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2, ent 256 (256 - 1) (UAcols.getD c 0) x =
        ∑ c' : Fin kd, ent 256 (256 - 1) (Acols.getD c 0) c' * ent 256 (256 - 1) (Ucols.getD c' 0) x :=
    fun c hc => uaCheck_sound _ kd Ucols _ _ hUlen hkd hU (hua c hc)
  constructor
  · intro a b ha0 ha1 ha2 hb0 hb1 hb2
    have hN' : N k = (0 : Matrix (x2Col s k) (Fin 0) ℚ) * (0 : Matrix (x2Col s k) (Fin 0) ℚ)ᵀ +
        (x2FactorOf (x2KeySize s k) kd Kcols).map (Int.cast : ℤ → ℚ) *
          ((1 / (46188793025384413423571871319830538981162952029845382496256000 : ℚ)) •
            (x2AMatOf kd Acols).map (Int.cast : ℤ → ℚ)) *
          ((x2FactorOf (x2KeySize s k) kd Kcols).map (Int.cast : ℤ → ℚ))ᵀ := by
      rw [hN]
      simp
    rw [x2Lookup_inputBlock_gram x2DataConcrete s N k _ _ _ hN' a b, if_neg hdeg, add_zero]
    unfold x2GramPart
    have eU : ∀ (c : Fin kd) (y0 y1 y2 : ℕ), y0 < x2KeyMult s k 0 → y1 < x2KeyMult s k 1 → y2 < x2KeyMult s k 2 →
        x2Get3 (x2GJ x2DataConcrete s k * (x2FactorOf (x2KeySize s k) kd Kcols).map (Int.cast : ℤ → ℚ)) y0 y1 y2 c =
          (ent 256 (256 - 1) (Ucols.getD c 0) (kflat (x2KeyMult s k 1) (x2KeyMult s k 2) y0 y1 y2) : ℚ) :=
      fun c y0 y1 y2 hy0 hy1 hy2 => x2V_get3_cols 256 s k kd GJcols Kcols Ucols (by norm_num) h0 h1 h2 hr0 hr1 hr2
        hlen hsz hchk (fun c hc => (hu c hc).1) y0 y1 y2 hy0 hy1 hy2 c
    have hxa : kflat (x2KeyMult s k 1) (x2KeyMult s k 2) (a 0) (a 1) (a 2) <
        x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2 := by
      have := site_idx_lt _ _ _ _ _ _ ha0 ha1 ha2
      unfold kflat
      calc _ < x2KeyMult s k 0 * (x2KeyMult s k 1 * x2KeyMult s k 2) := this
        _ = _ := by ring
    rw [Fin.sum_univ_zero, zero_add, ibIB_pair _ _ _ UAcols Ucols (by rw [hUlen, hUAlen]), hUAlen,
      Finset.sum_range, Int.cast_sum, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c' _ => ?_)
    rw [(hUA c' c'.isLt).2.2 _ hxa, Int.cast_mul, Int.cast_mul, Int.cast_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [eU c (a 0) (a 1) (a 2) ha0 ha1 ha2, eU c' (b 0) (b 1) (b 2) hb0 hb1 hb2, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul]
    simp only [x2AMatOf, Matrix.of_apply]
    push_cast
    ring
  · intro p hp
    obtain ⟨c, hc, _, rfl⟩ := mem_ibFS_single UAcols Ucols 3 p hp
    rw [hUAlen] at hc
    obtain ⟨hl1, hb1, _⟩ := hUA c hc
    obtain ⟨hl2, hb2⟩ := hU c hc
    rw [hL] at hl1 hl2 hb1 hb2
    refine ⟨hl1, hl2, by norm_num, fun x hx y hy => ?_⟩
    have e1 := hb1 x hx
    have e2 := hb2 y hy
    rw [abs_mul, abs_mul]
    calc |((3 : ℕ) : ℤ)| * |ent 256 (256 - 1) (UAcols.getD c 0) x| * |ent 256 (256 - 1) (Ucols.getD c 0) y|
        ≤ 3 * 2 ^ 204 * 2 ^ 18 := by
          have e0 : |((3 : ℕ) : ℤ)| = 3 := by norm_num
          rw [e0]
          exact mul_le_mul (mul_le_mul_of_nonneg_left e1 (by norm_num)) e2 (abs_nonneg _) (by positivity)
      _ ≤ 2 ^ 227 := by norm_num

/-! ### The key sum of a triple -/

theorem sum_keyIB (s : Fin 3) (N : X2Blocks s) (t : Fin 3 → Fin 8) (a b : Fin 3 → ℕ)
    (ha0 : a 0 < x2Mult s (t 0)) (ha1 : a 1 < x2Mult s (t 1)) (ha2 : a 2 < x2Mult s (t 2))
    (hb0 : b 0 < x2Mult s (t 0)) (hb1 : b 1 < x2Mult s (t 1)) (hb2 : b 2 < x2Mult s (t 2)) :
    ∀ L : List (x2Key s × List (ℕ × ℕ × ℕ)), (∀ e ∈ L, x2KeyTypes s e.1 = t ∧ keyIB s N e.1 e.2) →
      (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) *
          (L.map (fun e => x2Lookup (x2InputBlock x2DataConcrete s N e.1) a b)).sum =
        (ibIB 256 (L.flatMap Prod.snd) (kflat (x2Mult s (t 1)) (x2Mult s (t 2)) (a 0) (a 1) (a 2))
          (kflat (x2Mult s (t 1)) (x2Mult s (t 2)) (b 0) (b 1) (b 2)) : ℚ)
  | [], _ => by simp [ibIB]
  | e :: L, h => by
    obtain ⟨ht, hk⟩ := h e (by simp)
    have ih := sum_keyIB s N t a b ha0 ha1 ha2 hb0 hb1 hb2 L (fun e' he' => h e' (by simp [he']))
    have hm : ∀ i, x2KeyMult s e.1 i = x2Mult s (t i) := fun i => by
      show x2Mult s (x2KeyTypes s e.1 i) = x2Mult s (t i)
      rw [ht]
    have he := hk a b (by rw [hm]; exact ha0) (by rw [hm]; exact ha1) (by rw [hm]; exact ha2)
      (by rw [hm]; exact hb0) (by rw [hm]; exact hb1) (by rw [hm]; exact hb2)
    have he' : (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) *
        x2Lookup (x2InputBlock x2DataConcrete s N e.1) a b =
        (ibIB 256 e.2 (kflat (x2Mult s (t 1)) (x2Mult s (t 2)) (a 0) (a 1) (a 2))
          (kflat (x2Mult s (t 1)) (x2Mult s (t 2)) (b 0) (b 1) (b 2)) : ℚ) :=
      he.trans (by rw [hm 1, hm 2])
    rw [List.map_cons, List.sum_cons, mul_add, he', ih, List.flatMap_cons, ibIB_append, Int.cast_add]

/-- `3 den_c ×` the key sum of a type triple is the `ibIB` of the concatenated parts of its keys. -/
theorem x2KeySum_ib (s : Fin 3) (N : X2Blocks s) (t : Fin 3 → Fin 8) (ks : List (x2Key s × List (ℕ × ℕ × ℕ)))
    (hks : ∀ k : x2Key s, x2KeyTypes s k = t ↔ k ∈ ks.map Prod.fst) (hnd : (ks.map Prod.fst).Nodup)
    (hok : ∀ e ∈ ks, keyIB s N e.1 e.2) (a b : Fin 3 → ℕ)
    (ha0 : a 0 < x2Mult s (t 0)) (ha1 : a 1 < x2Mult s (t 1)) (ha2 : a 2 < x2Mult s (t 2))
    (hb0 : b 0 < x2Mult s (t 0)) (hb1 : b 1 < x2Mult s (t 1)) (hb2 : b 2 < x2Mult s (t 2)) :
    (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) * x2KeySum s N t a b =
      (ibIB 256 (ks.flatMap Prod.snd) (kflat (x2Mult s (t 1)) (x2Mult s (t 2)) (a 0) (a 1) (a 2))
        (kflat (x2Mult s (t 1)) (x2Mult s (t 2)) (b 0) (b 1) (b 2)) : ℚ) := by
  rw [x2KeySum_list s N t (ks.map Prod.fst) hks hnd a b, List.map_map]
  exact sum_keyIB s N t a b ha0 ha1 ha2 hb0 hb1 hb2 ks
    (fun e he => ⟨(hks e.1).mpr (List.mem_map.mpr ⟨e, he, rfl⟩), hok e he⟩)

/-! ### Stored upper blocks in a nested table -/

/-- Block `(b₀, b₁)` of row-batch `(a₀, a₁)`. -/
def UBget (UBT : List (List (List (List ℕ)))) (a0 a1 b0 b1 : ℕ) : ℕ :=
  (((UBT.getD a0 []).getD a1 []).getD b0 []).getD b1 0

theorem flatten_length_of (m1 : ℕ) : ∀ (L : List (List ℕ)), (∀ l ∈ L, l.length = m1) →
    L.flatten.length = L.length * m1
  | [], _ => by simp
  | l :: L, h => by
    rw [List.flatten_cons, List.length_append, h l (by simp),
      flatten_length_of m1 L (fun l' hl' => h l' (by simp [hl'])), List.length_cons]
    ring

theorem flatten_getD_of (m1 : ℕ) : ∀ (L : List (List ℕ)), (∀ l ∈ L, l.length = m1) →
    ∀ b0 b1, b0 < L.length → b1 < m1 → L.flatten.getD (b0 * m1 + b1) 0 = (L.getD b0 []).getD b1 0
  | [], _, b0, b1, hb0, _ => by simp at hb0
  | l :: L, h, b0, b1, hb0, hb1 => by
    have hl := h l (by simp)
    rw [List.flatten_cons]
    cases b0 with
    | zero =>
      rw [zero_mul, zero_add, List.getD_cons_zero, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
    | succ b0 =>
      have ih := flatten_getD_of m1 L (fun l' hl' => h l' (by simp [hl'])) b0 b1 (by simpa using hb0) hb1
      have hidx : (b0 + 1) * m1 + b1 - m1 = b0 * m1 + b1 := by rw [Nat.succ_mul]; omega
      rw [List.getD_cons_succ, ← ih, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [hl]; nlinarith), hl, hidx]

theorem ubSpec (L m0 m1 m2 : ℕ) (fs : List (ℕ × ℕ × ℕ)) (UBT : List (List (List (List ℕ))))
    (hm2 : 1 ≤ m2) (hL : L = m0 * m1 * m2)
    (hparts : ∀ p ∈ fs, partBound L p) (hlen : fs.length < 2 ^ 27)
    (hshape : ∀ a0 < m0, ∀ a1 < m1, ((UBT.getD a0 []).getD a1 []).length = m0 ∧
      ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = m1)
    (hchk : ∀ a0 < m0, ∀ a1 < m1, ibBatchOK 256 L 302 m2 (m0 * m1) 0 m2 ((a0 * m1 + a1) * m2) fs
      ((UBT.getD a0 []).getD a1 []).flatten = true) :
    ∀ a0 < m0, ∀ a1 < m1, ∀ b0 < m0, ∀ b1 < m1, ∀ a2 b2 : ℕ, a2 ≤ b2 → b2 < m2 →
      ent 256 (256 - 1) (UBget UBT a0 a1 b0 b1) (upos m2 a2 b2) =
        ibIB 256 fs (kflat m1 m2 a0 a1 a2) (kflat m1 m2 b0 b1 b2) := by
  intro a0 ha0 a1 ha1 b0 hb0 b1 hb1 a2 b2 hab hb2
  obtain ⟨hl0, hl1⟩ := hshape a0 ha0 a1 ha1
  have hfs : ∀ p ∈ fs, p.2.1 < 2 ^ (256 * L) ∧ p.2.2 * 2 ^ (256 - 1) ≤ 2 ^ 302 :=
    fun p hp => ⟨(hparts p hp).2.1, (hparts p hp).2.2.1⟩
  have hlin : ∀ i < m2, ∀ k < L, |ibIB 256 fs ((a0 * m1 + a1) * m2 + i) k| < 2 ^ (256 - 1) := by
    intro i hi k hk
    have hx : (a0 * m1 + a1) * m2 + i < L := by
      rw [hL]
      have := site_idx_lt m0 m1 m2 a0 a1 i ha0 ha1 hi
      calc _ < m0 * (m1 * m2) := this
        _ = m0 * m1 * m2 := by ring
    have hb := ibIB_abs_le_parts L fs hparts _ hx k hk
    calc |ibIB 256 fs ((a0 * m1 + a1) * m2 + i) k| ≤ fs.length * 2 ^ 227 := hb
      _ < 2 ^ 27 * 2 ^ 227 := by
          have h27 : (fs.length : ℤ) < 2 ^ 27 := by exact_mod_cast hlen
          exact mul_lt_mul_of_pos_right h27 (by positivity)
      _ ≤ 2 ^ (256 - 1) := by norm_num
  have hflat : ((UBT.getD a0 []).getD a1 []).flatten.length = m0 * m1 := by
    rw [flatten_length_of m1 _ hl1, hl0]
  have hblk : b0 * m1 + b1 < m0 * m1 := by
    calc b0 * m1 + b1 < (b0 + 1) * m1 := by nlinarith
      _ ≤ m0 * m1 := Nat.mul_le_mul_right _ hb0
  have h := ibBatchOK_sound 256 L 302 m2 (m0 * m1) 0 m2 ((a0 * m1 + a1) * m2) fs _ (by norm_num) hm2 (by omega)
    (by rw [hL]) hflat hfs hlin (hchk a0 ha0 a1 ha1) a2 (by omega) (b0 * m1 + b1) hblk b2 (by omega) hb2
  rw [zero_add, flatten_getD_of m1 _ hl1 b0 b1 (by rw [hl0]; exact hb0) hb1] at h
  unfold UBget kflat
  rw [h]

/-! ### Labels -/

/-- Number of S labels of a type. -/
def nS (s : Fin 3) (u : Fin 8) : ℕ := x2Mult s u * (x2Mult s u + 1) / 2

/-- The `i`-th S label of type `u` (`i < nS s u`). -/
def slab (s : Fin 3) (u : Fin 8) (i : ℕ) : Fin 282 := ⟨(x2SOff s u + i) % 282, Nat.mod_lt _ (by norm_num)⟩

/-- The pairs `a ≤ b < m` in row-major upper-triangle order. -/
def pairsU (m : ℕ) : List (ℕ × ℕ) := (List.range m).flatMap (fun a => (List.range (m - a)).map (fun d => (a, a + d)))

/-- Kernel-checkable facts about `pairsU m`. -/
def pairsOK (m : ℕ) : Prop :=
  (pairsU m).length = m * (m + 1) / 2 ∧
    ∀ i < m * (m + 1) / 2, ((pairsU m).getD i (0, 0)).1 ≤ ((pairsU m).getD i (0, 0)).2 ∧
      ((pairsU m).getD i (0, 0)).2 < m ∧ upos m ((pairsU m).getD i (0, 0)).1 ((pairsU m).getD i (0, 0)).2 = i

/-- The S labels of a sector, type by type, in `pairsU` order. -/
def labelsOK (s : Fin 3) : Prop :=
  ∀ u : Fin 8, ∀ i < nS s u, x2SLabel s (slab s u i) = (u, (pairsU (x2Mult s u)).getD i (0, 0))

/-! ### T-blocks -/

/-- `σ · x2EmbedS` at the labels of a type triple, as T-table slots (rows by the second label). -/
def TTspecS (s : Fin 3) (N : X2Blocks s) (t0 t1 t2 : Fin 8) (TT : List (List ℕ)) : Prop :=
  ∀ i0 < nS s t0, ∀ i1 < nS s t1, ∀ i2 < nS s t2,
    (ent 256 (256 - 1) ((TT.getD i1 []).getD i0 0) i2 : ℚ) =
      1108531032609225922165724911675932935547910848716289179910144000 *
        x2EmbedS x2DataConcrete s N (slab s t0 i0) (slab s t1 i1) (slab s t2 i2)

/-- The same with rows by the first label. -/
def TCspecS (s : Fin 3) (N : X2Blocks s) (t0 t1 t2 : Fin 8) (TC : List (List ℕ)) : Prop :=
  ∀ i0 < nS s t0, ∀ i1 < nS s t1, ∀ i2 < nS s t2,
    (ent 256 (256 - 1) ((TC.getD i0 []).getD i1 0) i2 : ℚ) =
      1108531032609225922165724911675932935547910848716289179910144000 *
        x2EmbedS x2DataConcrete s N (slab s t0 i0) (slab s t1 i1) (slab s t2 i2)

/-- `x2EmbedS` vanishes at the labels of a type triple. -/
def ZspecS (s : Fin 3) (N : X2Blocks s) (t0 t1 t2 : Fin 8) : Prop :=
  ∀ i0 < nS s t0, ∀ i1 < nS s t1, ∀ i2 < nS s t2,
    x2EmbedS x2DataConcrete s N (slab s t0 i0) (slab s t1 i1) (slab s t2 i2) = 0

/-- One T-block check: `T = 2 (U₁ + U₂ + U₃ + U₄)` for the labels with pairs `p₀ = (a₀, b₀)`, `p₁ = (a₁, b₁)`. -/
noncomputable def tCell (UBT : List (List (List (List ℕ)))) (L2 : ℕ) (p0 p1 : ℕ × ℕ) (B : ℕ) : Bool :=
  t2Check 256 L2 6 6 6 6 (UBget UBT p0.1 p1.1 p0.2 p1.2) (UBget UBT p0.2 p1.1 p0.1 p1.2)
    (UBget UBT p0.1 p1.2 p0.2 p1.1) (UBget UBT p0.2 p1.2 p0.1 p1.1) B

/-- The T-blocks of a type triple from a generic accessor `Tget i₀ i₁`. -/
theorem ttSpecGen (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (t0 t1 t2 : Fin 8) (h01 : t0 ≤ t1) (h12 : t1 ≤ t2) (fs : List (ℕ × ℕ × ℕ))
    (UBT : List (List (List (List ℕ)))) (Tget : ℕ → ℕ → ℕ)
    (hlab : labelsOK s) (hp0 : pairsOK (x2Mult s t0)) (hp1 : pairsOK (x2Mult s t1)) (hp2 : pairsOK (x2Mult s t2))
    (hKS : ∀ x0 x1 x2 y0 y1 y2 : ℕ, x0 < x2Mult s t0 → x1 < x2Mult s t1 → x2 < x2Mult s t2 →
      y0 < x2Mult s t0 → y1 < x2Mult s t1 → y2 < x2Mult s t2 →
      (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) *
          x2KeySum s N ![t0, t1, t2] ![x0, x1, x2] ![y0, y1, y2] =
        (ibIB 256 fs (kflat (x2Mult s t1) (x2Mult s t2) x0 x1 x2) (kflat (x2Mult s t1) (x2Mult s t2) y0 y1 y2) : ℚ))
    (hU : ∀ a0 < x2Mult s t0, ∀ a1 < x2Mult s t1, ∀ b0 < x2Mult s t0, ∀ b1 < x2Mult s t1, ∀ a2 b2 : ℕ,
      a2 ≤ b2 → b2 < x2Mult s t2 →
      ent 256 (256 - 1) (UBget UBT a0 a1 b0 b1) (upos (x2Mult s t2) a2 b2) =
        ibIB 256 fs (kflat (x2Mult s t1) (x2Mult s t2) a0 a1 a2) (kflat (x2Mult s t1) (x2Mult s t2) b0 b1 b2))
    (hT : ∀ i0 < nS s t0, ∀ i1 < nS s t1, tCell UBT (nS s t2) ((pairsU (x2Mult s t0)).getD i0 (0, 0))
      ((pairsU (x2Mult s t1)).getD i1 (0, 0)) (Tget i0 i1) = true) :
    ∀ i0 < nS s t0, ∀ i1 < nS s t1, ∀ i2 < nS s t2,
      (ent 256 (256 - 1) (Tget i0 i1) i2 : ℚ) =
        1108531032609225922165724911675932935547910848716289179910144000 *
          x2EmbedS x2DataConcrete s N (slab s t0 i0) (slab s t1 i1) (slab s t2 i2) := by
  intro i0 hi0 i1 hi1 i2 hi2
  obtain ⟨_, hq0⟩ := hp0
  obtain ⟨_, hq1⟩ := hp1
  obtain ⟨_, hq2⟩ := hp2
  obtain ⟨hab0, hb0, hu0⟩ := hq0 i0 hi0
  obtain ⟨hab1, hb1, hu1⟩ := hq1 i1 hi1
  obtain ⟨hab2, hb2, hu2⟩ := hq2 i2 hi2
  have hl0 := hlab t0 i0 hi0
  have hl1 := hlab t1 i1 hi1
  have hl2 := hlab t2 i2 hi2
  have h8 := x2EmbedS_eight s hs N hN (slab s t0 i0) (slab s t1 i1) (slab s t2 i2)
    (by rw [hl0, hl1]; exact h01) (by rw [hl1, hl2]; exact h12)
  rw [hl0, hl1, hl2] at h8
  dsimp only at h8
  have hc := hT i0 hi0 i1 hi1
  unfold tCell at hc
  have ht := t2Check_sound 256 (nS s t2) 6 6 6 6 _ _ _ _ _ (by norm_num) (by norm_num) hc i2 hi2
  rw [ht]
  set a0 := ((pairsU (x2Mult s t0)).getD i0 (0, 0)).1 with ha0
  set b0 := ((pairsU (x2Mult s t0)).getD i0 (0, 0)).2 with hb0'
  set a1 := ((pairsU (x2Mult s t1)).getD i1 (0, 0)).1 with ha1
  set b1 := ((pairsU (x2Mult s t1)).getD i1 (0, 0)).2 with hb1'
  set a2 := ((pairsU (x2Mult s t2)).getD i2 (0, 0)).1 with ha2
  set b2 := ((pairsU (x2Mult s t2)).getD i2 (0, 0)).2 with hb2'
  have ha0l : a0 < x2Mult s t0 := lt_of_le_of_lt hab0 hb0
  have ha1l : a1 < x2Mult s t1 := lt_of_le_of_lt hab1 hb1
  have ha2l : a2 < x2Mult s t2 := lt_of_le_of_lt hab2 hb2
  have k1 := hKS a0 a1 a2 b0 b1 b2 ha0l ha1l ha2l hb0 hb1 hb2
  have k2 := hKS b0 a1 a2 a0 b1 b2 hb0 ha1l ha2l ha0l hb1 hb2
  have k3 := hKS a0 b1 a2 b0 a1 b2 ha0l hb1 ha2l hb0 ha1l hb2
  have k4 := hKS b0 b1 a2 a0 a1 b2 hb0 hb1 ha2l ha0l ha1l hb2
  have u1 := hU a0 ha0l a1 ha1l b0 hb0 b1 hb1 a2 b2 hab2 hb2
  have u2 := hU b0 hb0 a1 ha1l a0 ha0l b1 hb1 a2 b2 hab2 hb2
  have u3 := hU a0 ha0l b1 hb1 b0 hb0 a1 ha1l a2 b2 hab2 hb2
  have u4 := hU b0 hb0 b1 hb1 a0 ha0l a1 ha1l a2 b2 hab2 hb2
  rw [hu2] at u1 u2 u3 u4
  rw [← u1] at k1
  rw [← u2] at k2
  rw [← u3] at k3
  rw [← u4] at k4
  push_cast at k1 k2 k3 k4 ⊢
  linear_combination (-2 : ℚ) * k1 - 2 * k2 - 2 * k3 - 2 * k4 -
    (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) * h8

/-- Rows by the second label. -/
theorem ttSpecS_of (s : Fin 3) (N : X2Blocks s) (t0 t1 t2 : Fin 8) (TT : List (List ℕ))
    (h : ∀ i0 < nS s t0, ∀ i1 < nS s t1, ∀ i2 < nS s t2,
      (ent 256 (256 - 1) ((TT.getD i1 []).getD i0 0) i2 : ℚ) =
        1108531032609225922165724911675932935547910848716289179910144000 *
          x2EmbedS x2DataConcrete s N (slab s t0 i0) (slab s t1 i1) (slab s t2 i2)) : TTspecS s N t0 t1 t2 TT := h

/-- Rows by the first label, for two equal first types: the same table, by the label symmetry. -/
theorem tcSpec_of_tt_eq (s : Fin 3) (N : X2Blocks s) (t0 t2 : Fin 8) (TT : List (List ℕ))
    (h : TTspecS s N t0 t0 t2 TT) : TCspecS s N t0 t0 t2 TT := by
  intro i0 hi0 i1 hi1 i2 hi2
  rw [h i1 hi1 i0 hi0 i2 hi2, x2EmbedS_swap01]

/-- A triple whose keys contribute no part: `x2EmbedS` vanishes on its labels. -/
theorem zspecS_of_empty (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (t0 t1 t2 : Fin 8) (h01 : t0 ≤ t1) (h12 : t1 ≤ t2) (hlab : labelsOK s)
    (hp0 : pairsOK (x2Mult s t0)) (hp1 : pairsOK (x2Mult s t1)) (hp2 : pairsOK (x2Mult s t2))
    (hKS : ∀ x0 x1 x2 y0 y1 y2 : ℕ, x0 < x2Mult s t0 → x1 < x2Mult s t1 → x2 < x2Mult s t2 →
      y0 < x2Mult s t0 → y1 < x2Mult s t1 → y2 < x2Mult s t2 →
      x2KeySum s N ![t0, t1, t2] ![x0, x1, x2] ![y0, y1, y2] = 0) :
    ZspecS s N t0 t1 t2 := by
  intro i0 hi0 i1 hi1 i2 hi2
  obtain ⟨_, hq0⟩ := hp0
  obtain ⟨_, hq1⟩ := hp1
  obtain ⟨_, hq2⟩ := hp2
  obtain ⟨hab0, hb0, _⟩ := hq0 i0 hi0
  obtain ⟨hab1, hb1, _⟩ := hq1 i1 hi1
  obtain ⟨hab2, hb2, _⟩ := hq2 i2 hi2
  have hl0 := hlab t0 i0 hi0
  have hl1 := hlab t1 i1 hi1
  have hl2 := hlab t2 i2 hi2
  have h8 := x2EmbedS_eight s hs N hN (slab s t0 i0) (slab s t1 i1) (slab s t2 i2)
    (by rw [hl0, hl1]; exact h01) (by rw [hl1, hl2]; exact h12)
  rw [hl0, hl1, hl2] at h8
  dsimp only at h8
  have ha0 := lt_of_le_of_lt hab0 hb0
  have ha1 := lt_of_le_of_lt hab1 hb1
  have ha2 := lt_of_le_of_lt hab2 hb2
  rw [hKS _ _ _ _ _ _ ha0 ha1 ha2 hb0 hb1 hb2, hKS _ _ _ _ _ _ hb0 ha1 ha2 ha0 hb1 hb2,
    hKS _ _ _ _ _ _ ha0 hb1 ha2 hb0 ha1 hb2, hKS _ _ _ _ _ _ hb0 hb1 ha2 ha0 ha1 hb2] at h8
  linarith

/-- The key sum of a triple whose keys contribute no part vanishes. -/
theorem keySum_zero_of_empty (s : Fin 3) (N : X2Blocks s) (t : Fin 3 → Fin 8)
    (ks : List (x2Key s × List (ℕ × ℕ × ℕ)))
    (hks : ∀ k : x2Key s, x2KeyTypes s k = t ↔ k ∈ ks.map Prod.fst) (hnd : (ks.map Prod.fst).Nodup)
    (hok : ∀ e ∈ ks, keyIB s N e.1 e.2) (hempty : ks.flatMap Prod.snd = []) (a b : Fin 3 → ℕ)
    (ha0 : a 0 < x2Mult s (t 0)) (ha1 : a 1 < x2Mult s (t 1)) (ha2 : a 2 < x2Mult s (t 2))
    (hb0 : b 0 < x2Mult s (t 0)) (hb1 : b 1 < x2Mult s (t 1)) (hb2 : b 2 < x2Mult s (t 2)) :
    x2KeySum s N t a b = 0 := by
  have h := x2KeySum_ib s N t ks hks hnd hok a b ha0 ha1 ha2 hb0 hb1 hb2
  rw [hempty] at h
  simp only [ibIB, List.map_nil, List.sum_nil, Int.cast_zero, mul_eq_zero] at h
  rcases h with h | h
  · norm_num at h
  · exact h

end X2
end ThreeCopyQutritWerner
