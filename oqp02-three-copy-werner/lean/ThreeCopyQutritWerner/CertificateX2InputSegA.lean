module

public import ThreeCopyQutritWerner.CertificateX2InputTripA

@[expose] public section


/-!
# Input stage: the A-pipeline input table from T-tables

The A-pipeline input table `f0` (super-rows `r = j / 77`, entries `c`, slot `(j % 77) · 282 + i` holds
`σ · x2EmbedA i j c`; `i` an S label, `j`, `c` A labels) is checked segment by segment as in the S pipeline
(CertificateX2InputSeg): for an A column `c` (type `w`), the type `u` of `i` and the type `v` of `j`,
* `u ≥ v, w`: AAS, whole T-blocks over the S labels (`TTaas` rows by the second A label, `TCaas` by the first);
* `u < v, w`: SAA, gathered from `TTsaa` (rows by the A label of the middle site) at the A-pair positions `posA`;
* otherwise: ASA, gathered from `TCasa` (rows by the A label of the first site) at `posA`;
* triples without parts: zero runs.
-/

set_option maxRecDepth 100000
set_option exponentiation.threshold 1000000
set_option maxHeartbeats 0

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-! ### A-label facts -/

/-- The type of an A label by comparison with the A-type offsets. -/
def typeA (s : Fin 3) (c : ℕ) : Fin 8 :=
  if c < x2AOff s 1 then 0 else if c < x2AOff s 2 then 1 else if c < x2AOff s 3 then 2 else
  if c < x2AOff s 4 then 3 else if c < x2AOff s 5 then 4 else if c < x2AOff s 6 then 5 else
  if c < x2AOff s 7 then 6 else 7

def typeOKA (s : Fin 3) : Prop := ∀ l : Fin 231, typeA s l.val = (x2ALabel s l).1

def labelDecompA (s : Fin 3) : Prop :=
  ∀ l : Fin 231, x2AOff s (x2ALabel s l).1 ≤ l.val ∧ l.val - x2AOff s (x2ALabel s l).1 < nA s (x2ALabel s l).1 ∧
    alab s (x2ALabel s l).1 (l.val - x2AOff s (x2ALabel s l).1) = l

theorem labelsAOK_1 : labelsAOK 1 := by unfold labelsAOK; decide +kernel
theorem labelsAOK_2 : labelsAOK 2 := by unfold labelsAOK; decide +kernel
theorem labelDecompA_1 : labelDecompA 1 := by unfold labelDecompA; decide +kernel
theorem labelDecompA_2 : labelDecompA 2 := by unfold labelDecompA; decide +kernel
theorem typeOKA_1 : typeOKA 1 := by unfold typeOKA; decide +kernel
theorem typeOKA_2 : typeOKA 2 := by unfold typeOKA; decide +kernel

theorem pairsAOK_0 : pairsAOK 0 := by unfold pairsAOK; decide +kernel
theorem pairsAOK_1 : pairsAOK 1 := by unfold pairsAOK; decide +kernel
theorem pairsAOK_2 : pairsAOK 2 := by unfold pairsAOK; decide +kernel
theorem pairsAOK_4 : pairsAOK 4 := by unfold pairsAOK; decide +kernel
theorem pairsAOK_5 : pairsAOK 5 := by unfold pairsAOK; decide +kernel
theorem pairsAOK_6 : pairsAOK 6 := by unfold pairsAOK; decide +kernel
theorem pairsAOK_7 : pairsAOK 7 := by unfold pairsAOK; decide +kernel
theorem pairsAOK_9 : pairsAOK 9 := by unfold pairsAOK; decide +kernel
theorem pairsAOK_10 : pairsAOK 10 := by unfold pairsAOK; decide +kernel
theorem pairsAOK_11 : pairsAOK 11 := by unfold pairsAOK; decide +kernel
theorem pairsAOK_15 : pairsAOK 15 := by unfold pairsAOK; decide +kernel
theorem pairsAOK_17 : pairsAOK 17 := by unfold pairsAOK; decide +kernel

theorem pairsAOK_mult (s : Fin 3) (hs : s = 1 ∨ s = 2) (u : Fin 8) : pairsAOK (x2Mult s u) := by
  rcases hs with rfl | rfl <;> fin_cases u <;>
    first
    | exact pairsAOK_0 | exact pairsAOK_1 | exact pairsAOK_2 | exact pairsAOK_4 | exact pairsAOK_5 | exact pairsAOK_6
    | exact pairsAOK_7 | exact pairsAOK_9 | exact pairsAOK_10 | exact pairsAOK_11 | exact pairsAOK_15
    | exact pairsAOK_17

theorem labelsAOK_of (s : Fin 3) (hs : s = 1 ∨ s = 2) : labelsAOK s := by
  rcases hs with rfl | rfl
  · exact labelsAOK_1
  · exact labelsAOK_2

/-! ### Runs of the A input table -/

/-- The run of `n` slots from slot `(j % 77) · 282 + off` of the fiber of super-row `j / 77`. -/
def runAtA (Fs : List ℕ) (j off n : ℕ) : ℕ :=
  ((Fs.getD (j / 77) 0) >>> (384 * ((j % 77) * 282 + off))) &&& (2 ^ (384 * n) - 1)

theorem runAtA_dig (Fs : List ℕ) (j off n t : ℕ) (ht : t < n) :
    dig 384 (runAtA Fs j off n) t = dig 384 (Fs.getD (j / 77) 0) ((j % 77) * 282 + off + t) := by
  unfold runAtA
  rw [dig_low 384 _ n t (by norm_num) ht, dig_shift, Nat.add_comm t]

theorem runA_ent (Fs : List ℕ) (j off n X : ℕ) (h : Nat.beq (runAtA Fs j off n) X = true) (t : ℕ) (ht : t < n) :
    ent 384 (384 - 1) (Fs.getD (j / 77) 0) ((j % 77) * 282 + off + t) = ent 384 (384 - 1) X t := by
  have e := Nat.eq_of_beq_eq_true h
  unfold ent
  rw [← runAtA_dig Fs j off n t ht, e]

def zeroRunsOKA (Fs : List ℕ) (ov nv ou nu : ℕ) : Bool :=
  (List.range nv).all (fun j' => Nat.beq (runAtA Fs (ov + j') ou nu) (offset 384 (384 - 1) nu))

noncomputable def wideRowOKA (Fs : List ℕ) (row : List ℕ) (ov nv ou nu : ℕ) : Bool :=
  Nat.beq row.length nv &&
    (List.zip row (List.range nv)).all (fun p => Nat.beq (runAtA Fs (ov + p.2) ou nu) (widen 256 384 nu p.1))

def gatherRowsOKA (Fs : List ℕ) (rows : List (List ℕ)) (pos ov nv ou nu : ℕ) : Bool :=
  Nat.beq rows.length nv &&
    (List.zip rows (List.range nv)).all (fun p =>
      Nat.beq p.1.length nu && Nat.beq (runAtA Fs (ov + p.2) ou nu) (gatherRun p.1 pos))

def gatherPosOKA (Fs : List ℕ) (row : List ℕ) (posf : ℕ → ℕ) (ov nv ou nu : ℕ) : Bool :=
  Nat.beq row.length nu &&
    (List.range nv).all (fun j' => Nat.beq (runAtA Fs (ov + j') ou nu) (gatherRun row (posf j')))

theorem zeroRunsOKA_sound (Fs : List ℕ) (ov nv ou nu : ℕ) (h : zeroRunsOKA Fs ov nv ou nu = true) :
    ∀ j' < nv, ∀ t < nu, ent 384 (384 - 1) (Fs.getD ((ov + j') / 77) 0) (((ov + j') % 77) * 282 + ou + t) = 0 := by
  intro j' hj' t ht
  have hc := List.all_eq_true.mp h j' (List.mem_range.mpr hj')
  rw [runA_ent Fs _ _ _ _ hc t ht, offset_ent nu t ht]

theorem wideRowOKA_sound (Fs : List ℕ) (row : List ℕ) (ov nv ou nu : ℕ) (h : wideRowOKA Fs row ov nv ou nu = true) :
    ∀ j' < nv, ∀ t < nu, ent 384 (384 - 1) (Fs.getD ((ov + j') / 77) 0) (((ov + j') % 77) * 282 + ou + t) =
      ent 256 (256 - 1) (row.getD j' 0) t := by
  intro j' hj' t ht
  unfold wideRowOKA at h
  rw [Bool.and_eq_true] at h
  have hlen := Nat.eq_of_beq_eq_true h.1
  have hc := List.all_eq_true.mp h.2 _ (mem_zip_range row nv hlen 0 j' hj')
  dsimp only at hc
  rw [runA_ent Fs _ _ _ _ hc t ht]
  exact (widen_spec 256 384 nu _ (by norm_num) (by norm_num)).2 t ht

theorem gatherRowsOKA_sound (Fs : List ℕ) (rows : List (List ℕ)) (pos ov nv ou nu : ℕ)
    (h : gatherRowsOKA Fs rows pos ov nv ou nu = true) :
    ∀ j' < nv, ∀ t < nu, ent 384 (384 - 1) (Fs.getD ((ov + j') / 77) 0) (((ov + j') % 77) * 282 + ou + t) =
      ent 256 (256 - 1) ((rows.getD j' []).getD t 0) pos := by
  intro j' hj' t ht
  unfold gatherRowsOKA at h
  rw [Bool.and_eq_true] at h
  have hlen := Nat.eq_of_beq_eq_true h.1
  have hc := List.all_eq_true.mp h.2 _ (mem_zip_range rows nv hlen [] j' hj')
  simp only [Bool.and_eq_true] at hc
  have hl := Nat.eq_of_beq_eq_true hc.1
  rw [runA_ent Fs _ _ _ _ hc.2 t ht, gatherRun_ent _ pos t (by rw [hl]; exact ht)]

theorem gatherPosOKA_sound (Fs : List ℕ) (row : List ℕ) (posf : ℕ → ℕ) (ov nv ou nu : ℕ)
    (h : gatherPosOKA Fs row posf ov nv ou nu = true) :
    ∀ j' < nv, ∀ t < nu, ent 384 (384 - 1) (Fs.getD ((ov + j') / 77) 0) (((ov + j') % 77) * 282 + ou + t) =
      ent 256 (256 - 1) (row.getD t 0) (posf j') := by
  intro j' hj' t ht
  unfold gatherPosOKA at h
  rw [Bool.and_eq_true] at h
  have hl := Nat.eq_of_beq_eq_true h.1
  have hc := List.all_eq_true.mp h.2 j' (List.mem_range.mpr hj')
  rw [runA_ent Fs _ _ _ _ hc t ht, gatherRun_ent _ (posf j') t (by rw [hl]; exact ht)]

/-! ### Segments of the A table -/

noncomputable def segOKwA (s : Fin 3) (TTaas TCaas TTsaa TCasa : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) (Fs : List ℕ) (w : Fin 8) (c' : ℕ) (u v : Fin 8) : Bool :=
  if w ≤ u ∧ v ≤ u then
    if v ≤ w then
      (if Zd v w u then zeroRunsOKA Fs (x2AOff s v) (nA s v) (x2SOff s u) (nS s u)
        else wideRowOKA Fs ((TTaas v w u).getD c' []) (x2AOff s v) (nA s v) (x2SOff s u) (nS s u))
    else
      (if Zd w v u then zeroRunsOKA Fs (x2AOff s v) (nA s v) (x2SOff s u) (nS s u)
        else wideRowOKA Fs ((TCaas w v u).getD c' []) (x2AOff s v) (nA s v) (x2SOff s u) (nS s u))
  else if u < w ∧ u < v then
    if v ≤ w then
      (if Zd u v w then zeroRunsOKA Fs (x2AOff s v) (nA s v) (x2SOff s u) (nS s u)
        else gatherRowsOKA Fs (TTsaa u v w) (posA (x2Mult s w) c') (x2AOff s v) (nA s v) (x2SOff s u) (nS s u))
    else
      (if Zd u w v then zeroRunsOKA Fs (x2AOff s v) (nA s v) (x2SOff s u) (nS s u)
        else gatherPosOKA Fs ((TTsaa u w v).getD c' []) (posA (x2Mult s v)) (x2AOff s v) (nA s v) (x2SOff s u)
          (nS s u))
  else
    if v ≤ w then
      (if Zd v u w then zeroRunsOKA Fs (x2AOff s v) (nA s v) (x2SOff s u) (nS s u)
        else gatherRowsOKA Fs (TCasa v u w) (posA (x2Mult s w) c') (x2AOff s v) (nA s v) (x2SOff s u) (nS s u))
    else
      (if Zd w u v then zeroRunsOKA Fs (x2AOff s v) (nA s v) (x2SOff s u) (nS s u)
        else gatherPosOKA Fs ((TCasa w u v).getD c' []) (posA (x2Mult s v)) (x2AOff s v) (nA s v) (x2SOff s u)
          (nS s u))

noncomputable def segOKA (s : Fin 3) (TTaas TCaas TTsaa TCasa : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) (Fs : List ℕ) (c : ℕ) (u v : Fin 8) : Bool :=
  segOKwA s TTaas TCaas TTsaa TCasa Zd Fs (typeA s c) (c - x2AOff s (typeA s c)) u v

def DirSpecA (s : Fin 3) (N : X2Blocks s) (TTaas TCaas TTsaa TCasa : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) : Prop :=
  ∀ t0 t1 t2 : Fin 8, t0 ≤ t1 → t1 ≤ t2 →
    (Zd t0 t1 t2 = true → ZspecA s N t0 t1 t2) ∧
      (Zd t0 t1 t2 = false → TTspecAAS s N t0 t1 t2 (TTaas t0 t1 t2) ∧ TCspecAAS s N t0 t1 t2 (TCaas t0 t1 t2) ∧
        TTspecSAA s N t0 t1 t2 (TTsaa t0 t1 t2) ∧ TCspecASA s N t0 t1 t2 (TCasa t0 t1 t2))

theorem segOKA_sound (s : Fin 3) (N : X2Blocks s) (TTaas TCaas TTsaa TCasa : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) (hdir : DirSpecA s N TTaas TCaas TTsaa TCasa Zd) (hdec : labelDecompA s)
    (hty : typeOKA s) (Fs : List ℕ) (c : Fin 231) (u v : Fin 8)
    (h : segOKA s TTaas TCaas TTsaa TCasa Zd Fs c u v = true) :
    ∀ j' < nA s v, ∀ i' < nS s u,
      (ent 384 (384 - 1) (Fs.getD ((x2AOff s v + j') / 77) 0) (((x2AOff s v + j') % 77) * 282 + x2SOff s u + i') : ℚ) =
        1108531032609225922165724911675932935547910848716289179910144000 *
          x2EmbedA x2DataConcrete s N (slab s u i') (alab s v j') c := by
  intro j' hj' i' hi'
  obtain ⟨_, hclt, hceq⟩ := hdec c
  unfold segOKA at h
  rw [hty c] at h
  generalize hw : (x2ALabel s c).1 = w at h hclt hceq
  generalize hc' : c.val - x2AOff s w = c' at h hclt hceq
  have hcc : c = alab s w c' := hceq.symm
  rw [hcc]
  unfold segOKwA at h
  by_cases hA : w ≤ u ∧ v ≤ u
  · rw [if_pos hA] at h
    by_cases hvw : v ≤ w
    · rw [if_pos hvw] at h
      have hsp := hdir v w u hvw hA.1
      by_cases hZ : Zd v w u = true
      · rw [if_pos hZ] at h
        rw [zeroRunsOKA_sound Fs _ _ _ _ h j' hj' i' hi', (hsp.1 hZ).1 j' hj' c' hclt i' hi']
        norm_num
      · rw [if_neg hZ] at h
        rw [wideRowOKA_sound Fs _ _ _ _ _ h j' hj' i' hi']
        exact (hsp.2 (by simpa using hZ)).1 j' hj' c' hclt i' hi'
    · rw [if_neg hvw] at h
      have hwv : w ≤ v := le_of_lt (not_le.mp hvw)
      have hsp := hdir w v u hwv hA.2
      by_cases hZ : Zd w v u = true
      · rw [if_pos hZ] at h
        rw [zeroRunsOKA_sound Fs _ _ _ _ h j' hj' i' hi', ← x2EmbedA_swap12, (hsp.1 hZ).1 c' hclt j' hj' i' hi']
        norm_num
      · rw [if_neg hZ] at h
        rw [wideRowOKA_sound Fs _ _ _ _ _ h j' hj' i' hi', ← x2EmbedA_swap12]
        exact (hsp.2 (by simpa using hZ)).2.1 c' hclt j' hj' i' hi'
  · rw [if_neg hA] at h
    by_cases hB : u < w ∧ u < v
    · rw [if_pos hB] at h
      by_cases hvw : v ≤ w
      · rw [if_pos hvw] at h
        have hsp := hdir u v w (le_of_lt hB.2) hvw
        by_cases hZ : Zd u v w = true
        · rw [if_pos hZ] at h
          rw [zeroRunsOKA_sound Fs _ _ _ _ h j' hj' i' hi', (hsp.1 hZ).2.1 i' hi' j' hj' c' hclt]
          norm_num
        · rw [if_neg hZ] at h
          rw [gatherRowsOKA_sound Fs _ _ _ _ _ _ h j' hj' i' hi']
          exact (hsp.2 (by simpa using hZ)).2.2.1 i' hi' j' hj' c' hclt
      · rw [if_neg hvw] at h
        have hwv : w ≤ v := le_of_lt (not_le.mp hvw)
        have hsp := hdir u w v (le_of_lt hB.1) hwv
        by_cases hZ : Zd u w v = true
        · rw [if_pos hZ] at h
          rw [zeroRunsOKA_sound Fs _ _ _ _ h j' hj' i' hi', ← x2EmbedA_swap12, (hsp.1 hZ).2.1 i' hi' c' hclt j' hj']
          norm_num
        · rw [if_neg hZ] at h
          rw [gatherPosOKA_sound Fs _ _ _ _ _ _ h j' hj' i' hi', ← x2EmbedA_swap12]
          exact (hsp.2 (by simpa using hZ)).2.2.1 i' hi' c' hclt j' hj'
    · rw [if_neg hB] at h
      by_cases hvw : v ≤ w
      · rw [if_pos hvw] at h
        have hvu : v ≤ u := by
          by_contra hc
          exact hB ⟨lt_of_lt_of_le (not_le.mp hc) hvw, not_le.mp hc⟩
        have huw : u < w := by
          by_contra hc
          exact hA ⟨not_lt.mp hc, hvu⟩
        have hsp := hdir v u w hvu (le_of_lt huw)
        by_cases hZ : Zd v u w = true
        · rw [if_pos hZ] at h
          rw [zeroRunsOKA_sound Fs _ _ _ _ h j' hj' i' hi', (hsp.1 hZ).2.2 j' hj' i' hi' c' hclt]
          norm_num
        · rw [if_neg hZ] at h
          rw [gatherRowsOKA_sound Fs _ _ _ _ _ _ h j' hj' i' hi']
          exact (hsp.2 (by simpa using hZ)).2.2.2 j' hj' i' hi' c' hclt
      · rw [if_neg hvw] at h
        have hwv : w < v := not_le.mp hvw
        have hwu : w ≤ u := by
          by_contra hc
          exact hB ⟨not_le.mp hc, lt_trans (not_le.mp hc) hwv⟩
        have huv : u < v := by
          by_contra hc
          exact hA ⟨hwu, not_lt.mp hc⟩
        have hsp := hdir w u v hwu (le_of_lt huv)
        by_cases hZ : Zd w u v = true
        · rw [if_pos hZ] at h
          rw [zeroRunsOKA_sound Fs _ _ _ _ h j' hj' i' hi', ← x2EmbedA_swap12, (hsp.1 hZ).2.2 c' hclt i' hi' j' hj']
          norm_num
        · rw [if_neg hZ] at h
          rw [gatherPosOKA_sound Fs _ _ _ _ _ _ h j' hj' i' hi', ← x2EmbedA_swap12]
          exact (hsp.2 (by simpa using hZ)).2.2.2 c' hclt i' hi' j' hj'

/-- hT0 of the A-pipeline transfer theorems for every cell, from all segments. -/
theorem hT0A_of_segs (s : Fin 3) (N : X2Blocks s) (TTaas TCaas TTsaa TCasa : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) (hdir : DirSpecA s N TTaas TCaas TTsaa TCasa Zd) (hdecS : labelDecompS s)
    (hdecA : labelDecompA s) (hty : typeOKA s) (f0 : List (List ℕ))
    (hchk : ∀ c : Fin 231, ∀ u v : Fin 8, segOKA s TTaas TCaas TTsaa TCasa Zd (colFibers f0 c) c u v = true) :
    ∀ (i : Fin 282) (j : Fin 231) (c : Fin 231), x2EmbedA x2DataConcrete s N i j c =
      (ent 384 (384 - 1) (x2Tab f0 (j.val / 77) c) ((j.val % 77) * 282 + i.val) : ℚ) /
        1108531032609225922165724911675932935547910848716289179910144000 := by
  intro i j c
  obtain ⟨hil, hilt, hieq⟩ := hdecS i
  obtain ⟨hjl, hjlt, hjeq⟩ := hdecA j
  have h := segOKA_sound s N TTaas TCaas TTsaa TCasa Zd hdir hdecA hty (colFibers f0 c) c (x2SLabel s i).1
    (x2ALabel s j).1 (hchk c _ _) _ hjlt _ hilt
  have ei : (j.val % 77) * 282 + x2SOff s (x2SLabel s i).1 + (i.val - x2SOff s (x2SLabel s i).1) =
      (j.val % 77) * 282 + i.val := by omega
  rw [hieq, hjeq, Nat.add_sub_cancel' hjl, ei, colFibers_getD f0 c _ (by omega)] at h
  rw [eq_div_iff (by norm_num), h]
  ring

/-- All segments of the A columns `lo ≤ c < lo + cnt`. -/
noncomputable def colsChunkOKA (s : Fin 3) (TTaas TCaas TTsaa TCasa : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) (f0 : List (List ℕ)) (lo cnt : ℕ) : Bool :=
  (List.zip (List.range cnt) (List.zip ((f0.getD 0 []).drop lo)
      (List.zip ((f0.getD 1 []).drop lo) ((f0.getD 2 []).drop lo)))).all
    (fun p => (List.finRange 8).all (fun u => (List.finRange 8).all (fun v =>
      segOKA s TTaas TCaas TTsaa TCasa Zd [p.2.1, p.2.2.1, p.2.2.2] (lo + p.1) u v)))

theorem colsChunkOKA_sound (s : Fin 3) (TTaas TCaas TTsaa TCasa : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) (f0 : List (List ℕ)) (hlen : ∀ r < 3, (f0.getD r []).length = 231)
    (lo cnt : ℕ) (hlc : lo + cnt ≤ 231) (h : colsChunkOKA s TTaas TCaas TTsaa TCasa Zd f0 lo cnt = true) :
    ∀ c : ℕ, lo ≤ c → c < lo + cnt → ∀ u v : Fin 8,
      segOKA s TTaas TCaas TTsaa TCasa Zd (colFibers f0 c) c u v = true := by
  intro c hlo hhi u v
  have hl0 := hlen 0 (by norm_num)
  have hl1 := hlen 1 (by norm_num)
  have hl2 := hlen 2 (by norm_num)
  have hMl : cnt ≤ (List.zip ((f0.getD 0 []).drop lo)
      (List.zip ((f0.getD 1 []).drop lo) ((f0.getD 2 []).drop lo))).length := by
    simp only [List.length_zip, List.length_drop, hl0, hl1, hl2]
    omega
  have hm := mem_range_zip _ cnt hMl (0, 0, 0) (c - lo) (by omega)
  have hc := List.all_eq_true.mp h _ hm
  dsimp only at hc
  rw [getD_zip' _ _ _ 0 (0, 0) (by simp only [List.length_drop, hl0]; omega)
      (by simp only [List.length_zip, List.length_drop, hl1, hl2]; omega),
    getD_zip' _ _ _ 0 0 (by simp only [List.length_drop, hl1]; omega) (by simp only [List.length_drop, hl2]; omega)] at hc
  dsimp only at hc
  rw [getD_drop', getD_drop', getD_drop', show lo + (c - lo) = c by omega] at hc
  have hu := List.all_eq_true.mp hc u (List.mem_finRange u)
  exact List.all_eq_true.mp hu v (List.mem_finRange v)

/-! ### The A-pipeline triple theorem -/

/-- From key facts, checked stored blocks and the checked T-tables of the three arrangements: the four
A specifications of a sorted type triple. -/
theorem tripleSpecA (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (t0 t1 t2 : Fin 8) (h01 : t0 ≤ t1) (h12 : t1 ≤ t2) (ks : List (x2Key s × List (ℕ × ℕ × ℕ)))
    (hks : ∀ k : x2Key s, x2KeyTypes s k = ![t0, t1, t2] ↔ k ∈ ks.map Prod.fst) (hnd : (ks.map Prod.fst).Nodup)
    (hkeys : ∀ e ∈ ks, keyOK (x2Mult s t0 * x2Mult s t1 * x2Mult s t2) s N e.1 e.2)
    (hlen : (ks.flatMap Prod.snd).length < 2 ^ 27) (UBT : List (List (List (List ℕ))))
    (hshape : ∀ a0 < x2Mult s t0, ∀ a1 < x2Mult s t1, ((UBT.getD a0 []).getD a1 []).length = x2Mult s t0 ∧
      ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = x2Mult s t1)
    (hchk : ∀ a0 < x2Mult s t0, ∀ a1 < x2Mult s t1,
      ibBatchOK 256 (x2Mult s t0 * x2Mult s t1 * x2Mult s t2) 302 (x2Mult s t2) (x2Mult s t0 * x2Mult s t1) 0
        (x2Mult s t2) ((a0 * x2Mult s t1 + a1) * x2Mult s t2) (ks.flatMap Prod.snd)
        ((UBT.getD a0 []).getD a1 []).flatten = true)
    (TTa TCa TTs TCs : List (List ℕ))
    (hTTa : ∀ i0 < nA s t0, ∀ i1 < nA s t1, tCellG UBT (nS s t2) 6 2 2 6 ((pairsA (x2Mult s t0)).getD i0 (0, 0))
      ((pairsA (x2Mult s t1)).getD i1 (0, 0)) ((TTa.getD i1 []).getD i0 0) = true)
    (hTCa : ∀ i0 < nA s t0, ∀ i1 < nA s t1, tCellG UBT (nS s t2) 6 2 2 6 ((pairsA (x2Mult s t0)).getD i0 (0, 0))
      ((pairsA (x2Mult s t1)).getD i1 (0, 0)) ((TCa.getD i0 []).getD i1 0) = true)
    (hTTs : ∀ i0 < nS s t0, ∀ i1 < nA s t1, tCellG UBT (nS s t2) 6 6 2 2 ((pairsU (x2Mult s t0)).getD i0 (0, 0))
      ((pairsA (x2Mult s t1)).getD i1 (0, 0)) ((TTs.getD i1 []).getD i0 0) = true)
    (hTCs : ∀ i0 < nA s t0, ∀ i1 < nS s t1, tCellG UBT (nS s t2) 6 2 6 2 ((pairsA (x2Mult s t0)).getD i0 (0, 0))
      ((pairsU (x2Mult s t1)).getD i1 (0, 0)) ((TCs.getD i0 []).getD i1 0) = true) :
    TTspecAAS s N t0 t1 t2 TTa ∧ TCspecAAS s N t0 t1 t2 TCa ∧ TTspecSAA s N t0 t1 t2 TTs ∧
      TCspecASA s N t0 t1 t2 TCs := by
  obtain ⟨hok, hparts⟩ := parts_of_keys _ s N ks hkeys
  by_cases hm2 : x2Mult s t2 = 0
  · have hz : nS s t2 = 0 ∧ nA s t2 = 0 := by unfold nS nA; rw [hm2]; simp
    refine ⟨fun _ _ _ _ i2 hi2 => by omega, fun _ _ _ _ i2 hi2 => by omega, fun _ _ _ _ i2 hi2 => by omega,
      fun _ _ _ _ i2 hi2 => by omega⟩
  have hm2' : 1 ≤ x2Mult s t2 := Nat.one_le_iff_ne_zero.mpr hm2
  have hU := ubSpec (x2Mult s t0 * x2Mult s t1 * x2Mult s t2) (x2Mult s t0) (x2Mult s t1) (x2Mult s t2)
    (ks.flatMap Prod.snd) UBT hm2' rfl hparts hlen hshape hchk
  have hKS : ∀ x0 x1 x2 y0 y1 y2 : ℕ, x0 < x2Mult s t0 → x1 < x2Mult s t1 → x2 < x2Mult s t2 →
      y0 < x2Mult s t0 → y1 < x2Mult s t1 → y2 < x2Mult s t2 →
      (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) *
          x2KeySum s N ![t0, t1, t2] ![x0, x1, x2] ![y0, y1, y2] =
        (ibIB 256 (ks.flatMap Prod.snd) (kflat (x2Mult s t1) (x2Mult s t2) x0 x1 x2)
          (kflat (x2Mult s t1) (x2Mult s t2) y0 y1 y2) : ℚ) :=
    fun x0 x1 x2 y0 y1 y2 h0 h1 h2 h3 h4 h5 =>
      x2KeySum_ib s N ![t0, t1, t2] ks hks hnd hok ![x0, x1, x2] ![y0, y1, y2] h0 h1 h2 h3 h4 h5
  have hl := labelsOK_of s hs
  have hlA := labelsAOK_of s hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ttSpecAAS s hs N hN t0 t1 t2 h01 h12 _ UBT hKS hU (fun i0 i1 => (TTa.getD i1 []).getD i0 0) hl hlA
      (pairsAOK_mult s hs t0) (pairsAOK_mult s hs t1) (pairsOK_mult s hs t2) hTTa
  · exact ttSpecAAS s hs N hN t0 t1 t2 h01 h12 _ UBT hKS hU (fun i0 i1 => (TCa.getD i0 []).getD i1 0) hl hlA
      (pairsAOK_mult s hs t0) (pairsAOK_mult s hs t1) (pairsOK_mult s hs t2) hTCa
  · exact ttSpecSAA s hs N hN t0 t1 t2 h01 h12 _ UBT hKS hU (fun i0 i1 => (TTs.getD i1 []).getD i0 0) hl hlA
      (pairsOK_mult s hs t0) (pairsAOK_mult s hs t1) (pairsAOK_mult s hs t2) hTTs
  · exact ttSpecASA s hs N hN t0 t1 t2 h01 h12 _ UBT hKS hU (fun i0 i1 => (TCs.getD i0 []).getD i1 0) hl hlA
      (pairsAOK_mult s hs t0) (pairsOK_mult s hs t1) (pairsAOK_mult s hs t2) hTCs

/-- (Row-range checks of the stored blocks.) From key facts, checked stored blocks and the checked T-tables of the three arrangements: the four
A specifications of a sorted type triple. -/
theorem tripleSpecA' (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (t0 t1 t2 : Fin 8) (h01 : t0 ≤ t1) (h12 : t1 ≤ t2) (ks : List (x2Key s × List (ℕ × ℕ × ℕ)))
    (hks : ∀ k : x2Key s, x2KeyTypes s k = ![t0, t1, t2] ↔ k ∈ ks.map Prod.fst) (hnd : (ks.map Prod.fst).Nodup)
    (hkeys : ∀ e ∈ ks, keyOK (x2Mult s t0 * x2Mult s t1 * x2Mult s t2) s N e.1 e.2)
    (hlen : (ks.flatMap Prod.snd).length < 2 ^ 27) (UBT : List (List (List (List ℕ))))
    (hshape : ∀ a0 < x2Mult s t0, ∀ a1 < x2Mult s t1, ((UBT.getD a0 []).getD a1 []).length = x2Mult s t0 ∧
      ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = x2Mult s t1)
    (hchk : ubRowsOK (x2Mult s t0 * x2Mult s t1 * x2Mult s t2) (x2Mult s t0) (x2Mult s t1) (x2Mult s t2)
      (ks.flatMap Prod.snd) UBT)
    (TTa TCa TTs TCs : List (List ℕ))
    (hTTa : ∀ i0 < nA s t0, ∀ i1 < nA s t1, tCellG UBT (nS s t2) 6 2 2 6 ((pairsA (x2Mult s t0)).getD i0 (0, 0))
      ((pairsA (x2Mult s t1)).getD i1 (0, 0)) ((TTa.getD i1 []).getD i0 0) = true)
    (hTCa : ∀ i0 < nA s t0, ∀ i1 < nA s t1, tCellG UBT (nS s t2) 6 2 2 6 ((pairsA (x2Mult s t0)).getD i0 (0, 0))
      ((pairsA (x2Mult s t1)).getD i1 (0, 0)) ((TCa.getD i0 []).getD i1 0) = true)
    (hTTs : ∀ i0 < nS s t0, ∀ i1 < nA s t1, tCellG UBT (nS s t2) 6 6 2 2 ((pairsU (x2Mult s t0)).getD i0 (0, 0))
      ((pairsA (x2Mult s t1)).getD i1 (0, 0)) ((TTs.getD i1 []).getD i0 0) = true)
    (hTCs : ∀ i0 < nA s t0, ∀ i1 < nS s t1, tCellG UBT (nS s t2) 6 2 6 2 ((pairsA (x2Mult s t0)).getD i0 (0, 0))
      ((pairsU (x2Mult s t1)).getD i1 (0, 0)) ((TCs.getD i0 []).getD i1 0) = true) :
    TTspecAAS s N t0 t1 t2 TTa ∧ TCspecAAS s N t0 t1 t2 TCa ∧ TTspecSAA s N t0 t1 t2 TTs ∧
      TCspecASA s N t0 t1 t2 TCs := by
  obtain ⟨hok, hparts⟩ := parts_of_keys _ s N ks hkeys
  by_cases hm2 : x2Mult s t2 = 0
  · have hz : nS s t2 = 0 ∧ nA s t2 = 0 := by unfold nS nA; rw [hm2]; simp
    refine ⟨fun _ _ _ _ i2 hi2 => by omega, fun _ _ _ _ i2 hi2 => by omega, fun _ _ _ _ i2 hi2 => by omega,
      fun _ _ _ _ i2 hi2 => by omega⟩
  have hm2' : 1 ≤ x2Mult s t2 := Nat.one_le_iff_ne_zero.mpr hm2
  have hU := ubSpec' (x2Mult s t0 * x2Mult s t1 * x2Mult s t2) (x2Mult s t0) (x2Mult s t1) (x2Mult s t2)
    (ks.flatMap Prod.snd) UBT hm2' rfl hparts hlen hshape hchk
  have hKS : ∀ x0 x1 x2 y0 y1 y2 : ℕ, x0 < x2Mult s t0 → x1 < x2Mult s t1 → x2 < x2Mult s t2 →
      y0 < x2Mult s t0 → y1 < x2Mult s t1 → y2 < x2Mult s t2 →
      (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) *
          x2KeySum s N ![t0, t1, t2] ![x0, x1, x2] ![y0, y1, y2] =
        (ibIB 256 (ks.flatMap Prod.snd) (kflat (x2Mult s t1) (x2Mult s t2) x0 x1 x2)
          (kflat (x2Mult s t1) (x2Mult s t2) y0 y1 y2) : ℚ) :=
    fun x0 x1 x2 y0 y1 y2 h0 h1 h2 h3 h4 h5 =>
      x2KeySum_ib s N ![t0, t1, t2] ks hks hnd hok ![x0, x1, x2] ![y0, y1, y2] h0 h1 h2 h3 h4 h5
  have hl := labelsOK_of s hs
  have hlA := labelsAOK_of s hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ttSpecAAS s hs N hN t0 t1 t2 h01 h12 _ UBT hKS hU (fun i0 i1 => (TTa.getD i1 []).getD i0 0) hl hlA
      (pairsAOK_mult s hs t0) (pairsAOK_mult s hs t1) (pairsOK_mult s hs t2) hTTa
  · exact ttSpecAAS s hs N hN t0 t1 t2 h01 h12 _ UBT hKS hU (fun i0 i1 => (TCa.getD i0 []).getD i1 0) hl hlA
      (pairsAOK_mult s hs t0) (pairsAOK_mult s hs t1) (pairsOK_mult s hs t2) hTCa
  · exact ttSpecSAA s hs N hN t0 t1 t2 h01 h12 _ UBT hKS hU (fun i0 i1 => (TTs.getD i1 []).getD i0 0) hl hlA
      (pairsOK_mult s hs t0) (pairsAOK_mult s hs t1) (pairsAOK_mult s hs t2) hTTs
  · exact ttSpecASA s hs N hN t0 t1 t2 h01 h12 _ UBT hKS hU (fun i0 i1 => (TCs.getD i0 []).getD i1 0) hl hlA
      (pairsAOK_mult s hs t0) (pairsOK_mult s hs t1) (pairsAOK_mult s hs t2) hTCs

/-- Zero triples for the A pipeline. -/
theorem zeroTripleA (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (t0 t1 t2 : Fin 8) (h01 : t0 ≤ t1) (h12 : t1 ≤ t2) (ks : List (x2Key s × List (ℕ × ℕ × ℕ)))
    (hks : ∀ k : x2Key s, x2KeyTypes s k = ![t0, t1, t2] ↔ k ∈ ks.map Prod.fst) (hnd : (ks.map Prod.fst).Nodup)
    (hkeys : ∀ e ∈ ks, keyIB s N e.1 e.2) (hempty : ks.flatMap Prod.snd = []) : ZspecA s N t0 t1 t2 :=
  zspecA_of_empty s hs N hN t0 t1 t2 h01 h12 (labelsOK_of s hs) (labelsAOK_of s hs) (pairsOK_mult s hs)
    (pairsAOK_mult s hs) (fun x0 x1 x2 y0 y1 y2 h0 h1 h2 h3 h4 h5 =>
      keySum_zero_of_empty s N ![t0, t1, t2] ks hks hnd hkeys hempty ![x0, x1, x2] ![y0, y1, y2] h0 h1 h2 h3 h4 h5)

theorem zspecA_of_mult (s : Fin 3) (N : X2Blocks s) (t0 t1 t2 : Fin 8)
    (h : x2Mult s t0 = 0 ∨ x2Mult s t1 = 0 ∨ x2Mult s t2 = 0) : ZspecA s N t0 t1 t2 := by
  have e : ∀ u : Fin 8, x2Mult s u = 0 → nS s u = 0 ∧ nA s u = 0 := by
    intro u hu
    unfold nS nA
    rw [hu]
    simp
  refine ⟨fun i0 hi0 i1 hi1 i2 hi2 => ?_, fun i0 hi0 i1 hi1 i2 hi2 => ?_, fun i0 hi0 i1 hi1 i2 hi2 => ?_⟩ <;>
    rcases h with h | h | h <;> have := e _ h <;> omega

/-! ### Row checks of T-tables over S or A pairs, with signs -/

noncomputable def tRowOKG (UBT : List (List (List (List ℕ)))) (L2 s1 s2 s3 s4 : ℕ) (P0 : List (ℕ × ℕ)) (p1 : ℕ × ℕ)
    (row : List ℕ) : Bool :=
  Nat.beq row.length P0.length && (List.zip row P0).all (fun q => tCellG UBT L2 s1 s2 s3 s4 q.2 p1 q.1)

noncomputable def tRowOKG' (UBT : List (List (List (List ℕ)))) (L2 s1 s2 s3 s4 : ℕ) (P1 : List (ℕ × ℕ)) (p0 : ℕ × ℕ)
    (row : List ℕ) : Bool :=
  Nat.beq row.length P1.length && (List.zip row P1).all (fun q => tCellG UBT L2 s1 s2 s3 s4 p0 q.2 q.1)

theorem tTab_of_rowsG (UBT : List (List (List (List ℕ)))) (L2 s1 s2 s3 s4 : ℕ) (P0 P1 : List (ℕ × ℕ)) (n0 n1 : ℕ)
    (hP0 : P0.length = n0) (TT : List (List ℕ))
    (h : ∀ i1 < n1, tRowOKG UBT L2 s1 s2 s3 s4 P0 (P1.getD i1 (0, 0)) (TT.getD i1 []) = true) :
    ∀ i0 < n0, ∀ i1 < n1, tCellG UBT L2 s1 s2 s3 s4 (P0.getD i0 (0, 0)) (P1.getD i1 (0, 0))
      ((TT.getD i1 []).getD i0 0) = true := by
  intro i0 hi0 i1 hi1
  have hr := h i1 hi1
  unfold tRowOKG at hr
  rw [Bool.and_eq_true] at hr
  have hl := Nat.eq_of_beq_eq_true hr.1
  have hz : i0 < (List.zip (TT.getD i1 []) P0).length := by
    rw [List.length_zip, hl, hP0, Nat.min_self]
    exact hi0
  have hm := List.getElem_mem hz
  rw [List.getElem_zip] at hm
  have hc := List.all_eq_true.mp hr.2 _ hm
  dsimp only at hc
  rwa [List.getD_eq_getElem (TT.getD i1 []) 0 (by omega), List.getD_eq_getElem P0 (0, 0) (by omega)]

theorem tTabC_of_rowsG (UBT : List (List (List (List ℕ)))) (L2 s1 s2 s3 s4 : ℕ) (P0 P1 : List (ℕ × ℕ)) (n0 n1 : ℕ)
    (hP1 : P1.length = n1) (TC : List (List ℕ))
    (h : ∀ i0 < n0, tRowOKG' UBT L2 s1 s2 s3 s4 P1 (P0.getD i0 (0, 0)) (TC.getD i0 []) = true) :
    ∀ i0 < n0, ∀ i1 < n1, tCellG UBT L2 s1 s2 s3 s4 (P0.getD i0 (0, 0)) (P1.getD i1 (0, 0))
      ((TC.getD i0 []).getD i1 0) = true := by
  intro i0 hi0 i1 hi1
  have hr := h i0 hi0
  unfold tRowOKG' at hr
  rw [Bool.and_eq_true] at hr
  have hl := Nat.eq_of_beq_eq_true hr.1
  have hz : i1 < (List.zip (TC.getD i0 []) P1).length := by
    rw [List.length_zip, hl, hP1, Nat.min_self]
    exact hi1
  have hm := List.getElem_mem hz
  rw [List.getElem_zip] at hm
  have hc := List.all_eq_true.mp hr.2 _ hm
  dsimp only at hc
  rwa [List.getD_eq_getElem (TC.getD i0 []) 0 (by omega), List.getD_eq_getElem P1 (0, 0) (by omega)]

end X2
end ThreeCopyQutritWerner
