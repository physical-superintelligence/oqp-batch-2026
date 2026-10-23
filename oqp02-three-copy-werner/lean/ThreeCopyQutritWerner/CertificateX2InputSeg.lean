module

public import ThreeCopyQutritWerner.CertificateX2InputTrip
public import ThreeCopyQutritWerner.CertificateX2InputF0
public import ThreeCopyQutritWerner.CertificateX2InputSym
public import ThreeCopyQutritWerner.CertificateX2CoreBatch

@[expose] public section


/-!
# Input stage: the core's input table from T-tables

The S-pipeline input table `f0` (super-rows `r = j / 94`, entries `c`, slot `(j % 94) · 282 + i` holds
`σ · x2EmbedS i j c` in 384-bit offset slots) is checked SEGMENT by segment: for a column `c` (type `w`), a type
`u` of `i` and a type `v` of `j`, the runs over `i` of type `u` of the fibers `(j, c)`, `j` of type `v`, are
compared with the T-blocks of the sorted type triple of `(u, v, w)` (`segOK`):
* `u ≥ v, w` (the run label has the largest type): each run is a whole T-block (`wideRowOK`, re-packed to 384 bits);
* `u < v, w`: each run is gathered from one T-block per label `i` (`gatherRowsOK` / `gatherPosOK`);
* `min(v, w) ≤ u < max(v, w)`: the same from the table with rows by the first label;
* triples without parts: every run is zero (`zeroRunsOK`).
`segOK_sound` turns a passed segment into `hT0` at its cells, given the T-table specifications of the directory
(`DirSpecS`, from `ttSpecGen`), and `hT0S_of_segs` assembles hT0 of the core's transfer theorems for all cells.
-/

set_option maxRecDepth 100000
set_option exponentiation.threshold 1000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-! ### Label types and decomposition -/

/-- The type of an S label by comparison with the type offsets. -/
def typeS (s : Fin 3) (c : ℕ) : Fin 8 :=
  if c < x2SOff s 1 then 0 else if c < x2SOff s 2 then 1 else if c < x2SOff s 3 then 2 else
  if c < x2SOff s 4 then 3 else if c < x2SOff s 5 then 4 else if c < x2SOff s 6 then 5 else
  if c < x2SOff s 7 then 6 else 7

def typeOKS (s : Fin 3) : Prop := ∀ l : Fin 282, typeS s l.val = (x2SLabel s l).1

def labelDecompS (s : Fin 3) : Prop :=
  ∀ l : Fin 282, x2SOff s (x2SLabel s l).1 ≤ l.val ∧ l.val - x2SOff s (x2SLabel s l).1 < nS s (x2SLabel s l).1 ∧
    slab s (x2SLabel s l).1 (l.val - x2SOff s (x2SLabel s l).1) = l

/-! ### Runs of the input table -/

/-- The run of `n` slots from slot `(j % 94) · 282 + off` of the fiber of super-row `j / 94`. -/
def runAtS (Fs : List ℕ) (j off n : ℕ) : ℕ :=
  ((Fs.getD (j / 94) 0) >>> (384 * ((j % 94) * 282 + off))) &&& (2 ^ (384 * n) - 1)

/-- 256-bit offset digits re-packed as 384-bit offset slots. -/
def packOff (ds : List ℕ) : ℕ := concatFibers 384 1 (ds.map (fun d => d + (2 ^ (384 - 1) - 2 ^ (256 - 1))))

/-- Slot `pos` of every block of a row, as one 384-bit run. -/
def gatherRun (row : List ℕ) (pos : ℕ) : ℕ := packOff (row.map (fun B => digS 256 B pos))

theorem runAtS_dig (Fs : List ℕ) (j off n t : ℕ) (ht : t < n) :
    dig 384 (runAtS Fs j off n) t = dig 384 (Fs.getD (j / 94) 0) ((j % 94) * 282 + off + t) := by
  unfold runAtS
  rw [dig_low 384 _ n t (by norm_num) ht, dig_shift, Nat.add_comm t]

theorem run_ent (Fs : List ℕ) (j off n X : ℕ) (h : Nat.beq (runAtS Fs j off n) X = true) (t : ℕ) (ht : t < n) :
    ent 384 (384 - 1) (Fs.getD (j / 94) 0) ((j % 94) * 282 + off + t) = ent 384 (384 - 1) X t := by
  have e := Nat.eq_of_beq_eq_true h
  unfold ent
  rw [← runAtS_dig Fs j off n t ht, e]

theorem gather_ent_gen (W1 W2 : ℕ) (h1 : 1 ≤ W1) (h12 : W1 ≤ W2) (row : List ℕ) (pos t : ℕ) (ht : t < row.length) :
    ent W2 (W2 - 1) (concatFibers W2 1 ((row.map (fun B => digS W1 B pos)).map
        (fun d => d + (2 ^ (W2 - 1) - 2 ^ (W1 - 1))))) t = ent W1 (W1 - 1) (row.getD t 0) pos := by
  have hoff : 2 ^ (W1 - 1) ≤ 2 ^ (W2 - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hW1 : 2 ^ W1 = 2 * 2 ^ (W1 - 1) := by rw [← pow_succ']; congr 1; omega
  have hW2 : 2 ^ W2 = 2 * 2 ^ (W2 - 1) := by rw [← pow_succ']; congr 1; omega
  have hlt : ∀ B, dig W1 B pos + (2 ^ (W2 - 1) - 2 ^ (W1 - 1)) < 2 ^ (W2 * 1) := by
    intro B
    have hd := dig_lt W1 B pos
    rw [mul_one]
    omega
  have hall : ∀ f ∈ (row.map (fun B => digS W1 B pos)).map (fun d => d + (2 ^ (W2 - 1) - 2 ^ (W1 - 1))),
      f < 2 ^ (W2 * 1) := by
    intro f hf
    rw [List.map_map, List.mem_map] at hf
    obtain ⟨B, _, rfl⟩ := hf
    simp only [Function.comp_apply]
    rw [digS_eq]
    exact hlt B
  have hlen : t < ((row.map (fun B => digS W1 B pos)).map (fun d => d + (2 ^ (W2 - 1) - 2 ^ (W1 - 1)))).length := by
    simpa using ht
  have hd := concatFibers_dig W2 1 _ hall t 0 hlen (by norm_num)
  rw [mul_one, add_zero] at hd
  have hget : ((row.map (fun B => digS W1 B pos)).map (fun d => d + (2 ^ (W2 - 1) - 2 ^ (W1 - 1)))).getD t 0 =
      dig W1 (row.getD t 0) pos + (2 ^ (W2 - 1) - 2 ^ (W1 - 1)) := by
    rw [List.getD_eq_getElem _ _ hlen, List.getElem_map, List.getElem_map, List.getD_eq_getElem _ _ ht, digS_eq]
  have h0 := hlt (row.getD t 0)
  rw [mul_one] at h0
  rw [hget, dig_one_zero W2 _ h0] at hd
  unfold ent
  rw [hd, Nat.cast_add, Nat.cast_sub hoff]
  push_cast
  ring

theorem gatherRun_ent (row : List ℕ) (pos t : ℕ) (ht : t < row.length) :
    ent 384 (384 - 1) (gatherRun row pos) t = ent 256 (256 - 1) (row.getD t 0) pos :=
  gather_ent_gen 256 384 (by norm_num) (by norm_num) row pos t ht

theorem offset_ent_gen (W L t : ℕ) (hW : 1 ≤ W) (ht : t < L) : ent W (W - 1) (offset W (W - 1) L) t = 0 := by
  have hs : offset W (W - 1) L = ∑ k ∈ Finset.range L, (fun _ => 2 ^ (W - 1)) k * (2 ^ W) ^ k := by
    unfold offset
    rw [repunit_eq W L hW, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_mul]
  have hlt : 2 ^ (W - 1) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hd : dig W (offset W (W - 1) L) t = 2 ^ (W - 1) := by
    unfold dig
    rw [hs, pow_mul]
    exact sum_digit (2 ^ W) L (fun _ => 2 ^ (W - 1)) (by positivity) (fun _ => hlt) t ht
  unfold ent
  rw [hd]
  push_cast
  ring

theorem offset_ent (n t : ℕ) (ht : t < n) : ent 384 (384 - 1) (offset 384 (384 - 1) n) t = 0 :=
  offset_ent_gen 384 n t (by norm_num) ht

/-! ### Run checks of one segment -/

/-- Every run of the segment is zero. -/
def zeroRunsOK (Fs : List ℕ) (ov nv ou nu : ℕ) : Bool :=
  (List.range nv).all (fun j' => Nat.beq (runAtS Fs (ov + j') ou nu) (offset 384 (384 - 1) nu))

/-- Run `j'` is the whole block `row[j']` (re-packed to 384 bits). -/
noncomputable def wideRowOK (Fs : List ℕ) (row : List ℕ) (ov nv ou nu : ℕ) : Bool :=
  Nat.beq row.length nv &&
    (List.zip row (List.range nv)).all (fun p => Nat.beq (runAtS Fs (ov + p.2) ou nu) (widen 256 384 nu p.1))

/-- Run `j'` is slot `pos` of the blocks of `rows[j']`. -/
def gatherRowsOK (Fs : List ℕ) (rows : List (List ℕ)) (pos ov nv ou nu : ℕ) : Bool :=
  Nat.beq rows.length nv &&
    (List.zip rows (List.range nv)).all (fun p =>
      Nat.beq p.1.length nu && Nat.beq (runAtS Fs (ov + p.2) ou nu) (gatherRun p.1 pos))

/-- Run `j'` is slot `j'` of the blocks of `row`. -/
def gatherPosOK (Fs : List ℕ) (row : List ℕ) (ov nv ou nu : ℕ) : Bool :=
  Nat.beq row.length nu && (List.range nv).all (fun j' => Nat.beq (runAtS Fs (ov + j') ou nu) (gatherRun row j'))

theorem mem_zip_range {α : Type*} (row : List α) (n : ℕ) (hlen : row.length = n) (d : α) (j : ℕ) (hj : j < n) :
    (row.getD j d, j) ∈ List.zip row (List.range n) := by
  have hz : j < (List.zip row (List.range n)).length := by simp [hlen, hj]
  have h1 := List.getElem_mem hz
  rw [List.getElem_zip, List.getElem_range] at h1
  rwa [List.getD_eq_getElem _ _ (by omega)]

theorem zeroRunsOK_sound (Fs : List ℕ) (ov nv ou nu : ℕ) (h : zeroRunsOK Fs ov nv ou nu = true) :
    ∀ j' < nv, ∀ t < nu, ent 384 (384 - 1) (Fs.getD ((ov + j') / 94) 0) (((ov + j') % 94) * 282 + ou + t) = 0 := by
  intro j' hj' t ht
  have hc := List.all_eq_true.mp h j' (List.mem_range.mpr hj')
  rw [run_ent Fs _ _ _ _ hc t ht, offset_ent nu t ht]

theorem wideRowOK_sound (Fs : List ℕ) (row : List ℕ) (ov nv ou nu : ℕ) (h : wideRowOK Fs row ov nv ou nu = true) :
    ∀ j' < nv, ∀ t < nu, ent 384 (384 - 1) (Fs.getD ((ov + j') / 94) 0) (((ov + j') % 94) * 282 + ou + t) =
      ent 256 (256 - 1) (row.getD j' 0) t := by
  intro j' hj' t ht
  unfold wideRowOK at h
  rw [Bool.and_eq_true] at h
  have hlen := Nat.eq_of_beq_eq_true h.1
  have hc := List.all_eq_true.mp h.2 _ (mem_zip_range row nv hlen 0 j' hj')
  dsimp only at hc
  rw [run_ent Fs _ _ _ _ hc t ht]
  exact (widen_spec 256 384 nu _ (by norm_num) (by norm_num)).2 t ht

theorem gatherRowsOK_sound (Fs : List ℕ) (rows : List (List ℕ)) (pos ov nv ou nu : ℕ)
    (h : gatherRowsOK Fs rows pos ov nv ou nu = true) :
    ∀ j' < nv, ∀ t < nu, ent 384 (384 - 1) (Fs.getD ((ov + j') / 94) 0) (((ov + j') % 94) * 282 + ou + t) =
      ent 256 (256 - 1) ((rows.getD j' []).getD t 0) pos := by
  intro j' hj' t ht
  unfold gatherRowsOK at h
  rw [Bool.and_eq_true] at h
  have hlen := Nat.eq_of_beq_eq_true h.1
  have hc := List.all_eq_true.mp h.2 _ (mem_zip_range rows nv hlen [] j' hj')
  simp only [Bool.and_eq_true] at hc
  have hl := Nat.eq_of_beq_eq_true hc.1
  rw [run_ent Fs _ _ _ _ hc.2 t ht, gatherRun_ent _ pos t (by rw [hl]; exact ht)]

theorem gatherPosOK_sound (Fs : List ℕ) (row : List ℕ) (ov nv ou nu : ℕ) (h : gatherPosOK Fs row ov nv ou nu = true) :
    ∀ j' < nv, ∀ t < nu, ent 384 (384 - 1) (Fs.getD ((ov + j') / 94) 0) (((ov + j') % 94) * 282 + ou + t) =
      ent 256 (256 - 1) (row.getD t 0) j' := by
  intro j' hj' t ht
  unfold gatherPosOK at h
  rw [Bool.and_eq_true] at h
  have hl := Nat.eq_of_beq_eq_true h.1
  have hc := List.all_eq_true.mp h.2 j' (List.mem_range.mpr hj')
  rw [run_ent Fs _ _ _ _ hc t ht, gatherRun_ent _ j' t (by rw [hl]; exact ht)]

/-! ### Segments -/

/-- One segment `(c, u, v)` given the type `w` of `c` and its index `c'` within the type. -/
noncomputable def segOKw (s : Fin 3) (TTd TCd : Fin 8 → Fin 8 → Fin 8 → List (List ℕ)) (Zd : Fin 8 → Fin 8 → Fin 8 → Bool)
    (Fs : List ℕ) (w : Fin 8) (c' : ℕ) (u v : Fin 8) : Bool :=
  if w ≤ u ∧ v ≤ u then
    if v ≤ w then
      (if Zd v w u then zeroRunsOK Fs (x2SOff s v) (nS s v) (x2SOff s u) (nS s u)
        else wideRowOK Fs ((TTd v w u).getD c' []) (x2SOff s v) (nS s v) (x2SOff s u) (nS s u))
    else
      (if Zd w v u then zeroRunsOK Fs (x2SOff s v) (nS s v) (x2SOff s u) (nS s u)
        else wideRowOK Fs ((TCd w v u).getD c' []) (x2SOff s v) (nS s v) (x2SOff s u) (nS s u))
  else if u < w ∧ u < v then
    if v ≤ w then
      (if Zd u v w then zeroRunsOK Fs (x2SOff s v) (nS s v) (x2SOff s u) (nS s u)
        else gatherRowsOK Fs (TTd u v w) c' (x2SOff s v) (nS s v) (x2SOff s u) (nS s u))
    else
      (if Zd u w v then zeroRunsOK Fs (x2SOff s v) (nS s v) (x2SOff s u) (nS s u)
        else gatherPosOK Fs ((TTd u w v).getD c' []) (x2SOff s v) (nS s v) (x2SOff s u) (nS s u))
  else
    if v ≤ w then
      (if Zd v u w then zeroRunsOK Fs (x2SOff s v) (nS s v) (x2SOff s u) (nS s u)
        else gatherRowsOK Fs (TCd v u w) c' (x2SOff s v) (nS s v) (x2SOff s u) (nS s u))
    else
      (if Zd w u v then zeroRunsOK Fs (x2SOff s v) (nS s v) (x2SOff s u) (nS s u)
        else gatherPosOK Fs ((TCd w u v).getD c' []) (x2SOff s v) (nS s v) (x2SOff s u) (nS s u))

/-- One segment of column `c`. -/
noncomputable def segOK (s : Fin 3) (TTd TCd : Fin 8 → Fin 8 → Fin 8 → List (List ℕ)) (Zd : Fin 8 → Fin 8 → Fin 8 → Bool)
    (Fs : List ℕ) (c : ℕ) (u v : Fin 8) : Bool :=
  segOKw s TTd TCd Zd Fs (typeS s c) (c - x2SOff s (typeS s c)) u v

/-- The T-tables of the directory hold `σ · x2EmbedS` at the labels of their sorted triples. -/
def DirSpecS (s : Fin 3) (N : X2Blocks s) (TTd TCd : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) : Prop :=
  ∀ t0 t1 t2 : Fin 8, t0 ≤ t1 → t1 ≤ t2 →
    (Zd t0 t1 t2 = true → ZspecS s N t0 t1 t2) ∧
      (Zd t0 t1 t2 = false → TTspecS s N t0 t1 t2 (TTd t0 t1 t2) ∧ TCspecS s N t0 t1 t2 (TCd t0 t1 t2))

theorem E_jci (s : Fin 3) (N : X2Blocks s) (i j c : Fin 282) :
    x2EmbedS x2DataConcrete s N i j c = x2EmbedS x2DataConcrete s N j c i := by
  rw [x2EmbedS_swap01 x2DataConcrete s N j i c, x2EmbedS_swap12 x2DataConcrete s N j c i]

theorem E_cji (s : Fin 3) (N : X2Blocks s) (i j c : Fin 282) :
    x2EmbedS x2DataConcrete s N i j c = x2EmbedS x2DataConcrete s N c j i := by
  rw [E_jci, x2EmbedS_swap01 x2DataConcrete s N c j i]

theorem E_icj (s : Fin 3) (N : X2Blocks s) (i j c : Fin 282) :
    x2EmbedS x2DataConcrete s N i j c = x2EmbedS x2DataConcrete s N i c j := by
  rw [x2EmbedS_swap12 x2DataConcrete s N i c j]

theorem E_jic (s : Fin 3) (N : X2Blocks s) (i j c : Fin 282) :
    x2EmbedS x2DataConcrete s N i j c = x2EmbedS x2DataConcrete s N j i c := by
  rw [x2EmbedS_swap01 x2DataConcrete s N j i c]

theorem E_cij (s : Fin 3) (N : X2Blocks s) (i j c : Fin 282) :
    x2EmbedS x2DataConcrete s N i j c = x2EmbedS x2DataConcrete s N c i j := by
  rw [E_icj, x2EmbedS_swap01 x2DataConcrete s N c i j]

theorem segOK_sound (s : Fin 3) (N : X2Blocks s) (TTd TCd : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) (hdir : DirSpecS s N TTd TCd Zd) (hdec : labelDecompS s)
    (hty : typeOKS s) (Fs : List ℕ) (c : Fin 282) (u v : Fin 8) (h : segOK s TTd TCd Zd Fs c u v = true) :
    ∀ j' < nS s v, ∀ i' < nS s u,
      (ent 384 (384 - 1) (Fs.getD ((x2SOff s v + j') / 94) 0) (((x2SOff s v + j') % 94) * 282 + x2SOff s u + i') : ℚ) =
        1108531032609225922165724911675932935547910848716289179910144000 *
          x2EmbedS x2DataConcrete s N (slab s u i') (slab s v j') c := by
  intro j' hj' i' hi'
  obtain ⟨_, hclt, hceq⟩ := hdec c
  unfold segOK at h
  rw [hty c] at h
  generalize hw : (x2SLabel s c).1 = w at h hclt hceq
  generalize hc' : c.val - x2SOff s w = c' at h hclt hceq
  have hcc : c = slab s w c' := hceq.symm
  rw [hcc]
  unfold segOKw at h
  by_cases hA : w ≤ u ∧ v ≤ u
  · rw [if_pos hA] at h
    by_cases hvw : v ≤ w
    · rw [if_pos hvw] at h
      have hsp := hdir v w u hvw hA.1
      by_cases hZ : Zd v w u = true
      · rw [if_pos hZ] at h
        rw [zeroRunsOK_sound Fs _ _ _ _ h j' hj' i' hi', E_jci, hsp.1 hZ j' hj' c' hclt i' hi']
        norm_num
      · rw [if_neg hZ] at h
        rw [wideRowOK_sound Fs _ _ _ _ _ h j' hj' i' hi', E_jci]
        exact (hsp.2 (by simpa using hZ)).1 j' hj' c' hclt i' hi'
    · rw [if_neg hvw] at h
      have hwv : w ≤ v := le_of_lt (not_le.mp hvw)
      have hsp := hdir w v u hwv hA.2
      by_cases hZ : Zd w v u = true
      · rw [if_pos hZ] at h
        rw [zeroRunsOK_sound Fs _ _ _ _ h j' hj' i' hi', E_cji, hsp.1 hZ c' hclt j' hj' i' hi']
        norm_num
      · rw [if_neg hZ] at h
        rw [wideRowOK_sound Fs _ _ _ _ _ h j' hj' i' hi', E_cji]
        exact (hsp.2 (by simpa using hZ)).2 c' hclt j' hj' i' hi'
  · rw [if_neg hA] at h
    by_cases hB : u < w ∧ u < v
    · rw [if_pos hB] at h
      by_cases hvw : v ≤ w
      · rw [if_pos hvw] at h
        have hsp := hdir u v w (le_of_lt hB.2) hvw
        by_cases hZ : Zd u v w = true
        · rw [if_pos hZ] at h
          rw [zeroRunsOK_sound Fs _ _ _ _ h j' hj' i' hi', hsp.1 hZ i' hi' j' hj' c' hclt]
          norm_num
        · rw [if_neg hZ] at h
          rw [gatherRowsOK_sound Fs _ _ _ _ _ _ h j' hj' i' hi']
          exact (hsp.2 (by simpa using hZ)).1 i' hi' j' hj' c' hclt
      · rw [if_neg hvw] at h
        have hwv : w ≤ v := le_of_lt (not_le.mp hvw)
        have hsp := hdir u w v (le_of_lt hB.1) hwv
        by_cases hZ : Zd u w v = true
        · rw [if_pos hZ] at h
          rw [zeroRunsOK_sound Fs _ _ _ _ h j' hj' i' hi', E_icj, hsp.1 hZ i' hi' c' hclt j' hj']
          norm_num
        · rw [if_neg hZ] at h
          rw [gatherPosOK_sound Fs _ _ _ _ _ h j' hj' i' hi', E_icj]
          exact (hsp.2 (by simpa using hZ)).1 i' hi' c' hclt j' hj'
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
          rw [zeroRunsOK_sound Fs _ _ _ _ h j' hj' i' hi', E_jic, hsp.1 hZ j' hj' i' hi' c' hclt]
          norm_num
        · rw [if_neg hZ] at h
          rw [gatherRowsOK_sound Fs _ _ _ _ _ _ h j' hj' i' hi', E_jic]
          exact (hsp.2 (by simpa using hZ)).2 j' hj' i' hi' c' hclt
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
          rw [zeroRunsOK_sound Fs _ _ _ _ h j' hj' i' hi', E_cij, hsp.1 hZ c' hclt i' hi' j' hj']
          norm_num
        · rw [if_neg hZ] at h
          rw [gatherPosOK_sound Fs _ _ _ _ _ h j' hj' i' hi', E_cij]
          exact (hsp.2 (by simpa using hZ)).2 c' hclt i' hi' j' hj'

/-! ### hT0 of the S pipeline -/

/-- The three fibers of column `c` of an input table. -/
def colFibers (f0 : List (List ℕ)) (c : ℕ) : List ℕ := [x2Tab f0 0 c, x2Tab f0 1 c, x2Tab f0 2 c]

theorem colFibers_getD (f0 : List (List ℕ)) (c r : ℕ) (hr : r < 3) : (colFibers f0 c).getD r 0 = x2Tab f0 r c := by
  interval_cases r <;> rfl

/-- hT0 of the S-pipeline transfer theorems for every cell, from all segments. -/
theorem hT0S_of_segs (s : Fin 3) (N : X2Blocks s) (TTd TCd : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) (hdir : DirSpecS s N TTd TCd Zd) (hdec : labelDecompS s)
    (hty : typeOKS s) (f0 : List (List ℕ))
    (hchk : ∀ c : Fin 282, ∀ u v : Fin 8, segOK s TTd TCd Zd (colFibers f0 c) c u v = true) :
    ∀ (i : Fin 282) (j : Fin 282) (c : Fin 282), x2EmbedS x2DataConcrete s N i j c =
      (ent 384 (384 - 1) (x2Tab f0 (j.val / 94) c) ((j.val % 94) * 282 + i.val) : ℚ) /
        1108531032609225922165724911675932935547910848716289179910144000 := by
  intro i j c
  obtain ⟨hil, hilt, hieq⟩ := hdec i
  obtain ⟨hjl, hjlt, hjeq⟩ := hdec j
  have h := segOK_sound s N TTd TCd Zd hdir hdec hty (colFibers f0 c) c (x2SLabel s i).1 (x2SLabel s j).1
    (hchk c _ _) _ hjlt _ hilt
  have ei : (j.val % 94) * 282 + x2SOff s (x2SLabel s i).1 + (i.val - x2SOff s (x2SLabel s i).1) =
      (j.val % 94) * 282 + i.val := by omega
  rw [hieq, hjeq, Nat.add_sub_cancel' hjl, ei, colFibers_getD f0 c _ (by omega)] at h
  rw [eq_div_iff (by norm_num), h]
  ring

/-! ### Checks over ranges of columns -/

/-- All segments of the columns `lo ≤ c < lo + cnt`, the fibers taken from the table rows in order. -/
noncomputable def colsChunkOK (s : Fin 3) (TTd TCd : Fin 8 → Fin 8 → Fin 8 → List (List ℕ)) (Zd : Fin 8 → Fin 8 → Fin 8 → Bool)
    (f0 : List (List ℕ)) (lo cnt : ℕ) : Bool :=
  (List.zip (List.range cnt) (List.zip ((f0.getD 0 []).drop lo)
      (List.zip ((f0.getD 1 []).drop lo) ((f0.getD 2 []).drop lo)))).all
    (fun p => (List.finRange 8).all (fun u => (List.finRange 8).all (fun v =>
      segOK s TTd TCd Zd [p.2.1, p.2.2.1, p.2.2.2] (lo + p.1) u v)))

theorem getD_drop' (l : List ℕ) (lo k : ℕ) : (l.drop lo).getD k 0 = l.getD (lo + k) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_zip' {α β : Type*} (l1 : List α) (l2 : List β) (k : ℕ) (d1 : α) (d2 : β) (h1 : k < l1.length)
    (h2 : k < l2.length) : (List.zip l1 l2).getD k (d1, d2) = (l1.getD k d1, l2.getD k d2) := by
  rw [List.getD_eq_getElem _ _ (by simp [h1, h2]), List.getElem_zip, List.getD_eq_getElem _ _ h1,
    List.getD_eq_getElem _ _ h2]

theorem mem_range_zip {α : Type*} (M : List α) (n : ℕ) (hlen : n ≤ M.length) (d : α) (k : ℕ) (hk : k < n) :
    (k, M.getD k d) ∈ List.zip (List.range n) M := by
  have hz : k < (List.zip (List.range n) M).length := by simp; omega
  have h1 := List.getElem_mem hz
  rw [List.getElem_zip, List.getElem_range] at h1
  rwa [List.getD_eq_getElem _ _ (by omega)]

theorem colsChunkOK_sound (s : Fin 3) (TTd TCd : Fin 8 → Fin 8 → Fin 8 → List (List ℕ))
    (Zd : Fin 8 → Fin 8 → Fin 8 → Bool) (f0 : List (List ℕ)) (hlen : ∀ r < 3, (f0.getD r []).length = 282)
    (lo cnt : ℕ) (hlc : lo + cnt ≤ 282) (h : colsChunkOK s TTd TCd Zd f0 lo cnt = true) :
    ∀ c : ℕ, lo ≤ c → c < lo + cnt → ∀ u v : Fin 8, segOK s TTd TCd Zd (colFibers f0 c) c u v = true := by
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

end X2
end ThreeCopyQutritWerner
