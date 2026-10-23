module

public import ThreeCopyQutritWerner.CertificateDiagrams
public import ThreeCopyQutritWerner.CertificateLocalFramesData
public import ThreeCopyQutritWerner.CertificateX2PackedCore

@[expose] public section


/-!
# Packed kernel checks of local diagram compressions (generic part)

For a sparse integer frame `U = certificateMatrixFromSparseEntries E` (rows: the 729 words
`Fin 6 → Fin 3`) and a local diagram `certificateLocalDiagram S σ`, the compression
`(Uᵀ D U) i j = ∑_w U (r w) i * U (c w) j` (`certificateLocalDiagram_compression`) is evaluated by
the kernel with packed natural numbers:

* words are coded in base 3 (`wcode`, digit `k` of weight `3^k`, Mathlib's `finFunctionFinEquiv`),
  and the swapped words of the diagram are digit selections of the code (`sel6`);
* each frame gives packed row tables (`tab`): the positive and negative parts of the row of a word,
  as a polynomial in `2^W` (`rowPoly`), stored in the slot of the word's code;
* the kernel reads rows by shift and mask (`ext`), and products of a stretched row with a plain
  row are the outer products of rows, laid out row-major.

This module proves the generic facts: table extraction returns the row polynomials
(`ext_tab`), and frames are differences of counts (`sparse_eq_cnt`).
-/

set_option maxRecDepth 100000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2Sites

open X2

/-- Words of the six local registers. -/
abbrev Word := Fin 6 → Fin 3

/-! ## Word codes -/

/-- Base-3 code of a word, digit `k` of weight `3^k`. -/
def wcode (w : Word) : ℕ :=
  Nat.add (w 0).val (Nat.mul 3 (Nat.add (w 1).val (Nat.mul 3 (Nat.add (w 2).val (Nat.mul 3 (Nat.add (w 3).val (Nat.mul 3 (Nat.add (w 4).val (Nat.mul 3 ((w 5).val))))))))))

theorem wcode_eq (w : Word) : wcode w = (finFunctionFinEquiv w : ℕ) := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_six]
  simp only [wcode, Nat.add_eq, Nat.mul_eq, Fin.val_zero, Fin.val_one, Fin.val_two]
  have h3 : ((3 : Fin 6) : ℕ) = 3 := rfl
  have h4 : ((4 : Fin 6) : ℕ) = 4 := rfl
  have h5 : ((5 : Fin 6) : ℕ) = 5 := rfl
  rw [h3, h4, h5]
  ring

/-- Word of a code: digit `k` is `a / 3^k % 3`. -/
def wdec (a : ℕ) : Word := fun k => ⟨a / 3 ^ (k : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩

theorem wdec_eq_symm (a : Fin (3 ^ 6)) : wdec a = finFunctionFinEquiv.symm a := by
  funext k
  apply Fin.ext
  rfl

theorem wcode_lt (w : Word) : wcode w < 729 := by
  rw [wcode_eq]
  exact (finFunctionFinEquiv w).isLt

theorem wdec_wcode (w : Word) : wdec (wcode w) = w := by
  have h := wdec_eq_symm (finFunctionFinEquiv w)
  rw [Equiv.symm_apply_apply] at h
  rw [wcode_eq]
  exact h

theorem wcode_wdec (a : ℕ) (ha : a < 729) : wcode (wdec a) = a := by
  have h := wdec_eq_symm ⟨a, ha⟩
  rw [wcode_eq]
  simp only at h
  rw [h, Equiv.apply_symm_apply]

theorem eq_wdec_iff (w : Word) (a : ℕ) (ha : a < 729) : w = wdec a ↔ wcode w = a := by
  constructor
  · rintro rfl
    exact wcode_wdec a ha
  · rintro rfl
    exact (wdec_wcode w).symm

/-- Sums over words are sums over codes. -/
theorem sum_words {M : Type*} [AddCommMonoid M] (f : Word → M) :
    ∑ w : Word, f w = ∑ a ∈ Finset.range 729, f (wdec a) := by
  calc ∑ w : Word, f w = ∑ a : Fin (3 ^ 6), f (finFunctionFinEquiv.symm a) :=
        (Equiv.sum_comp finFunctionFinEquiv.symm f).symm
    _ = ∑ a : Fin (3 ^ 6), f (wdec a) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [wdec_eq_symm]
    _ = ∑ a ∈ Finset.range (3 ^ 6), f (wdec a) := Fin.sum_univ_eq_sum_range (fun a => f (wdec a)) _
    _ = ∑ a ∈ Finset.range 729, f (wdec a) := by norm_num

/-! ## Digit selections -/

/-- Digit of `a` at the power `p` (`p = 3^j`). -/
def dg (a p : ℕ) : ℕ := Nat.mod (Nat.div a p) 3

/-- Code of the word `k ↦ digit (a, j_k)`, from the six powers `p_k = 3^(j_k)`. -/
def sel6 (a p0 p1 p2 p3 p4 p5 : ℕ) : ℕ :=
  Nat.add (dg a p0) (Nat.mul 3 (Nat.add (dg a p1) (Nat.mul 3 (Nat.add (dg a p2) (Nat.mul 3 (Nat.add (dg a p3) (Nat.mul 3 (Nat.add (dg a p4) (Nat.mul 3 ((dg a p5)))))))))))

theorem sel6_eq (a : ℕ) (α : Fin 6 → Fin 6) :
    sel6 a (3 ^ (α 0 : ℕ)) (3 ^ (α 1 : ℕ)) (3 ^ (α 2 : ℕ)) (3 ^ (α 3 : ℕ)) (3 ^ (α 4 : ℕ))
      (3 ^ (α 5 : ℕ)) = wcode (fun k => wdec a (α k)) := rfl

theorem wdec_sel6 (a : ℕ) (α : Fin 6 → Fin 6) :
    wdec (sel6 a (3 ^ (α 0 : ℕ)) (3 ^ (α 1 : ℕ)) (3 ^ (α 2 : ℕ)) (3 ^ (α 3 : ℕ)) (3 ^ (α 4 : ℕ))
      (3 ^ (α 5 : ℕ))) = fun k => wdec a (α k) := by
  rw [sel6_eq, wdec_wcode]

theorem sel6_lt (a : ℕ) (α : Fin 6 → Fin 6) :
    sel6 a (3 ^ (α 0 : ℕ)) (3 ^ (α 1 : ℕ)) (3 ^ (α 2 : ℕ)) (3 ^ (α 3 : ℕ)) (3 ^ (α 4 : ℕ))
      (3 ^ (α 5 : ℕ)) < 729 := by
  rw [sel6_eq]
  exact wcode_lt _

/-- Positions read by the row word of a diagram: `S` itself, `σ` elsewhere. -/
def rowPos (S : Finset (Fin 6)) (σ : Equiv.Perm (Fin 6)) (k : Fin 6) : Fin 6 :=
  if k ∈ S then k else σ k

/-- Positions read by the column word of a diagram: `σ` on `S`, itself elsewhere. -/
def colPos (S : Finset (Fin 6)) (σ : Equiv.Perm (Fin 6)) (k : Fin 6) : Fin 6 :=
  if k ∈ S then σ k else k

theorem wordSwap_row (S : Finset (Fin 6)) (σ : Equiv.Perm (Fin 6)) (w : Word) :
    certificateWordSwap S (w ∘ σ) w = fun k => w (rowPos S σ k) := by
  funext k
  unfold certificateWordSwap rowPos
  by_cases h : k ∈ S
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    rfl

theorem wordSwap_col (S : Finset (Fin 6)) (σ : Equiv.Perm (Fin 6)) (w : Word) :
    certificateWordSwap S w (w ∘ σ) = fun k => w (colPos S σ k) := by
  funext k
  unfold certificateWordSwap colPos
  by_cases h : k ∈ S
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]

/-! ## Frames as counts -/

/-- Positive (`neg = false`) or negative (`neg = true`) part of the entries at `(w, j)`. -/
def cnt {m : ℕ} (neg : Bool) (E : List (Word × Fin m × ℤ)) (w : Word) (j : Fin m) : ℕ :=
  (E.map (fun e => if e.1 = w ∧ e.2.1 = j then
    (bif neg then (-e.2.2).toNat else e.2.2.toNat) else 0)).sum

theorem cnt_nil {m : ℕ} (neg : Bool) (w : Word) (j : Fin m) : cnt neg [] w j = 0 := rfl

theorem cnt_cons {m : ℕ} (neg : Bool) (e : Word × Fin m × ℤ) (E : List (Word × Fin m × ℤ))
    (w : Word) (j : Fin m) :
    cnt neg (e :: E) w j = (if e.1 = w ∧ e.2.1 = j then
      (bif neg then (-e.2.2).toNat else e.2.2.toNat) else 0) + cnt neg E w j := by
  unfold cnt
  rw [List.map_cons, List.sum_cons]

theorem sparse_eq_cnt {m : ℕ} (E : List (Word × Fin m × ℤ)) (w : Word) (j : Fin m) :
    certificateMatrixFromSparseEntries E w j = (cnt false E w j : ℤ) - (cnt true E w j : ℤ) := by
  induction E with
  | nil => rfl
  | cons e es ih =>
    have h1 : certificateMatrixFromSparseEntries (e :: es) w j =
        (if e.1 = w ∧ e.2.1 = j then e.2.2 else 0) + certificateMatrixFromSparseEntries es w j := by
      unfold certificateMatrixFromSparseEntries
      rw [List.map_cons, List.sum_cons]
    rw [h1, ih, cnt_cons, cnt_cons]
    by_cases hc : e.1 = w ∧ e.2.1 = j
    · rw [if_pos hc, if_pos hc, if_pos hc]
      have hv := Int.toNat_sub_toNat_neg e.2.2
      simp only [Bool.cond_false, Bool.cond_true]
      push_cast
      linarith
    · rw [if_neg hc, if_neg hc, if_neg hc]
      push_cast
      ring

/-- Total absolute weight of the entries. -/
def absSum {m : ℕ} (E : List (Word × Fin m × ℤ)) : ℕ := (E.map (fun e => e.2.2.natAbs)).sum

theorem cnt_le_absSum {m : ℕ} (neg : Bool) (E : List (Word × Fin m × ℤ)) (w : Word) (j : Fin m) :
    cnt neg E w j ≤ absSum E := by
  induction E with
  | nil => exact le_refl _
  | cons e es ih =>
    rw [cnt_cons]
    have hs : absSum (e :: es) = e.2.2.natAbs + absSum es := by
      unfold absSum
      rw [List.map_cons, List.sum_cons]
    rw [hs]
    have he : (if e.1 = w ∧ e.2.1 = j then (bif neg then (-e.2.2).toNat else e.2.2.toNat) else 0)
        ≤ e.2.2.natAbs := by
      split_ifs
      · cases neg
        · simp only [Bool.cond_false]
          omega
        · simp only [Bool.cond_true]
          omega
      · exact Nat.zero_le _
    omega

/-! ## Packed row tables -/

/-- Packed table of one sign part of a sparse frame: entry `e` adds its weight at bit
`W * (col * str) + WY * wcode word`. -/
def tab {m : ℕ} (W WY str : ℕ) (neg : Bool) : List (Word × Fin m × ℤ) → ℕ
  | [] => 0
  | e :: es => Nat.add (Nat.mul (bif neg then (-e.2.2).toNat else e.2.2.toNat)
      (Nat.shiftLeft 1 (Nat.add (Nat.mul W (Nat.mul e.2.1.val str)) (Nat.mul WY (wcode e.1)))))
      (tab W WY str neg es)

/-- The row polynomial of a word: `∑_j cnt (w, j) (2^W)^(j * str)`. -/
def rowPoly {m : ℕ} (W str : ℕ) (neg : Bool) (E : List (Word × Fin m × ℤ)) (w : Word) : ℕ :=
  ∑ j : Fin m, cnt neg E w j * 2 ^ (W * (j * str))

theorem rowPoly_cons {m : ℕ} (W str : ℕ) (neg : Bool) (e : Word × Fin m × ℤ)
    (E : List (Word × Fin m × ℤ)) (w : Word) :
    rowPoly W str neg (e :: E) w = (if e.1 = w then
      (bif neg then (-e.2.2).toNat else e.2.2.toNat) * 2 ^ (W * (e.2.1 * str)) else 0) +
        rowPoly W str neg E w := by
  unfold rowPoly
  simp only [cnt_cons, add_mul, Finset.sum_add_distrib]
  congr 1
  by_cases hw : e.1 = w
  · rw [if_pos hw]
    simp only [hw, true_and]
    rw [Finset.sum_eq_single e.2.1]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg (fun h => hj h.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hw]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (fun h => hw h.1), zero_mul]

theorem tab_eq {m : ℕ} (W WY str : ℕ) (neg : Bool) (E : List (Word × Fin m × ℤ)) :
    tab W WY str neg E = ∑ c ∈ Finset.range 729, rowPoly W str neg E (wdec c) * 2 ^ (WY * c) := by
  induction E with
  | nil =>
    symm
    apply Finset.sum_eq_zero
    intro c _
    unfold rowPoly
    simp [cnt_nil]
  | cons e es ih =>
    have h1 : tab W WY str neg (e :: es) =
        (bif neg then (-e.2.2).toNat else e.2.2.toNat) * 2 ^ (W * (e.2.1 * str)) *
          2 ^ (WY * wcode e.1) + tab W WY str neg es := by
      show Nat.add (Nat.mul _ (Nat.shiftLeft 1 _)) _ = _
      rw [Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.add_eq,
        Nat.mul_eq, Nat.mul_eq, Nat.mul_eq, pow_add]
      ring
    have hsingle : ∑ c ∈ Finset.range 729, (if e.1 = wdec c then
        (bif neg then (-e.2.2).toNat else e.2.2.toNat) * 2 ^ (W * (e.2.1 * str)) else 0) *
          2 ^ (WY * c) =
        (bif neg then (-e.2.2).toNat else e.2.2.toNat) * 2 ^ (W * (e.2.1 * str)) *
          2 ^ (WY * wcode e.1) := by
      rw [Finset.sum_eq_single (wcode e.1)]
      · rw [if_pos (wdec_wcode e.1).symm]
      · intro c hc hne
        rw [if_neg, zero_mul]
        intro h
        apply hne
        rw [(eq_wdec_iff e.1 c (Finset.mem_range.mp hc)).mp h]
      · intro h
        exact absurd (Finset.mem_range.mpr (wcode_lt e.1)) h
    rw [h1, ih]
    simp only [rowPoly_cons, add_mul, Finset.sum_add_distrib]
    rw [hsingle]

/-- Read the slot `c` (width `WY`) of a packed natural, by shift and mask. -/
def ext (T WY c : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight T (Nat.mul WY c)) (Nat.sub (Nat.shiftLeft 1 WY) 1)

theorem ext_eq (T WY c : ℕ) : ext T WY c = T / (2 ^ WY) ^ c % 2 ^ WY := by
  show (T >>> (WY * c)) &&& ((1 <<< WY) - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod,
    pow_mul]

theorem rowPoly_lt {m : ℕ} (W str : ℕ) (neg : Bool) (E : List (Word × Fin m × ℤ)) (w : Word)
    (hW : absSum E < 2 ^ W) (hstr : 1 ≤ str) :
    rowPoly W str neg E w < 2 ^ (W * str * m) := by
  unfold rowPoly
  let f : ℕ → ℕ := fun s => if h : s < m then cnt neg E w ⟨s, h⟩ else 0
  have hB : 2 ^ W ≤ 2 ^ (W * str) := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right W hstr)
  have hf : ∀ s, f s < 2 ^ (W * str) := by
    intro s
    by_cases h : s < m
    · simp only [f, dif_pos h]
      exact lt_of_le_of_lt (cnt_le_absSum neg E w _) (lt_of_lt_of_le hW hB)
    · simp only [f, dif_neg h]
      positivity
  have hsum : ∑ j : Fin m, cnt neg E w j * 2 ^ (W * (j * str)) =
      ∑ s ∈ Finset.range m, f s * (2 ^ (W * str)) ^ s := by
    rw [← Fin.sum_univ_eq_sum_range (fun s => f s * (2 ^ (W * str)) ^ s) m]
    apply Finset.sum_congr rfl
    intro j _
    simp only [f, dif_pos j.isLt]
    rw [← pow_mul]
    congr 2
    ring
  rw [hsum]
  calc ∑ s ∈ Finset.range m, f s * (2 ^ (W * str)) ^ s < (2 ^ (W * str)) ^ m :=
        sum_digits_lt (2 ^ (W * str)) f hf m
    _ = 2 ^ (W * str * m) := (pow_mul 2 (W * str) m).symm

/-- Table extraction returns the row polynomial of the word. -/
theorem ext_tab {m : ℕ} (W WY str : ℕ) (neg : Bool) (E : List (Word × Fin m × ℤ))
    (hb : ∀ w, rowPoly W str neg E w < 2 ^ WY) (c : ℕ) (hc : c < 729) :
    ext (tab W WY str neg E) WY c = rowPoly W str neg E (wdec c) := by
  rw [ext_eq, tab_eq]
  have h := sum_digit (2 ^ WY) 729 (fun c => rowPoly W str neg E (wdec c)) (by positivity)
    (fun s => hb _) c hc
  simpa only [pow_mul] using h

/-! ## Row masks -/

/-- Bit `wcode word` for every entry. -/
def rmask {m : ℕ} : List (Word × Fin m × ℤ) → ℕ
  | [] => 0
  | e :: es => Nat.lor (Nat.shiftLeft 1 (wcode e.1)) (rmask es)

theorem rmask_false {m : ℕ} (E : List (Word × Fin m × ℤ)) (c : ℕ)
    (h : (rmask E).testBit c = false) : ∀ e ∈ E, wcode e.1 ≠ c := by
  induction E with
  | nil => intro e he; exact absurd he (List.not_mem_nil)
  | cons e es ih =>
    have h1 : rmask (e :: es) = 2 ^ wcode e.1 ||| rmask es := by
      show Nat.lor (Nat.shiftLeft 1 _) _ = _
      rw [Nat.lor_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]
    rw [h1, Nat.testBit_or, Bool.or_eq_false_iff] at h
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | hes
    · intro hc
      rw [hc, Nat.testBit_two_pow_self] at h
      exact absurd h.1 (by decide)
    · exact ih h.2 e' hes

theorem rowPoly_zero_of_mask {m : ℕ} (W str : ℕ) (neg : Bool) (E : List (Word × Fin m × ℤ))
    (c : ℕ) (hc : c < 729) (h : (rmask E).testBit c = false) : rowPoly W str neg E (wdec c) = 0 := by
  have hz : ∀ j, cnt neg E (wdec c) j = 0 := by
    intro j
    unfold cnt
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    rw [if_neg]
    intro hwe
    exact rmask_false E c h e he ((eq_wdec_iff e.1 c hc).mp hwe.1)
  unfold rowPoly
  apply Finset.sum_eq_zero
  intro j _
  rw [hz, zero_mul]

theorem sparse_zero_of_mask {m : ℕ} (E : List (Word × Fin m × ℤ)) (c : ℕ) (hc : c < 729)
    (h : (rmask E).testBit c = false) (j : Fin m) :
    certificateMatrixFromSparseEntries E (wdec c) j = 0 := by
  rw [sparse_eq_cnt]
  have hz : ∀ neg, cnt neg E (wdec c) j = 0 := by
    intro neg
    unfold cnt
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    rw [if_neg]
    intro hwe
    exact rmask_false E c h e he ((eq_wdec_iff e.1 c hc).mp hwe.1)
  rw [hz false, hz true]
  rfl

end X2Sites
end ThreeCopyQutritWerner
