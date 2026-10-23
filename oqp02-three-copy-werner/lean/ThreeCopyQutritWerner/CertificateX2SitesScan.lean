module

public import ThreeCopyQutritWerner.CertificateX2SitesCore

@[expose] public section


/-!
# The packed compression scan and its soundness

`scanM` runs over the 729 word codes `a`; the row and column words of the diagram are digit
selections of `a` (`sel6`). For every frame type (`TyTab`, built by `mkTy` from the frame's
entries) whose row mask contains both words, the positive and negative parts of the two rows are
read from the packed tables and their outer products are added, at the type's offset, to two
accumulators. `finish` compares `base + Pos - Neg` with a candidate fiber `F` (offset `2^(W-1)`
slots of width `W`).

`scan_sound`: if the check passes, slot `off t + i * m t + j` of `F` is
`∑_a U_t(row word, i) * U_t(column word, j)`; `comp_sound`: that is the compression entry
`(U_tᵀ * certificateLocalDiagram S σ * U_t) i j`.
-/

set_option maxRecDepth 100000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2Sites

open X2

/-! ## Kernel-evaluated scan -/

/-- Packed tables of one frame type. -/
structure TyTab where
  sp : ℕ
  sn : ℕ
  pp : ℕ
  pn : ℕ
  wys : ℕ
  wyp : ℕ
  sh : ℕ
  msk : ℕ

/-- Tables of one frame type: stretched rows (`str = m`) and plain rows (`str = 1`), both signs,
slot widths, the output offset and the row mask. -/
def mkTy {m : ℕ} (W off : ℕ) (E : List (Word × Fin m × ℤ)) : TyTab :=
  ⟨tab W (W * m * m) m false E, tab W (W * m * m) m true E, tab W (W * m) 1 false E,
    tab W (W * m) 1 true E, W * m * m, W * m, W * off, rmask E⟩

def contrib4 (sp sn pp pn sh : ℕ) (st : ℕ × ℕ) : ℕ × ℕ :=
  (Nat.add st.1 (Nat.shiftLeft (Nat.add (Nat.mul sp pp) (Nat.mul sn pn)) sh),
   Nat.add st.2 (Nat.shiftLeft (Nat.add (Nat.mul sp pn) (Nat.mul sn pp)) sh))

def contrib (ty : TyTab) (r c : ℕ) (st : ℕ × ℕ) : ℕ × ℕ :=
  contrib4 (ext ty.sp ty.wys r) (ext ty.sn ty.wys r) (ext ty.pp ty.wyp c) (ext ty.pn ty.wyp c)
    ty.sh st

def contribM (ty : TyTab) (r c : ℕ) (st : ℕ × ℕ) : ℕ × ℕ :=
  @Bool.casesOn (fun _ => ℕ × ℕ) (Nat.testBit ty.msk r && Nat.testBit ty.msk c) st
    (contrib ty r c st)

def contribAllM (tys : List TyTab) (r c : ℕ) (st : ℕ × ℕ) : ℕ × ℕ :=
  @List.rec TyTab (fun _ => ℕ × ℕ → ℕ × ℕ) (fun st => st)
    (fun ty _ ih st => ih (contribM ty r c st)) tys st

def leaf (M : ℕ) (tys : List TyTab) (r c : ℕ) (st : ℕ × ℕ) : ℕ × ℕ :=
  @Bool.casesOn (fun _ => ℕ × ℕ) (Nat.testBit M r && Nat.testBit M c) st
    (contribAllM tys r c st)

def scanM (M : ℕ) (tys : List TyTab) (p0 p1 p2 p3 p4 p5 q0 q1 q2 q3 q4 q5 : ℕ) (n : ℕ)
    (st : ℕ × ℕ) : ℕ × ℕ :=
  @Nat.rec (fun _ => ℕ × ℕ → ℕ × ℕ) (fun st => st)
    (fun a ih st => ih (leaf M tys (sel6 a p0 p1 p2 p3 p4 p5) (sel6 a q0 q1 q2 q3 q4 q5) st)) n st

def finish (base F : ℕ) (st : ℕ × ℕ) : Bool :=
  @Prod.casesOn ℕ ℕ (fun _ => Bool) st (fun pos neg => Nat.beq (Nat.sub (Nat.add base pos) neg) F)

/-- Bitwise or of a list. -/
def lorAll : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.lor x (lorAll xs)

theorem lorAll_false (xs : List ℕ) (c : ℕ) (h : (lorAll xs).testBit c = false) :
    ∀ x ∈ xs, x.testBit c = false := by
  induction xs with
  | nil => intro x hx; exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    have h1 : lorAll (y :: ys) = y ||| lorAll ys := rfl
    rw [h1, Nat.testBit_or, Bool.or_eq_false_iff] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact h.1
    · exact ih h.2 x hx'

/-! ## Values of one step -/

/-- Positive part added by one type for the words `r`, `c`. -/
def posT {m : ℕ} (W off : ℕ) (E : List (Word × Fin m × ℤ)) (r c : ℕ) : ℕ :=
  (rowPoly W m false E (wdec r) * rowPoly W 1 false E (wdec c) +
    rowPoly W m true E (wdec r) * rowPoly W 1 true E (wdec c)) * 2 ^ (W * off)

/-- Negative part added by one type for the words `r`, `c`. -/
def negT {m : ℕ} (W off : ℕ) (E : List (Word × Fin m × ℤ)) (r c : ℕ) : ℕ :=
  (rowPoly W m false E (wdec r) * rowPoly W 1 true E (wdec c) +
    rowPoly W m true E (wdec r) * rowPoly W 1 false E (wdec c)) * 2 ^ (W * off)

theorem posT_negT_zero {m : ℕ} (W off : ℕ) (E : List (Word × Fin m × ℤ)) (r c : ℕ)
    (hr : r < 729) (hc : c < 729)
    (h : (rmask E).testBit r = false ∨ (rmask E).testBit c = false) :
    posT W off E r c = 0 ∧ negT W off E r c = 0 := by
  unfold posT negT
  rcases h with h | h
  · rw [rowPoly_zero_of_mask W m false E r hr h, rowPoly_zero_of_mask W m true E r hr h]
    simp
  · rw [rowPoly_zero_of_mask W 1 false E c hc h, rowPoly_zero_of_mask W 1 true E c hc h]
    simp

theorem rowPoly_lt_S {m : ℕ} (W : ℕ) (neg : Bool) (E : List (Word × Fin m × ℤ)) (w : Word)
    (hW : absSum E < 2 ^ W) : rowPoly W m neg E w < 2 ^ (W * m * m) := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    simp [rowPoly]
  · exact rowPoly_lt W m neg E w hW h0

theorem rowPoly_lt_P {m : ℕ} (W : ℕ) (neg : Bool) (E : List (Word × Fin m × ℤ)) (w : Word)
    (hW : absSum E < 2 ^ W) : rowPoly W 1 neg E w < 2 ^ (W * m) := by
  have h := rowPoly_lt W 1 neg E w hW le_rfl
  simpa only [Nat.mul_one] using h

theorem contribM_mkTy {m : ℕ} (W off : ℕ) (E : List (Word × Fin m × ℤ)) (hW : absSum E < 2 ^ W)
    (r c x y : ℕ) (hr : r < 729) (hc : c < 729) :
    contribM (mkTy W off E) r c (x, y) = (x + posT W off E r c, y + negT W off E r c) := by
  unfold contribM
  have hmsk : (mkTy W off E).msk = rmask E := rfl
  rw [hmsk]
  cases hb : (Nat.testBit (rmask E) r && Nat.testBit (rmask E) c) with
  | false =>
    have h' : (rmask E).testBit r = false ∨ (rmask E).testBit c = false := by
      cases h1 : (rmask E).testBit r
      · exact Or.inl rfl
      · rw [h1, Bool.true_and] at hb
        exact Or.inr hb
    obtain ⟨h1, h2⟩ := posT_negT_zero W off E r c hr hc h'
    rw [h1, h2]
    rfl
  | true =>
    have e1 : ext (tab W (W * m * m) m false E) (W * m * m) r = rowPoly W m false E (wdec r) :=
      ext_tab W (W * m * m) m false E (fun w => rowPoly_lt_S W false E w hW) r hr
    have e2 : ext (tab W (W * m * m) m true E) (W * m * m) r = rowPoly W m true E (wdec r) :=
      ext_tab W (W * m * m) m true E (fun w => rowPoly_lt_S W true E w hW) r hr
    have e3 : ext (tab W (W * m) 1 false E) (W * m) c = rowPoly W 1 false E (wdec c) :=
      ext_tab W (W * m) 1 false E (fun w => rowPoly_lt_P W false E w hW) c hc
    have e4 : ext (tab W (W * m) 1 true E) (W * m) c = rowPoly W 1 true E (wdec c) :=
      ext_tab W (W * m) 1 true E (fun w => rowPoly_lt_P W true E w hW) c hc
    show contrib4 (ext (tab W (W * m * m) m false E) (W * m * m) r)
      (ext (tab W (W * m * m) m true E) (W * m * m) r) (ext (tab W (W * m) 1 false E) (W * m) c)
      (ext (tab W (W * m) 1 true E) (W * m) c) (W * off) (x, y) = _
    rw [e1, e2, e3, e4]
    simp only [contrib4, posT, negT, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]

theorem contribAllM_eq (L : List (TyTab × (ℕ → ℕ → ℕ) × (ℕ → ℕ → ℕ))) (r c : ℕ) :
    (∀ p ∈ L, ∀ x y, contribM p.1 r c (x, y) = (x + p.2.1 r c, y + p.2.2 r c)) →
    ∀ x y, contribAllM (L.map Prod.fst) r c (x, y) =
      (x + (L.map (fun p => p.2.1 r c)).sum, y + (L.map (fun p => p.2.2 r c)).sum) := by
  induction L with
  | nil =>
    intro _ x y
    rfl
  | cons p ps ih =>
    intro hL x y
    have h1 : contribAllM ((p :: ps).map Prod.fst) r c (x, y) =
        contribAllM (ps.map Prod.fst) r c (contribM p.1 r c (x, y)) := rfl
    rw [h1, hL p List.mem_cons_self x y,
      ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))]
    simp only [List.map_cons, List.sum_cons, Prod.mk.injEq]
    constructor <;> ring

theorem leaf_eq (M : ℕ) (L : List (TyTab × (ℕ → ℕ → ℕ) × (ℕ → ℕ → ℕ))) (r c : ℕ)
    (hL : ∀ p ∈ L, ∀ x y, contribM p.1 r c (x, y) = (x + p.2.1 r c, y + p.2.2 r c))
    (hz : (Nat.testBit M r && Nat.testBit M c) = false → ∀ p ∈ L, p.2.1 r c = 0 ∧ p.2.2 r c = 0)
    (x y : ℕ) :
    leaf M (L.map Prod.fst) r c (x, y) =
      (x + (L.map (fun p => p.2.1 r c)).sum, y + (L.map (fun p => p.2.2 r c)).sum) := by
  unfold leaf
  cases hb : (Nat.testBit M r && Nat.testBit M c) with
  | false =>
    have h1 : (L.map (fun p => p.2.1 r c)).sum = 0 := by
      apply List.sum_eq_zero
      intro z hz'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz'
      exact (hz hb p hp).1
    have h2 : (L.map (fun p => p.2.2 r c)).sum = 0 := by
      apply List.sum_eq_zero
      intro z hz'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz'
      exact (hz hb p hp).2
    rw [h1, h2]
    rfl
  | true =>
    exact contribAllM_eq L r c hL x y

theorem scanM_eq (M : ℕ) (tys : List TyTab) (α β : Fin 6 → Fin 6) (pos neg : ℕ → ℕ)
    (hleaf : ∀ a x y, leaf M tys
      (sel6 a (3 ^ (α 0 : ℕ)) (3 ^ (α 1 : ℕ)) (3 ^ (α 2 : ℕ)) (3 ^ (α 3 : ℕ)) (3 ^ (α 4 : ℕ))
        (3 ^ (α 5 : ℕ)))
      (sel6 a (3 ^ (β 0 : ℕ)) (3 ^ (β 1 : ℕ)) (3 ^ (β 2 : ℕ)) (3 ^ (β 3 : ℕ)) (3 ^ (β 4 : ℕ))
        (3 ^ (β 5 : ℕ))) (x, y) = (x + pos a, y + neg a)) :
    ∀ n x y, scanM M tys (3 ^ (α 0 : ℕ)) (3 ^ (α 1 : ℕ)) (3 ^ (α 2 : ℕ)) (3 ^ (α 3 : ℕ))
      (3 ^ (α 4 : ℕ)) (3 ^ (α 5 : ℕ)) (3 ^ (β 0 : ℕ)) (3 ^ (β 1 : ℕ)) (3 ^ (β 2 : ℕ))
      (3 ^ (β 3 : ℕ)) (3 ^ (β 4 : ℕ)) (3 ^ (β 5 : ℕ)) n (x, y) =
        (x + ∑ a ∈ Finset.range n, pos a, y + ∑ a ∈ Finset.range n, neg a) := by
  intro n
  induction n with
  | zero =>
    intro x y
    simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero]
    rfl
  | succ n ih =>
    intro x y
    show scanM M tys (3 ^ (α 0 : ℕ)) (3 ^ (α 1 : ℕ)) (3 ^ (α 2 : ℕ)) (3 ^ (α 3 : ℕ))
      (3 ^ (α 4 : ℕ)) (3 ^ (α 5 : ℕ)) (3 ^ (β 0 : ℕ)) (3 ^ (β 1 : ℕ)) (3 ^ (β 2 : ℕ))
      (3 ^ (β 3 : ℕ)) (3 ^ (β 4 : ℕ)) (3 ^ (β 5 : ℕ)) n (leaf M tys
        (sel6 n (3 ^ (α 0 : ℕ)) (3 ^ (α 1 : ℕ)) (3 ^ (α 2 : ℕ)) (3 ^ (α 3 : ℕ))
          (3 ^ (α 4 : ℕ)) (3 ^ (α 5 : ℕ)))
        (sel6 n (3 ^ (β 0 : ℕ)) (3 ^ (β 1 : ℕ)) (3 ^ (β 2 : ℕ)) (3 ^ (β 3 : ℕ))
          (3 ^ (β 4 : ℕ)) (3 ^ (β 5 : ℕ))) (x, y)) = _
    rw [hleaf n x y, ih]
    simp only [Finset.sum_range_succ, Prod.mk.injEq]
    constructor <;> ring

/-! ## Expansion of the accumulators -/

theorem posT_expand {m : ℕ} (W off : ℕ) (E : List (Word × Fin m × ℤ)) (r c : ℕ) :
    posT W off E r c = ∑ i : Fin m, ∑ j : Fin m,
      (cnt false E (wdec r) i * cnt false E (wdec c) j + cnt true E (wdec r) i * cnt true E (wdec c) j) *
        2 ^ (W * (off + i * m + j)) := by
  unfold posT rowPoly
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hp : 2 ^ (W * (off + (i : ℕ) * m + j)) =
      2 ^ (W * ((i : ℕ) * m)) * 2 ^ (W * ((j : ℕ) * 1)) * 2 ^ (W * off) := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  rw [hp]
  ring

theorem negT_expand {m : ℕ} (W off : ℕ) (E : List (Word × Fin m × ℤ)) (r c : ℕ) :
    negT W off E r c = ∑ i : Fin m, ∑ j : Fin m,
      (cnt false E (wdec r) i * cnt true E (wdec c) j + cnt true E (wdec r) i * cnt false E (wdec c) j) *
        2 ^ (W * (off + i * m + j)) := by
  unfold negT rowPoly
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hp : 2 ^ (W * (off + (i : ℕ) * m + j)) =
      2 ^ (W * ((i : ℕ) * m)) * 2 ^ (W * ((j : ℕ) * 1)) * 2 ^ (W * off) := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  rw [hp]
  ring

/-! ## Digits of a packed family -/

theorem digits_of_family (W L : ℕ) (hW1 : 1 ≤ W) {ι : Type*} [Fintype ι] (pos neg flat : ι → ℕ)
    (hflat : ∀ x, flat x < L) (hinj : Function.Injective flat)
    (hb : ∑ x, pos x < 2 ^ (W - 1)) (hb' : ∑ x, neg x < 2 ^ (W - 1)) (F : ℕ)
    (hF : F = offset W (W - 1) L + ∑ x, pos x * 2 ^ (W * flat x) - ∑ x, neg x * 2 ^ (W * flat x))
    (x : ι) : ent W (W - 1) F (flat x) = (pos x : ℤ) - neg x := by
  classical
  let P : ℕ → ℕ := fun k => ∑ y, if flat y = k then pos y else 0
  let Q : ℕ → ℕ := fun k => ∑ y, if flat y = k then neg y else 0
  have hreidx : ∀ f : ι → ℕ, ∑ y, f y * 2 ^ (W * flat y) =
      ∑ k ∈ Finset.range L, (∑ y, if flat y = k then f y else 0) * 2 ^ (W * k) := by
    intro f
    calc ∑ y, f y * 2 ^ (W * flat y)
        = ∑ y, ∑ k ∈ Finset.range L, (if flat y = k then f y * 2 ^ (W * k) else 0) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_ite_eq (Finset.range L) (flat y) (fun k => f y * 2 ^ (W * k)),
            if_pos (Finset.mem_range.mpr (hflat y))]
      _ = ∑ k ∈ Finset.range L, ∑ y, (if flat y = k then f y * 2 ^ (W * k) else 0) :=
          Finset.sum_comm
      _ = ∑ k ∈ Finset.range L, (∑ y, if flat y = k then f y else 0) * 2 ^ (W * k) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro y _
          split_ifs <;> simp
  have hPle : ∀ k, P k ≤ ∑ y, pos y := by
    intro k
    apply Finset.sum_le_sum
    intro y _
    split_ifs <;> simp
  have hQle : ∀ k, Q k ≤ ∑ y, neg y := by
    intro k
    apply Finset.sum_le_sum
    intro y _
    split_ifs <;> simp
  have hpow : 2 ^ (W - 1) + 2 ^ (W - 1) = 2 ^ W := by
    rw [← two_mul, ← pow_succ']
    congr 1
    omega
  have hbase : offset W (W - 1) L = ∑ k ∈ Finset.range L, 2 ^ (W - 1) * 2 ^ (W * k) := by
    unfold offset
    rw [repunit_eq W L hW1, Finset.mul_sum]
  have hQP : ∀ k, Q k ≤ 2 ^ (W - 1) + P k := by
    intro k
    have := hQle k
    omega
  have hF' : F = ∑ k ∈ Finset.range L, (2 ^ (W - 1) + P k - Q k) * 2 ^ (W * k) := by
    rw [hF, hreidx pos, hreidx neg, hbase, ← Finset.sum_add_distrib]
    rw [← Finset.sum_tsub_distrib]
    · apply Finset.sum_congr rfl
      intro k _
      rw [← add_mul, Nat.sub_mul]
    · intro k _
      rw [← add_mul]
      exact Nat.mul_le_mul_right _ (hQP k)
  have hdig : ∀ k, k < L → dig W F k = 2 ^ (W - 1) + P k - Q k := by
    intro k hk
    unfold dig
    rw [hF']
    have hf : ∀ s, 2 ^ (W - 1) + P s - Q s < 2 ^ W := by
      intro s
      have := hPle s
      omega
    have h := sum_digit (2 ^ W) L (fun s => 2 ^ (W - 1) + P s - Q s) (by positivity) hf k hk
    simpa only [pow_mul] using h
  have hPx : P (flat x) = pos x := by
    show (∑ y, if flat y = flat x then pos y else 0) = pos x
    rw [Finset.sum_eq_single x]
    · rw [if_pos rfl]
    · intro y _ hy
      rw [if_neg (fun h => hy (hinj h))]
    · intro h
      exact absurd (Finset.mem_univ x) h
  have hQx : Q (flat x) = neg x := by
    show (∑ y, if flat y = flat x then neg y else 0) = neg x
    rw [Finset.sum_eq_single x]
    · rw [if_pos rfl]
    · intro y _ hy
      rw [if_neg (fun h => hy (hinj h))]
    · intro h
      exact absurd (Finset.mem_univ x) h
  unfold ent
  rw [hdig (flat x) (hflat x), hPx, hQx]
  have hle : neg x ≤ 2 ^ (W - 1) + pos x := by
    have := hQP (flat x)
    rw [hPx, hQx] at this
    exact this
  push_cast [hle]
  ring

/-! ## Soundness of the scan -/

/-- The index type of the unit slots of a family of frame types. -/
abbrev Slot {T : ℕ} (m : Fin T → ℕ) := Σ t : Fin T, Fin (m t) × Fin (m t)

set_option maxHeartbeats 4000000 in
theorem scan_sound (W L : ℕ) (hW1 : 1 ≤ W) {T : ℕ} (m : Fin T → ℕ)
    (E : (t : Fin T) → List (Word × Fin (m t) × ℤ)) (off : Fin T → ℕ) (N : ℕ)
    (hN : ∀ t, absSum (E t) ≤ N) (hNW : N < 2 ^ W)
    (hbig : (∑ t, m t * m t) * (729 * (2 * (N * N))) < 2 ^ (W - 1))
    (hflat : ∀ t (i j : Fin (m t)), off t + i * m t + j < L)
    (hinj : ∀ t t' (i j : Fin (m t)) (i' j' : Fin (m t')),
      off t + i * m t + j = off t' + i' * m t' + j' → t = t' ∧ (i : ℕ) = i' ∧ (j : ℕ) = j')
    (α β : Fin 6 → Fin 6) (F : ℕ)
    (hcheck : finish (offset W (W - 1) L) F (scanM (lorAll (List.ofFn fun t => rmask (E t)))
      (List.ofFn fun t => mkTy W (off t) (E t))
      (3 ^ (α 0 : ℕ)) (3 ^ (α 1 : ℕ)) (3 ^ (α 2 : ℕ)) (3 ^ (α 3 : ℕ)) (3 ^ (α 4 : ℕ))
      (3 ^ (α 5 : ℕ)) (3 ^ (β 0 : ℕ)) (3 ^ (β 1 : ℕ)) (3 ^ (β 2 : ℕ)) (3 ^ (β 3 : ℕ))
      (3 ^ (β 4 : ℕ)) (3 ^ (β 5 : ℕ)) 729 (0, 0)) = true)
    (t : Fin T) (i j : Fin (m t)) :
    ent W (W - 1) F (off t + i * m t + j) =
      ∑ a ∈ Finset.range 729, certificateMatrixFromSparseEntries (E t) (fun k => wdec a (α k)) i *
        certificateMatrixFromSparseEntries (E t) (fun k => wdec a (β k)) j := by
  classical
  -- words of the scan
  set rA : ℕ → ℕ := fun a => sel6 a (3 ^ (α 0 : ℕ)) (3 ^ (α 1 : ℕ)) (3 ^ (α 2 : ℕ))
    (3 ^ (α 3 : ℕ)) (3 ^ (α 4 : ℕ)) (3 ^ (α 5 : ℕ)) with hrA
  set cA : ℕ → ℕ := fun a => sel6 a (3 ^ (β 0 : ℕ)) (3 ^ (β 1 : ℕ)) (3 ^ (β 2 : ℕ))
    (3 ^ (β 3 : ℕ)) (3 ^ (β 4 : ℕ)) (3 ^ (β 5 : ℕ)) with hcA
  have hrlt : ∀ a, rA a < 729 := fun a => sel6_lt a α
  have hclt : ∀ a, cA a < 729 := fun a => sel6_lt a β
  have hrw : ∀ a, wdec (rA a) = fun k => wdec a (α k) := fun a => wdec_sel6 a α
  have hcw : ∀ a, wdec (cA a) = fun k => wdec a (β k) := fun a => wdec_sel6 a β
  have hWt : ∀ t, absSum (E t) < 2 ^ W := fun t => lt_of_le_of_lt (hN t) hNW
  -- the list of types with their step values
  let LL : List (TyTab × (ℕ → ℕ → ℕ) × (ℕ → ℕ → ℕ)) :=
    List.ofFn fun t => (mkTy W (off t) (E t), posT W (off t) (E t), negT W (off t) (E t))
  have hLL1 : (List.ofFn fun t => mkTy W (off t) (E t)) = LL.map Prod.fst := by
    simp only [LL, List.map_ofFn]
    rfl
  have hLLpos : ∀ r c, (LL.map (fun p => p.2.1 r c)).sum = ∑ t, posT W (off t) (E t) r c := by
    intro r c
    simp only [LL, List.map_ofFn, List.sum_ofFn]
    rfl
  have hLLneg : ∀ r c, (LL.map (fun p => p.2.2 r c)).sum = ∑ t, negT W (off t) (E t) r c := by
    intro r c
    simp only [LL, List.map_ofFn, List.sum_ofFn]
    rfl
  set M := lorAll (List.ofFn fun t => rmask (E t)) with hM
  have hleaf : ∀ a x y, leaf M (List.ofFn fun t => mkTy W (off t) (E t)) (rA a) (cA a) (x, y) =
      (x + ∑ t, posT W (off t) (E t) (rA a) (cA a), y + ∑ t, negT W (off t) (E t) (rA a) (cA a)) := by
    intro a x y
    rw [hLL1, leaf_eq M LL (rA a) (cA a), hLLpos, hLLneg]
    · intro p hp x' y'
      obtain ⟨t', rfl⟩ := List.mem_ofFn.mp hp
      exact contribM_mkTy W (off t') (E t') (hWt t') (rA a) (cA a) x' y' (hrlt a) (hclt a)
    · intro hb p hp
      obtain ⟨t', rfl⟩ := List.mem_ofFn.mp hp
      apply posT_negT_zero W (off t') (E t') (rA a) (cA a) (hrlt a) (hclt a)
      have hmem : rmask (E t') ∈ List.ofFn fun t => rmask (E t) := List.mem_ofFn.mpr ⟨t', rfl⟩
      cases h1 : M.testBit (rA a)
      · exact Or.inl (lorAll_false _ (rA a) h1 _ hmem)
      · rw [h1, Bool.true_and] at hb
        exact Or.inr (lorAll_false _ (cA a) hb _ hmem)
  have hscan := scanM_eq M (List.ofFn fun t => mkTy W (off t) (E t)) α β
    (fun a => ∑ t, posT W (off t) (E t) (rA a) (cA a))
    (fun a => ∑ t, negT W (off t) (E t) (rA a) (cA a)) hleaf 729 0 0
  rw [hscan] at hcheck
  -- the comparison
  have hF : F = offset W (W - 1) L + (0 + ∑ a ∈ Finset.range 729, ∑ t, posT W (off t) (E t) (rA a) (cA a)) -
      (0 + ∑ a ∈ Finset.range 729, ∑ t, negT W (off t) (E t) (rA a) (cA a)) := by
    have h := Nat.eq_of_beq_eq_true hcheck
    exact h.symm
  -- slot values
  let Pc : Slot m → ℕ := fun x => ∑ a ∈ Finset.range 729,
    (cnt false (E x.1) (wdec (rA a)) x.2.1 * cnt false (E x.1) (wdec (cA a)) x.2.2 +
      cnt true (E x.1) (wdec (rA a)) x.2.1 * cnt true (E x.1) (wdec (cA a)) x.2.2)
  let Nc : Slot m → ℕ := fun x => ∑ a ∈ Finset.range 729,
    (cnt false (E x.1) (wdec (rA a)) x.2.1 * cnt true (E x.1) (wdec (cA a)) x.2.2 +
      cnt true (E x.1) (wdec (rA a)) x.2.1 * cnt false (E x.1) (wdec (cA a)) x.2.2)
  let fl : Slot m → ℕ := fun x => off x.1 + x.2.1 * m x.1 + x.2.2
  have hsumPos : ∑ a ∈ Finset.range 729, ∑ t, posT W (off t) (E t) (rA a) (cA a) =
      ∑ x : Slot m, Pc x * 2 ^ (W * fl x) := by
    simp only [posT_expand]
    rw [Finset.sum_comm]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro t' _
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i' _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j' _
    rw [Finset.sum_mul]
  have hsumNeg : ∑ a ∈ Finset.range 729, ∑ t, negT W (off t) (E t) (rA a) (cA a) =
      ∑ x : Slot m, Nc x * 2 ^ (W * fl x) := by
    simp only [negT_expand]
    rw [Finset.sum_comm]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro t' _
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i' _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j' _
    rw [Finset.sum_mul]
  rw [hsumPos, hsumNeg, Nat.zero_add, Nat.zero_add] at hF
  -- bounds
  have hcntN : ∀ t neg w (k : Fin (m t)), cnt neg (E t) w k ≤ N :=
    fun t neg w k => le_trans (cnt_le_absSum neg (E t) w k) (hN t)
  have hPc : ∀ x, Pc x ≤ 729 * (2 * (N * N)) := by
    intro x
    calc Pc x ≤ ∑ a ∈ Finset.range 729, 2 * (N * N) := by
          apply Finset.sum_le_sum
          intro a _
          have h1 := Nat.mul_le_mul (hcntN x.1 false (wdec (rA a)) x.2.1) (hcntN x.1 false (wdec (cA a)) x.2.2)
          have h2 := Nat.mul_le_mul (hcntN x.1 true (wdec (rA a)) x.2.1) (hcntN x.1 true (wdec (cA a)) x.2.2)
          omega
      _ = 729 * (2 * (N * N)) := by simp
  have hNc : ∀ x, Nc x ≤ 729 * (2 * (N * N)) := by
    intro x
    calc Nc x ≤ ∑ a ∈ Finset.range 729, 2 * (N * N) := by
          apply Finset.sum_le_sum
          intro a _
          have h1 := Nat.mul_le_mul (hcntN x.1 false (wdec (rA a)) x.2.1) (hcntN x.1 true (wdec (cA a)) x.2.2)
          have h2 := Nat.mul_le_mul (hcntN x.1 true (wdec (rA a)) x.2.1) (hcntN x.1 false (wdec (cA a)) x.2.2)
          omega
      _ = 729 * (2 * (N * N)) := by simp
  have hcard : ∑ _x : Slot m, 729 * (2 * (N * N)) = (∑ t, m t * m t) * (729 * (2 * (N * N))) := by
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_fin]
  have hbP : ∑ x, Pc x < 2 ^ (W - 1) :=
    lt_of_le_of_lt (le_trans (Finset.sum_le_sum (fun x _ => hPc x)) (le_of_eq hcard)) hbig
  have hbN : ∑ x, Nc x < 2 ^ (W - 1) :=
    lt_of_le_of_lt (le_trans (Finset.sum_le_sum (fun x _ => hNc x)) (le_of_eq hcard)) hbig
  have hflat' : ∀ x : Slot m, fl x < L := fun x => hflat x.1 x.2.1 x.2.2
  have hinj' : Function.Injective fl := by
    rintro ⟨t1, i1, j1⟩ ⟨t2, i2, j2⟩ h
    obtain ⟨rfl, hi, hj⟩ := hinj t1 t2 i1 j1 i2 j2 h
    have hi' : i1 = i2 := Fin.ext hi
    have hj' : j1 = j2 := Fin.ext hj
    rw [hi', hj']
  have hdig := digits_of_family W L hW1 Pc Nc fl hflat' hinj' hbP hbN F hF ⟨t, i, j⟩
  show ent W (W - 1) F (fl ⟨t, i, j⟩) = _
  rw [hdig]
  simp only [Pc, Nc]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [sparse_eq_cnt, sparse_eq_cnt, ← hrw a, ← hcw a]
  ring

/-- The compression of a local diagram on a sparse frame, from a passing scan. -/
theorem comp_sound (W L : ℕ) (hW1 : 1 ≤ W) {T : ℕ} (m : Fin T → ℕ)
    (E : (t : Fin T) → List (Word × Fin (m t) × ℤ)) (off : Fin T → ℕ) (N : ℕ)
    (hN : ∀ t, absSum (E t) ≤ N) (hNW : N < 2 ^ W)
    (hbig : (∑ t, m t * m t) * (729 * (2 * (N * N))) < 2 ^ (W - 1))
    (hflat : ∀ t (i j : Fin (m t)), off t + i * m t + j < L)
    (hinj : ∀ t t' (i j : Fin (m t)) (i' j' : Fin (m t')),
      off t + i * m t + j = off t' + i' * m t' + j' → t = t' ∧ (i : ℕ) = i' ∧ (j : ℕ) = j')
    (S : Finset (Fin 6)) (σ : Equiv.Perm (Fin 6)) (F : ℕ)
    (hcheck : finish (offset W (W - 1) L) F (scanM (lorAll (List.ofFn fun t => rmask (E t)))
      (List.ofFn fun t => mkTy W (off t) (E t))
      (3 ^ (rowPos S σ 0 : ℕ)) (3 ^ (rowPos S σ 1 : ℕ)) (3 ^ (rowPos S σ 2 : ℕ))
      (3 ^ (rowPos S σ 3 : ℕ)) (3 ^ (rowPos S σ 4 : ℕ)) (3 ^ (rowPos S σ 5 : ℕ))
      (3 ^ (colPos S σ 0 : ℕ)) (3 ^ (colPos S σ 1 : ℕ)) (3 ^ (colPos S σ 2 : ℕ))
      (3 ^ (colPos S σ 3 : ℕ)) (3 ^ (colPos S σ 4 : ℕ)) (3 ^ (colPos S σ 5 : ℕ)) 729 (0, 0)) = true)
    (t : Fin T) (i j : Fin (m t)) :
    ((certificateMatrixFromSparseEntries (E t))ᵀ * certificateLocalDiagram (n := Fin 3) (R := ℤ) S σ *
      certificateMatrixFromSparseEntries (E t)) i j = ent W (W - 1) F (off t + i * m t + j) := by
  rw [scan_sound W L hW1 m E off N hN hNW hbig hflat hinj (rowPos S σ) (colPos S σ) F hcheck t i j,
    certificateLocalDiagram_compression, sum_words]
  apply Finset.sum_congr rfl
  intro a _
  rw [wordSwap_row, wordSwap_col]

end X2Sites
end ThreeCopyQutritWerner
