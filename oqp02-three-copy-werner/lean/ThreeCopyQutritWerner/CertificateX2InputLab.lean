module

public import ThreeCopyQutritWerner.CertificateX2InputSeg

@[expose] public section


/-!
# Input stage: label facts of the source sectors

Kernel checks of the S-label tables of sectors 1 and 2 in the forms the triple theory uses: labels type by type
in `pairsU` order (`labelsOK`), the decomposition of every label (`labelDecompS`), the type by comparison
(`typeOKS`), and the pair lists of every multiplicity that occurs (`pairsOK`).
-/

set_option maxRecDepth 100000
set_option exponentiation.threshold 1000000
set_option maxHeartbeats 0

open scoped Matrix

namespace ThreeCopyQutritWerner
namespace X2

theorem labelsOK_1 : labelsOK 1 := by unfold labelsOK; decide +kernel
theorem labelsOK_2 : labelsOK 2 := by unfold labelsOK; decide +kernel
theorem labelDecompS_1 : labelDecompS 1 := by unfold labelDecompS; decide +kernel
theorem labelDecompS_2 : labelDecompS 2 := by unfold labelDecompS; decide +kernel
theorem typeOKS_1 : typeOKS 1 := by unfold typeOKS; decide +kernel
theorem typeOKS_2 : typeOKS 2 := by unfold typeOKS; decide +kernel

theorem pairsOK_0 : pairsOK 0 := by unfold pairsOK; decide +kernel
theorem pairsOK_1 : pairsOK 1 := by unfold pairsOK; decide +kernel
theorem pairsOK_2 : pairsOK 2 := by unfold pairsOK; decide +kernel
theorem pairsOK_4 : pairsOK 4 := by unfold pairsOK; decide +kernel
theorem pairsOK_5 : pairsOK 5 := by unfold pairsOK; decide +kernel
theorem pairsOK_6 : pairsOK 6 := by unfold pairsOK; decide +kernel
theorem pairsOK_7 : pairsOK 7 := by unfold pairsOK; decide +kernel
theorem pairsOK_9 : pairsOK 9 := by unfold pairsOK; decide +kernel
theorem pairsOK_10 : pairsOK 10 := by unfold pairsOK; decide +kernel
theorem pairsOK_11 : pairsOK 11 := by unfold pairsOK; decide +kernel
theorem pairsOK_15 : pairsOK 15 := by unfold pairsOK; decide +kernel
theorem pairsOK_17 : pairsOK 17 := by unfold pairsOK; decide +kernel

/-- `pairsOK` for every multiplicity of the source sectors. -/
theorem pairsOK_mult (s : Fin 3) (hs : s = 1 ∨ s = 2) (u : Fin 8) : pairsOK (x2Mult s u) := by
  rcases hs with rfl | rfl <;> fin_cases u <;>
    first
    | exact pairsOK_0 | exact pairsOK_1 | exact pairsOK_2 | exact pairsOK_4 | exact pairsOK_5 | exact pairsOK_6
    | exact pairsOK_7 | exact pairsOK_9 | exact pairsOK_10 | exact pairsOK_11 | exact pairsOK_15 | exact pairsOK_17

theorem labelsOK_of (s : Fin 3) (hs : s = 1 ∨ s = 2) : labelsOK s := by
  rcases hs with rfl | rfl
  · exact labelsOK_1
  · exact labelsOK_2

/-- Key facts of a list of keys give the key glue and the part bounds of the concatenated parts. -/
theorem parts_of_keys (L : ℕ) (s : Fin 3) (N : X2Blocks s) (ks : List (x2Key s × List (ℕ × ℕ × ℕ)))
    (h : ∀ e ∈ ks, keyOK L s N e.1 e.2) :
    (∀ e ∈ ks, keyIB s N e.1 e.2) ∧ ∀ p ∈ ks.flatMap Prod.snd, partBound L p := by
  refine ⟨fun e he => (h e he).1, fun p hp => ?_⟩
  obtain ⟨e, he, hpe⟩ := List.mem_flatMap.mp hp
  exact (h e he).2 p hpe

/-- THE TRIPLE THEOREM: from key facts, checked stored blocks and checked T-blocks (any accessor), `σ · x2EmbedS`
at every label triple of a sorted type triple. -/
theorem tripleSpecS (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
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
    (Tget : ℕ → ℕ → ℕ)
    (hT : ∀ i0 < nS s t0, ∀ i1 < nS s t1, tCell UBT (nS s t2) ((pairsU (x2Mult s t0)).getD i0 (0, 0))
      ((pairsU (x2Mult s t1)).getD i1 (0, 0)) (Tget i0 i1) = true) :
    ∀ i0 < nS s t0, ∀ i1 < nS s t1, ∀ i2 < nS s t2,
      (ent 256 (256 - 1) (Tget i0 i1) i2 : ℚ) =
        1108531032609225922165724911675932935547910848716289179910144000 *
          x2EmbedS x2DataConcrete s N (slab s t0 i0) (slab s t1 i1) (slab s t2 i2) := by
  intro i0 hi0 i1 hi1 i2 hi2
  have hm2 : 1 ≤ x2Mult s t2 := by
    rcases Nat.eq_zero_or_pos (x2Mult s t2) with h | h
    · unfold nS at hi2
      rw [h] at hi2
      simp at hi2
    · exact h
  obtain ⟨hok, hparts⟩ := parts_of_keys _ s N ks hkeys
  have hU := ubSpec (x2Mult s t0 * x2Mult s t1 * x2Mult s t2) (x2Mult s t0) (x2Mult s t1) (x2Mult s t2)
    (ks.flatMap Prod.snd) UBT hm2 rfl hparts hlen hshape hchk
  have hKS : ∀ x0 x1 x2 y0 y1 y2 : ℕ, x0 < x2Mult s t0 → x1 < x2Mult s t1 → x2 < x2Mult s t2 →
      y0 < x2Mult s t0 → y1 < x2Mult s t1 → y2 < x2Mult s t2 →
      (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) *
          x2KeySum s N ![t0, t1, t2] ![x0, x1, x2] ![y0, y1, y2] =
        (ibIB 256 (ks.flatMap Prod.snd) (kflat (x2Mult s t1) (x2Mult s t2) x0 x1 x2)
          (kflat (x2Mult s t1) (x2Mult s t2) y0 y1 y2) : ℚ) :=
    fun x0 x1 x2 y0 y1 y2 h0 h1 h2 h3 h4 h5 =>
      x2KeySum_ib s N ![t0, t1, t2] ks hks hnd hok ![x0, x1, x2] ![y0, y1, y2] h0 h1 h2 h3 h4 h5
  exact ttSpecGen s hs N hN t0 t1 t2 h01 h12 (ks.flatMap Prod.snd) UBT Tget (labelsOK_of s hs)
    (pairsOK_mult s hs t0) (pairsOK_mult s hs t1) (pairsOK_mult s hs t2) hKS hU hT i0 hi0 i1 hi1 i2 hi2

/-- A sorted triple whose keys contribute no part (or that has no key): `x2EmbedS` vanishes on its labels. -/
theorem zeroTripleS (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (t0 t1 t2 : Fin 8) (h01 : t0 ≤ t1) (h12 : t1 ≤ t2) (ks : List (x2Key s × List (ℕ × ℕ × ℕ)))
    (hks : ∀ k : x2Key s, x2KeyTypes s k = ![t0, t1, t2] ↔ k ∈ ks.map Prod.fst) (hnd : (ks.map Prod.fst).Nodup)
    (hkeys : ∀ e ∈ ks, keyIB s N e.1 e.2) (hempty : ks.flatMap Prod.snd = []) : ZspecS s N t0 t1 t2 :=
  zspecS_of_empty s hs N hN t0 t1 t2 h01 h12 (labelsOK_of s hs) (pairsOK_mult s hs t0) (pairsOK_mult s hs t1)
    (pairsOK_mult s hs t2) (fun x0 x1 x2 y0 y1 y2 h0 h1 h2 h3 h4 h5 =>
      keySum_zero_of_empty s N ![t0, t1, t2] ks hks hnd hkeys hempty ![x0, x1, x2] ![y0, y1, y2] h0 h1 h2 h3 h4 h5)

/-- The decidable part of `trialKeyOK` (everything but the block form). -/
def trialKeyChk (s : Fin 3) (k : x2Key s) (n : ℕ) (GJcols Fcols Vcols : List ℕ) : Prop :=
  x2KeyDegree s k ≠ 2 ∧
    1 ≤ x2KeyMult s k 0 ∧ 1 ≤ x2KeyMult s k 1 ∧ 1 ≤ x2KeyMult s k 2 ∧
    glRowOK s (x2KeyTypes s k 0) (x2KeyMult s k 0) 512 = true ∧
    glRowOK s (x2KeyTypes s k 1) (x2KeyMult s k 1) 512 = true ∧
    glRowOK s (x2KeyTypes s k 2) (x2KeyMult s k 2) 512 = true ∧
    GJcols.length = x2KeySize s k ∧ x2KeySize s k ≤ 512 ∧
    (∀ d < x2KeySize s k, gjCheck 256 s (x2KeyTypes s k 0) (x2KeyTypes s k 1) (x2KeyTypes s k 2)
      (x2KeyMult s k 0) (x2KeyMult s k 1) (x2KeyMult s k 2) (x2JCols (x2KeyGlobal s k) d) (GJcols.getD d 0) = true) ∧
    (∀ c < n, vCheck 256 (x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2) (x2KeySize s k) GJcols
      (Fcols.getD c 0) (Vcols.getD c 0) = true) ∧
    Vcols.length = n

theorem keyOK_of_trialChk (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (n L : ℕ) (GJcols Fcols Vcols : List ℕ)
    (hL : x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2 = L)
    (hN : N k = ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ)) *
      ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ))ᵀ)
    (h : trialKeyChk s k n GJcols Fcols Vcols) : keyOK L s N k (ibFS [(Vcols, Vcols, 94810963968000)]) :=
  keyOK_of_trial s N k n L GJcols Fcols Vcols hL ⟨hN, h⟩

/-- The decidable part of `trial2KeyOK`. -/
def trial2KeyChk (s : Fin 3) (k : x2Key s) (n : ℕ) (GJcols Fcols Vcols Pcols : List ℕ) : Prop :=
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

theorem keyOK_of_trial2Chk (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (n L : ℕ) (GJcols Fcols Vcols Pcols : List ℕ)
    (hL : x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2 = L)
    (hN : N k = ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ)) *
      ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ))ᵀ)
    (h : trial2KeyChk s k n GJcols Fcols Vcols Pcols) :
    keyOK L s N k (ibFS [(Vcols, Vcols, 94810963968000), (Pcols, Pcols, 31603654656000)]) :=
  keyOK_of_trial2 s N k n L GJcols Fcols Vcols Pcols hL ⟨hN, h⟩

/-- The decidable part of `corrKeyOK`. -/
def corrKeyChk (s : Fin 3) (k : x2Key s) (kd : ℕ) (GJcols Kcols Ucols Acols UAcols : List ℕ) : Prop :=
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

theorem keyOK_of_corrChk (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (kd L : ℕ) (GJcols Kcols Ucols Acols UAcols : List ℕ)
    (hL : x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2 = L)
    (hN : N k = (x2FactorOf (x2KeySize s k) kd Kcols).map (Int.cast : ℤ → ℚ) *
      ((1 / (46188793025384413423571871319830538981162952029845382496256000 : ℚ)) •
        (x2AMatOf kd Acols).map (Int.cast : ℤ → ℚ)) *
      ((x2FactorOf (x2KeySize s k) kd Kcols).map (Int.cast : ℤ → ℚ))ᵀ)
    (h : corrKeyChk s k kd GJcols Kcols Ucols Acols UAcols) : keyOK L s N k (ibFS [(UAcols, Ucols, 3)]) :=
  keyOK_of_corr s N k kd L GJcols Kcols Ucols Acols UAcols hL ⟨hN, h⟩

/-! ### Uniform source forms and helpers for generated modules -/

/-- The trial block of a key in the packed form: `(2^-80 F)(2^-80 F)ᵀ`, `F` with the packed columns
`x2TrialAll[g]` and `x2TrialDim[g]` columns (`g` the global block). -/
noncomputable def x2TrialForm (s : Fin 3) (k : x2Key s) : Matrix (x2Col s k) (x2Col s k) ℚ :=
  ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) (x2TrialDim.getD (x2KeyGlobal s k) 0)
      (x2TrialAll.getD (x2KeyGlobal s k) [])).map (Int.cast : ℤ → ℚ)) *
    ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) (x2TrialDim.getD (x2KeyGlobal s k) 0)
      (x2TrialAll.getD (x2KeyGlobal s k) [])).map (Int.cast : ℤ → ℚ))ᵀ

/-- The corrected block of a key in the light form `K (A / den_c) Kᵀ` from packed columns. -/
noncomputable def x2CorrForm (s : Fin 3) (k : x2Key s) (kd : ℕ) (Kcols Acols : List ℕ) :
    Matrix (x2Col s k) (x2Col s k) ℚ :=
  (x2FactorOf (x2KeySize s k) kd Kcols).map (Int.cast : ℤ → ℚ) *
    ((1 / (46188793025384413423571871319830538981162952029845382496256000 : ℚ)) •
      (x2AMatOf kd Acols).map (Int.cast : ℤ → ℚ)) *
    ((x2FactorOf (x2KeySize s k) kd Kcols).map (Int.cast : ℤ → ℚ))ᵀ

theorem trialForm_eq (s : Fin 3) (k : x2Key s) (n : ℕ) (Fcols : List ℕ)
    (hn : x2TrialDim.getD (x2KeyGlobal s k) 0 = n) (hF : x2TrialAll.getD (x2KeyGlobal s k) [] = Fcols) :
    x2TrialForm s k = ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ)) *
      ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ))ᵀ := by
  unfold x2TrialForm
  rw [hn, hF]

/-- A key whose block vanishes contributes no part. -/
theorem keyOK_of_zeroBlock (L : ℕ) (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (hN : N k = 0) : keyOK L s N k [] := by
  refine ⟨fun a b _ _ _ _ _ _ => ?_, fun p hp => by simp at hp⟩
  have h0 : x2InputBlock x2DataConcrete s N k = 0 := by
    unfold x2InputBlock
    rw [hN]
    simp
  rw [h0, x2Lookup_zero]
  simp [ibIB]

/-- The trial form of a key without factor columns vanishes. -/
theorem trialForm_zero (s : Fin 3) (k : x2Key s) (hn : x2TrialDim.getD (x2KeyGlobal s k) 0 = 0) :
    x2TrialForm s k = 0 := by
  rw [trialForm_eq s k 0 _ hn rfl]
  ext i j
  simp [Matrix.mul_apply]

/-- A type of multiplicity zero: no labels, so every statement over its labels holds. -/
theorem zspecS_of_nS (s : Fin 3) (N : X2Blocks s) (t0 t1 t2 : Fin 8) (h : nS s t0 = 0 ∨ nS s t1 = 0 ∨ nS s t2 = 0) :
    ZspecS s N t0 t1 t2 := by
  intro i0 hi0 i1 hi1 i2 hi2
  rcases h with h | h | h <;> omega

/-- A Boolean check over a range of indices, read back index by index. -/
theorem rangeAll_sound (f : ℕ → Bool) (lo cnt : ℕ) (h : (List.range cnt).all (fun k => f (lo + k)) = true) :
    ∀ i, lo ≤ i → i < lo + cnt → f i = true := by
  intro i h1 h2
  have := List.all_eq_true.mp h (i - lo) (List.mem_range.mpr (by omega))
  rwa [show lo + (i - lo) = i by omega] at this

/-- One row of a T-table with rows by the second label (entries over the pairs `P₀` of the first label). -/
noncomputable def tRowOK (UBT : List (List (List (List ℕ)))) (L2 : ℕ) (P0 : List (ℕ × ℕ)) (p1 : ℕ × ℕ)
    (row : List ℕ) : Bool :=
  Nat.beq row.length P0.length && (List.zip row P0).all (fun q => tCell UBT L2 q.2 p1 q.1)

/-- One row of a T-table with rows by the first label (entries over the pairs `P₁` of the second label). -/
noncomputable def tRowOK' (UBT : List (List (List (List ℕ)))) (L2 : ℕ) (P1 : List (ℕ × ℕ)) (p0 : ℕ × ℕ)
    (row : List ℕ) : Bool :=
  Nat.beq row.length P1.length && (List.zip row P1).all (fun q => tCell UBT L2 p0 q.2 q.1)

theorem tRowOK_cell (UBT : List (List (List (List ℕ)))) (L2 : ℕ) (P0 : List (ℕ × ℕ)) (p1 : ℕ × ℕ) (row : List ℕ)
    (h : tRowOK UBT L2 P0 p1 row = true) (i0 : ℕ) (hi : i0 < P0.length) :
    tCell UBT L2 (P0.getD i0 (0, 0)) p1 (row.getD i0 0) = true := by
  unfold tRowOK at h
  rw [Bool.and_eq_true] at h
  have hl := Nat.eq_of_beq_eq_true h.1
  have hz : i0 < (List.zip row P0).length := by simp [hl, hi]
  have hm := List.getElem_mem hz
  rw [List.getElem_zip] at hm
  have hc := List.all_eq_true.mp h.2 _ hm
  dsimp only at hc
  rwa [List.getD_eq_getElem row 0 (by omega), List.getD_eq_getElem P0 (0, 0) hi]

theorem tRowOK'_cell (UBT : List (List (List (List ℕ)))) (L2 : ℕ) (P1 : List (ℕ × ℕ)) (p0 : ℕ × ℕ) (row : List ℕ)
    (h : tRowOK' UBT L2 P1 p0 row = true) (i1 : ℕ) (hi : i1 < P1.length) :
    tCell UBT L2 p0 (P1.getD i1 (0, 0)) (row.getD i1 0) = true := by
  unfold tRowOK' at h
  rw [Bool.and_eq_true] at h
  have hl := Nat.eq_of_beq_eq_true h.1
  have hz : i1 < (List.zip row P1).length := by simp [hl, hi]
  have hm := List.getElem_mem hz
  rw [List.getElem_zip] at hm
  have hc := List.all_eq_true.mp h.2 _ hm
  dsimp only at hc
  rwa [List.getD_eq_getElem row 0 (by omega), List.getD_eq_getElem P1 (0, 0) hi]

/-- The T-check of a whole table (rows by the second label) from row checks. -/
theorem tTT_of_rows (s : Fin 3) (hs : s = 1 ∨ s = 2) (UBT : List (List (List (List ℕ)))) (t0 t1 t2 : Fin 8)
    (TT : List (List ℕ))
    (h : ∀ i1 < nS s t1, tRowOK UBT (nS s t2) (pairsU (x2Mult s t0)) ((pairsU (x2Mult s t1)).getD i1 (0, 0))
      (TT.getD i1 []) = true) :
    ∀ i0 < nS s t0, ∀ i1 < nS s t1, tCell UBT (nS s t2) ((pairsU (x2Mult s t0)).getD i0 (0, 0))
      ((pairsU (x2Mult s t1)).getD i1 (0, 0)) ((TT.getD i1 []).getD i0 0) = true := by
  intro i0 hi0 i1 hi1
  have hl := (pairsOK_mult s hs t0).1
  exact tRowOK_cell UBT _ _ _ _ (h i1 hi1) i0 (by rw [hl]; exact hi0)

/-- The T-check of a whole table (rows by the first label) from row checks. -/
theorem tTC_of_rows (s : Fin 3) (hs : s = 1 ∨ s = 2) (UBT : List (List (List (List ℕ)))) (t0 t1 t2 : Fin 8)
    (TC : List (List ℕ))
    (h : ∀ i0 < nS s t0, tRowOK' UBT (nS s t2) (pairsU (x2Mult s t1)) ((pairsU (x2Mult s t0)).getD i0 (0, 0))
      (TC.getD i0 []) = true) :
    ∀ i0 < nS s t0, ∀ i1 < nS s t1, tCell UBT (nS s t2) ((pairsU (x2Mult s t0)).getD i0 (0, 0))
      ((pairsU (x2Mult s t1)).getD i1 (0, 0)) ((TC.getD i0 []).getD i1 0) = true := by
  intro i0 hi0 i1 hi1
  have hl := (pairsOK_mult s hs t1).1
  exact tRowOK'_cell UBT _ _ _ _ (h i0 hi0) i1 (by rw [hl]; exact hi1)

theorem trialKeyChk_intro (s : Fin 3) (k : x2Key s) (n : ℕ) (GJcols Fcols Vcols : List ℕ)
    (h1 : x2KeyDegree s k ≠ 2 ∧ 1 ≤ x2KeyMult s k 0 ∧ 1 ≤ x2KeyMult s k 1 ∧ 1 ≤ x2KeyMult s k 2 ∧
      glRowOK s (x2KeyTypes s k 0) (x2KeyMult s k 0) 512 = true ∧
      glRowOK s (x2KeyTypes s k 1) (x2KeyMult s k 1) 512 = true ∧
      glRowOK s (x2KeyTypes s k 2) (x2KeyMult s k 2) 512 = true ∧
      GJcols.length = x2KeySize s k ∧ x2KeySize s k ≤ 512 ∧ Vcols.length = n)
    (h2 : ∀ d < x2KeySize s k, gjCheck 256 s (x2KeyTypes s k 0) (x2KeyTypes s k 1) (x2KeyTypes s k 2)
      (x2KeyMult s k 0) (x2KeyMult s k 1) (x2KeyMult s k 2) (x2JCols (x2KeyGlobal s k) d) (GJcols.getD d 0) = true)
    (h3 : ∀ c < n, vCheck 256 (x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2) (x2KeySize s k) GJcols
      (Fcols.getD c 0) (Vcols.getD c 0) = true) : trialKeyChk s k n GJcols Fcols Vcols := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h1
  exact ⟨a, b, c, d, e, f, g, h, i, h2, h3, j⟩

theorem trial2KeyChk_intro (s : Fin 3) (k : x2Key s) (n : ℕ) (GJcols Fcols Vcols Pcols : List ℕ)
    (h1 : x2KeyDegree s k = 2 ∧ x2KeyMult s k 0 = x2KeyMult s k 1 ∧ x2KeyMult s k 1 = x2KeyMult s k 2 ∧
      1 ≤ x2KeyMult s k 0 ∧
      glRowOK s (x2KeyTypes s k 0) (x2KeyMult s k 0) 512 = true ∧
      glRowOK s (x2KeyTypes s k 1) (x2KeyMult s k 1) 512 = true ∧
      glRowOK s (x2KeyTypes s k 2) (x2KeyMult s k 2) 512 = true ∧
      GJcols.length = x2KeySize s k ∧ x2KeySize s k ≤ 512 ∧ Vcols.length = n ∧ Pcols.length = n)
    (h2 : ∀ d < x2KeySize s k, gjCheck 256 s (x2KeyTypes s k 0) (x2KeyTypes s k 1) (x2KeyTypes s k 2)
      (x2KeyMult s k 0) (x2KeyMult s k 1) (x2KeyMult s k 2) (x2JCols (x2KeyGlobal s k) d) (GJcols.getD d 0) = true)
    (h3 : ∀ c < n, vCheck 256 (x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2) (x2KeySize s k) GJcols
      (Fcols.getD c 0) (Vcols.getD c 0) = true)
    (h4 : ∀ c < n, partnerCheck (x2KeyMult s k 0) (Vcols.getD c 0) (Pcols.getD c 0) = true) :
    trial2KeyChk s k n GJcols Fcols Vcols Pcols := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, l⟩ := h1
  exact ⟨a, b, c, d, e, f, g, h, i, h2, h3, j, l, h4⟩

/-! ### Stored blocks checked by row ranges (for row-batches too large for one declaration) -/

/-- The row-range form of the stored-block checks: every row `a₂` of every row-batch lies in a checked range. -/
def ubRowsOK (L m0 m1 m2 : ℕ) (fs : List (ℕ × ℕ × ℕ)) (UBT : List (List (List (List ℕ)))) : Prop :=
  ∀ a0 < m0, ∀ a1 < m1, ∀ a2 < m2, ∃ lo R : ℕ, lo ≤ a2 ∧ a2 < lo + R ∧ lo + R ≤ m2 ∧
    ibBatchOK 256 L 302 m2 (m0 * m1) lo R ((a0 * m1 + a1) * m2 + lo) fs ((UBT.getD a0 []).getD a1 []).flatten = true

theorem ubSpec' (L m0 m1 m2 : ℕ) (fs : List (ℕ × ℕ × ℕ)) (UBT : List (List (List (List ℕ))))
    (hm2 : 1 ≤ m2) (hL : L = m0 * m1 * m2)
    (hparts : ∀ p ∈ fs, partBound L p) (hlen : fs.length < 2 ^ 27)
    (hshape : ∀ a0 < m0, ∀ a1 < m1, ((UBT.getD a0 []).getD a1 []).length = m0 ∧
      ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = m1)
    (hchk : ubRowsOK L m0 m1 m2 fs UBT) :
    ∀ a0 < m0, ∀ a1 < m1, ∀ b0 < m0, ∀ b1 < m1, ∀ a2 b2 : ℕ, a2 ≤ b2 → b2 < m2 →
      ent 256 (256 - 1) (UBget UBT a0 a1 b0 b1) (upos m2 a2 b2) =
        ibIB 256 fs (kflat m1 m2 a0 a1 a2) (kflat m1 m2 b0 b1 b2) := by
  intro a0 ha0 a1 ha1 b0 hb0 b1 hb1 a2 b2 hab hb2
  obtain ⟨hl0, hl1⟩ := hshape a0 ha0 a1 ha1
  obtain ⟨lo, R, hlo, hR, hlR, hc⟩ := hchk a0 ha0 a1 ha1 a2 (by omega)
  have hfs : ∀ p ∈ fs, p.2.1 < 2 ^ (256 * L) ∧ p.2.2 * 2 ^ (256 - 1) ≤ 2 ^ 302 :=
    fun p hp => ⟨(hparts p hp).2.1, (hparts p hp).2.2.1⟩
  have hlin : ∀ i < R, ∀ k < L, |ibIB 256 fs ((a0 * m1 + a1) * m2 + lo + i) k| < 2 ^ (256 - 1) := by
    intro i hi k hk
    have hx : (a0 * m1 + a1) * m2 + lo + i < L := by
      rw [hL]
      have := site_idx_lt m0 m1 m2 a0 a1 (lo + i) ha0 ha1 (by omega)
      calc (a0 * m1 + a1) * m2 + lo + i = (a0 * m1 + a1) * m2 + (lo + i) := by ring
        _ < m0 * (m1 * m2) := this
        _ = m0 * m1 * m2 := by ring
    have hb := ibIB_abs_le_parts L fs hparts _ hx k hk
    calc |ibIB 256 fs ((a0 * m1 + a1) * m2 + lo + i) k| ≤ fs.length * 2 ^ 227 := hb
      _ < 2 ^ 27 * 2 ^ 227 := by
          have h27 : (fs.length : ℤ) < 2 ^ 27 := by exact_mod_cast hlen
          exact mul_lt_mul_of_pos_right h27 (by positivity)
      _ ≤ 2 ^ (256 - 1) := by norm_num
  have hflat : ((UBT.getD a0 []).getD a1 []).flatten.length = m0 * m1 := by
    rw [flatten_length_of m1 _ hl1, hl0]
  have hblk : b0 * m1 + b1 < m0 * m1 := by
    calc b0 * m1 + b1 < (b0 + 1) * m1 := by nlinarith
      _ ≤ m0 * m1 := Nat.mul_le_mul_right _ hb0
  have h := ibBatchOK_sound 256 L 302 m2 (m0 * m1) lo R ((a0 * m1 + a1) * m2 + lo) fs _ (by norm_num) hm2 hlR
    (by rw [hL]) hflat hfs hlin hc (a2 - lo) (by omega) (b0 * m1 + b1) hblk b2 (by omega) hb2
  rw [show lo + (a2 - lo) = a2 by omega, show (a0 * m1 + a1) * m2 + lo + (a2 - lo) = (a0 * m1 + a1) * m2 + a2 by omega,
    flatten_getD_of m1 _ hl1 b0 b1 (by rw [hl0]; exact hb0) hb1] at h
  unfold UBget kflat
  rw [h]

/-- The triple theorem with stored blocks checked by row ranges. -/
theorem tripleSpecS' (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (t0 t1 t2 : Fin 8) (h01 : t0 ≤ t1) (h12 : t1 ≤ t2) (ks : List (x2Key s × List (ℕ × ℕ × ℕ)))
    (hks : ∀ k : x2Key s, x2KeyTypes s k = ![t0, t1, t2] ↔ k ∈ ks.map Prod.fst) (hnd : (ks.map Prod.fst).Nodup)
    (hkeys : ∀ e ∈ ks, keyOK (x2Mult s t0 * x2Mult s t1 * x2Mult s t2) s N e.1 e.2)
    (hlen : (ks.flatMap Prod.snd).length < 2 ^ 27) (UBT : List (List (List (List ℕ))))
    (hshape : ∀ a0 < x2Mult s t0, ∀ a1 < x2Mult s t1, ((UBT.getD a0 []).getD a1 []).length = x2Mult s t0 ∧
      ∀ l ∈ (UBT.getD a0 []).getD a1 [], l.length = x2Mult s t1)
    (hchk : ubRowsOK (x2Mult s t0 * x2Mult s t1 * x2Mult s t2) (x2Mult s t0) (x2Mult s t1) (x2Mult s t2)
      (ks.flatMap Prod.snd) UBT)
    (Tget : ℕ → ℕ → ℕ)
    (hT : ∀ i0 < nS s t0, ∀ i1 < nS s t1, tCell UBT (nS s t2) ((pairsU (x2Mult s t0)).getD i0 (0, 0))
      ((pairsU (x2Mult s t1)).getD i1 (0, 0)) (Tget i0 i1) = true) :
    ∀ i0 < nS s t0, ∀ i1 < nS s t1, ∀ i2 < nS s t2,
      (ent 256 (256 - 1) (Tget i0 i1) i2 : ℚ) =
        1108531032609225922165724911675932935547910848716289179910144000 *
          x2EmbedS x2DataConcrete s N (slab s t0 i0) (slab s t1 i1) (slab s t2 i2) := by
  intro i0 hi0 i1 hi1 i2 hi2
  have hm2 : 1 ≤ x2Mult s t2 := by
    rcases Nat.eq_zero_or_pos (x2Mult s t2) with h | h
    · unfold nS at hi2
      rw [h] at hi2
      simp at hi2
    · exact h
  obtain ⟨hok, hparts⟩ := parts_of_keys _ s N ks hkeys
  have hU := ubSpec' (x2Mult s t0 * x2Mult s t1 * x2Mult s t2) (x2Mult s t0) (x2Mult s t1) (x2Mult s t2)
    (ks.flatMap Prod.snd) UBT hm2 rfl hparts hlen hshape hchk
  have hKS : ∀ x0 x1 x2 y0 y1 y2 : ℕ, x0 < x2Mult s t0 → x1 < x2Mult s t1 → x2 < x2Mult s t2 →
      y0 < x2Mult s t0 → y1 < x2Mult s t1 → y2 < x2Mult s t2 →
      (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) *
          x2KeySum s N ![t0, t1, t2] ![x0, x1, x2] ![y0, y1, y2] =
        (ibIB 256 (ks.flatMap Prod.snd) (kflat (x2Mult s t1) (x2Mult s t2) x0 x1 x2)
          (kflat (x2Mult s t1) (x2Mult s t2) y0 y1 y2) : ℚ) :=
    fun x0 x1 x2 y0 y1 y2 h0 h1 h2 h3 h4 h5 =>
      x2KeySum_ib s N ![t0, t1, t2] ks hks hnd hok ![x0, x1, x2] ![y0, y1, y2] h0 h1 h2 h3 h4 h5
  exact ttSpecGen s hs N hN t0 t1 t2 h01 h12 (ks.flatMap Prod.snd) UBT Tget (labelsOK_of s hs)
    (pairsOK_mult s hs t0) (pairsOK_mult s hs t1) (pairsOK_mult s hs t2) hKS hU hT i0 hi0 i1 hi1 i2 hi2

end X2
end ThreeCopyQutritWerner
