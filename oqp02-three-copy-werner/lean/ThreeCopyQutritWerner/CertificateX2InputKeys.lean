module

public import ThreeCopyQutritWerner.CertificateX2InputGlueKey

@[expose] public section


/-!
# Input stage: key sums of type triples with several trial keys

`x2KeySum s N t` is the sum over the keys of the type triple `t`; given the list of those keys
(`x2KeySum_list`), and for each key the hypotheses of `x2Lookup_trial_ib` (bundled as `trialKeyOK`),
`3 den_c × x2KeySum` is the `ibIB` of the concatenated trial parts `(V_k, V_k, 3 ratio)`
(`x2KeySum_trial_ib`). This is the form `ibBatchOK_sound` consumes for the stored U-blocks of a type
triple (fibers of all its keys in one natural axpy per row).
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

theorem ibIB_append (W : ℕ) (fs1 fs2 : List (ℕ × ℕ × ℕ)) (x y : ℕ) :
    ibIB W (fs1 ++ fs2) x y = ibIB W fs1 x y + ibIB W fs2 x y := by
  unfold ibIB
  rw [List.map_append, List.sum_append]

theorem ibFS_cons (q : List ℕ × List ℕ × ℕ) (p : List (List ℕ × List ℕ × ℕ)) :
    ibFS (q :: p) = ibFS [q] ++ ibFS p := by
  simp [ibFS]

/-- The key sum of a type triple over an explicit list of its keys. -/
theorem x2KeySum_list (s : Fin 3) (N : X2Blocks s) (t : Fin 3 → Fin 8) (ks : List (x2Key s))
    (hks : ∀ k : x2Key s, x2KeyTypes s k = t ↔ k ∈ ks) (hnd : ks.Nodup) (a b : Fin 3 → ℕ) :
    x2KeySum s N t a b = (ks.map (fun k => x2Lookup (x2InputBlock x2DataConcrete s N k) a b)).sum := by
  unfold x2KeySum
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun k => x2KeyTypes s k = t) = ks.toFinset := by
    ext k
    simp [hks]
  rw [hf, List.sum_toFinset _ hnd]

/-- The hypotheses of `x2Lookup_trial_ib` for one key, except the coordinate ranges. -/
def trialKeyOK (W : ℕ) (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (n : ℕ) (GJcols Fcols Vcols : List ℕ) : Prop :=
  N k = ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ)) *
      ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ))ᵀ ∧
    x2KeyDegree s k ≠ 2 ∧
    1 ≤ x2KeyMult s k 0 ∧ 1 ≤ x2KeyMult s k 1 ∧ 1 ≤ x2KeyMult s k 2 ∧
    glRowOK s (x2KeyTypes s k 0) (x2KeyMult s k 0) 512 = true ∧
    glRowOK s (x2KeyTypes s k 1) (x2KeyMult s k 1) 512 = true ∧
    glRowOK s (x2KeyTypes s k 2) (x2KeyMult s k 2) 512 = true ∧
    GJcols.length = x2KeySize s k ∧ x2KeySize s k ≤ 512 ∧
    (∀ d < x2KeySize s k, gjCheck W s (x2KeyTypes s k 0) (x2KeyTypes s k 1) (x2KeyTypes s k 2)
      (x2KeyMult s k 0) (x2KeyMult s k 1) (x2KeyMult s k 2) (x2JCols (x2KeyGlobal s k) d) (GJcols.getD d 0) = true) ∧
    (∀ c < n, vCheck W (x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2) (x2KeySize s k) GJcols
      (Fcols.getD c 0) (Vcols.getD c 0) = true) ∧
    Vcols.length = n

theorem x2Lookup_trial_ib' (W : ℕ) (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (n : ℕ)
    (GJcols Fcols Vcols : List ℕ) (hW : 160 ≤ W) (h : trialKeyOK W s N k n GJcols Fcols Vcols) (a b : Fin 3 → ℕ)
    (ha0 : a 0 < x2KeyMult s k 0) (ha1 : a 1 < x2KeyMult s k 1) (ha2 : a 2 < x2KeyMult s k 2)
    (hb0 : b 0 < x2KeyMult s k 0) (hb1 : b 1 < x2KeyMult s k 1) (hb2 : b 2 < x2KeyMult s k 2) :
    (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) *
        x2Lookup (x2InputBlock x2DataConcrete s N k) a b =
      (ibIB W (ibFS [(Vcols, Vcols, 94810963968000)])
        (kflat (x2KeyMult s k 1) (x2KeyMult s k 2) (a 0) (a 1) (a 2))
        (kflat (x2KeyMult s k 1) (x2KeyMult s k 2) (b 0) (b 1) (b 2)) : ℚ) := by
  obtain ⟨hN, hdeg, h0, h1, h2, hr0, hr1, hr2, hlen, hsz, hchk, hv, hVlen⟩ := h
  exact x2Lookup_trial_ib W s N k n GJcols Fcols Vcols hW hN hdeg h0 h1 h2 hr0 hr1 hr2 hlen hsz hchk hv hVlen
    a b ha0 ha1 ha2 hb0 hb1 hb2

/-- A list of parts, each equal to `c ×` a term, sums to the `ibIB` of the concatenated parts. -/
theorem sum_trial_parts {α : Type*} (W x y : ℕ) (c : ℚ) (f : α → ℚ) (V : α → List ℕ) :
    ∀ L : List α, (∀ e ∈ L, c * f e = (ibIB W (ibFS [(V e, V e, 94810963968000)]) x y : ℚ)) →
      c * (L.map f).sum = (ibIB W (ibFS (L.map (fun e => (V e, V e, 94810963968000)))) x y : ℚ)
  | [], _ => by simp [ibFS, ibIB]
  | e :: L, h => by
    have ih := sum_trial_parts W x y c f V L (fun e' he' => h e' (by simp [he']))
    rw [List.map_cons, List.sum_cons, mul_add, h e (by simp), ih,
      List.map_cons,
      ibFS_cons (V e, V e, 94810963968000) (L.map (fun e => (V e, V e, 94810963968000))),
      ibIB_append W (ibFS [(V e, V e, 94810963968000)]) (ibFS (L.map (fun e => (V e, V e, 94810963968000)))) x y,
      Int.cast_add]

/-- `3 den_c ×` the key sum of a type triple whose keys are all trial keys with checked columns: the
`ibIB` of the concatenated trial parts. Keys as records `(k, n, GJcols, Fcols, Vcols)`. -/
theorem x2KeySum_trial_ib (W : ℕ) (s : Fin 3) (N : X2Blocks s) (t : Fin 3 → Fin 8)
    (ks : List (x2Key s × ℕ × List ℕ × List ℕ × List ℕ))
    (hks : ∀ k : x2Key s, x2KeyTypes s k = t ↔ k ∈ ks.map Prod.fst) (hnd : (ks.map Prod.fst).Nodup)
    (hW : 160 ≤ W) (hok : ∀ e ∈ ks, trialKeyOK W s N e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2)
    (a b : Fin 3 → ℕ)
    (ha0 : a 0 < x2Mult s (t 0)) (ha1 : a 1 < x2Mult s (t 1)) (ha2 : a 2 < x2Mult s (t 2))
    (hb0 : b 0 < x2Mult s (t 0)) (hb1 : b 1 < x2Mult s (t 1)) (hb2 : b 2 < x2Mult s (t 2)) :
    (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) * x2KeySum s N t a b =
      (ibIB W (ibFS (ks.map (fun e => (e.2.2.2.2, e.2.2.2.2, 94810963968000))))
        (kflat (x2Mult s (t 1)) (x2Mult s (t 2)) (a 0) (a 1) (a 2))
        (kflat (x2Mult s (t 1)) (x2Mult s (t 2)) (b 0) (b 1) (b 2)) : ℚ) := by
  rw [x2KeySum_list s N t (ks.map Prod.fst) hks hnd a b, List.map_map]
  refine sum_trial_parts W _ _ _ _ (fun e => e.2.2.2.2) ks (fun e he => ?_)
  have ht : x2KeyTypes s e.1 = t := (hks e.1).mpr (List.mem_map.mpr ⟨e, he, rfl⟩)
  have hm : ∀ i, x2KeyMult s e.1 i = x2Mult s (t i) := fun i => by
    rw [show x2KeyMult s e.1 i = x2Mult s (x2KeyTypes s e.1 i) from rfl, ht]
  have he' := x2Lookup_trial_ib' W s N e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 hW (hok e he) a b
    (by rw [hm]; exact ha0) (by rw [hm]; exact ha1) (by rw [hm]; exact ha2)
    (by rw [hm]; exact hb0) (by rw [hm]; exact hb1) (by rw [hm]; exact hb2)
  rw [← hm 1, ← hm 2]
  exact he'

end X2
end ThreeCopyQutritWerner
