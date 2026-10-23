module

public import ThreeCopyQutritWerner.CertificateX2InputGlueV
public import ThreeCopyQutritWerner.CertificateX2InputIB
public import ThreeCopyQutritWerner.CertificateX2InputSel

@[expose] public section


/-!
# Input stage: key sums of trial keys through the checked `V` columns

For a source key whose block is the trial `N k = (A)(A)ᵀ` with `A = 2^-80 F` (degree 1), the input-block
lookup is `2^-160 ∑_c V(a, c) V(b, c)` with `V = GJ F` (`x2Lookup_trial_key`); with checked `V` columns
(`x2V_get3_cols`) this is `2^-160 ∑_c ent(V_c, a) ent(V_c, b)`, i.e. `ibIB` of the part
`(Vcols, Vcols, 3 ratio)` divided by `3 den_c` (`x2Lookup_trial_ib`).
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

theorem x2Get3_smul {p q r : ℕ} {ι : Type*} (c : ℚ) (V : Matrix (Fin p × Fin q × Fin r) ι ℚ) (i j k : ℕ) (d : ι) :
    x2Get3 (c • V) i j k d = c * x2Get3 V i j k d := by
  unfold x2Get3
  split_ifs
  · rfl
  · ring

/-- The lookup of a degree-1 trial key, through `GJ F`. -/
theorem x2Lookup_trial_key (D : X2Data) (s : Fin 3) (N : X2Blocks s) (k : x2Key s) {n : ℕ}
    (F : Matrix (x2Col s k) (Fin n) ℤ)
    (hN : N k = ((1 / 2 ^ 80 : ℚ) • F.map (Int.cast : ℤ → ℚ)) * ((1 / 2 ^ 80 : ℚ) • F.map (Int.cast : ℤ → ℚ))ᵀ)
    (hdeg : x2KeyDegree s k ≠ 2) (a b : Fin 3 → ℕ) :
    x2Lookup (x2InputBlock D s N k) a b = (1 / 2 ^ 160 : ℚ) *
      ∑ c : Fin n, x2Get3 (x2GJ D s k * F.map (Int.cast : ℤ → ℚ)) (a 0) (a 1) (a 2) c *
        x2Get3 (x2GJ D s k * F.map (Int.cast : ℤ → ℚ)) (b 0) (b 1) (b 2) c := by
  have hN' : N k = ((1 / 2 ^ 80 : ℚ) • F.map (Int.cast : ℤ → ℚ)) * ((1 / 2 ^ 80 : ℚ) • F.map (Int.cast : ℤ → ℚ))ᵀ +
      (0 : Matrix (x2Col s k) (Fin 0) ℚ) * (0 : Matrix (Fin 0) (Fin 0) ℚ) * (0 : Matrix (x2Col s k) (Fin 0) ℚ)ᵀ := by
    rw [hN]
    simp
  rw [x2Lookup_inputBlock_gram D s N k _ _ _ hN', if_neg hdeg, add_zero]
  unfold x2GramPart
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Matrix.mul_smul, x2Get3_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- `ibIB` of one symmetric part `(L, L, α)`. -/
theorem ibIB_single (W α : ℕ) (x y : ℕ) : ∀ L : List ℕ,
    ibIB W (ibFS [(L, L, α)]) x y = ∑ c ∈ Finset.range L.length,
      (α : ℤ) * ent W (W - 1) (L.getD c 0) x * ent W (W - 1) (L.getD c 0) y
  | [] => by simp [ibIB, ibFS]
  | F :: L => by
    have ih := ibIB_single W α x y L
    have e : ibFS [(F :: L, F :: L, α)] = (F, F, α) :: ibFS [(L, L, α)] := by
      simp [ibFS]
    rw [e]
    unfold ibIB at ih ⊢
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- `3 den_c ×` the lookup of a degree-1 trial key with checked `V` columns: the `ibIB` of its part. -/
theorem x2Lookup_trial_ib (W : ℕ) (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (n : ℕ) (GJcols Fcols Vcols : List ℕ)
    (hW : 160 ≤ W)
    (hN : N k = ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ)) *
      ((1 / 2 ^ 80 : ℚ) • (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ))ᵀ)
    (hdeg : x2KeyDegree s k ≠ 2)
    (h0 : 1 ≤ x2KeyMult s k 0) (h1 : 1 ≤ x2KeyMult s k 1) (h2 : 1 ≤ x2KeyMult s k 2)
    (hr0 : glRowOK s (x2KeyTypes s k 0) (x2KeyMult s k 0) 512 = true)
    (hr1 : glRowOK s (x2KeyTypes s k 1) (x2KeyMult s k 1) 512 = true)
    (hr2 : glRowOK s (x2KeyTypes s k 2) (x2KeyMult s k 2) 512 = true)
    (hlen : GJcols.length = x2KeySize s k) (hsz : x2KeySize s k ≤ 512)
    (hchk : ∀ d < x2KeySize s k, gjCheck W s (x2KeyTypes s k 0) (x2KeyTypes s k 1) (x2KeyTypes s k 2)
      (x2KeyMult s k 0) (x2KeyMult s k 1) (x2KeyMult s k 2) (x2JCols (x2KeyGlobal s k) d) (GJcols.getD d 0) = true)
    (hv : ∀ c < n, vCheck W (x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2) (x2KeySize s k) GJcols
      (Fcols.getD c 0) (Vcols.getD c 0) = true)
    (hVlen : Vcols.length = n)
    (a b : Fin 3 → ℕ) (ha0 : a 0 < x2KeyMult s k 0) (ha1 : a 1 < x2KeyMult s k 1) (ha2 : a 2 < x2KeyMult s k 2)
    (hb0 : b 0 < x2KeyMult s k 0) (hb1 : b 1 < x2KeyMult s k 1) (hb2 : b 2 < x2KeyMult s k 2) :
    (3 * 46188793025384413423571871319830538981162952029845382496256000 : ℚ) *
        x2Lookup (x2InputBlock x2DataConcrete s N k) a b =
      (ibIB W (ibFS [(Vcols, Vcols, 94810963968000)])
        (kflat (x2KeyMult s k 1) (x2KeyMult s k 2) (a 0) (a 1) (a 2))
        (kflat (x2KeyMult s k 1) (x2KeyMult s k 2) (b 0) (b 1) (b 2)) : ℚ) := by
  rw [x2Lookup_trial_key x2DataConcrete s N k _ hN hdeg a b]
  simp only [x2V_get3_cols W s k n GJcols Fcols Vcols hW h0 h1 h2 hr0 hr1 hr2 hlen hsz hchk hv _ _ _ ha0 ha1 ha2,
    x2V_get3_cols W s k n GJcols Fcols Vcols hW h0 h1 h2 hr0 hr1 hr2 hlen hsz hchk hv _ _ _ hb0 hb1 hb2]
  rw [ibIB_single, hVlen, Fin.sum_univ_eq_sum_range
    (fun c => (ent W (W - 1) (Vcols.getD c 0) (kflat (x2KeyMult s k 1) (x2KeyMult s k 2) (a 0) (a 1) (a 2)) : ℚ) *
      (ent W (W - 1) (Vcols.getD c 0) (kflat (x2KeyMult s k 1) (x2KeyMult s k 2) (b 0) (b 1) (b 2)) : ℚ)) n]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

end X2
end ThreeCopyQutritWerner
