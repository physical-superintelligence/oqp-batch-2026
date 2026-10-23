module

public import ThreeCopyQutritWerner.CertificateX2InputV
public import ThreeCopyQutritWerner.CertificateX2Data
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-!
# Input stage: the checked `GJ` and `V` columns are the bridge's factors

For a source key `k` of the concrete data (image columns `x2JCols g d`, `g = x2KeyGlobal s k`), candidate
`GJ` columns that pass `gjCheck` are the natural-coordinate entries of the bridge's
`x2GJ x2DataConcrete s k` (`x2GJ_get3_cols`), and candidate `V` columns that pass `vCheck` against them are
the entries of `x2GJ x2DataConcrete s k * F` for the integer factor `F` with packed columns `Fcols`
(`x2V_get3_cols`; with `Fcols = x2TrialAll.getD g []` this `F` is the `x2TrialFactor s k`).
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-- Flat index of natural coordinates of a key's ambient. -/
def kflat (m1 m2 y0 y1 y2 : ℕ) : ℕ := (y0 * m1 + y1) * m2 + y2

theorem x2Get3_image_kflat (s : Fin 3) (k : x2Key s) (y0 y1 y2 : ℕ) (d : x2Col s k)
    (h0 : y0 < x2KeyMult s k 0) (h1 : y1 < x2KeyMult s k 1) (h2 : y2 < x2KeyMult s k 2) :
    x2Get3 ((x2DataConcrete.image s k).map (Int.cast : ℤ → ℚ)) y0 y1 y2 d =
      (ent 11 10 (x2JCols (x2KeyGlobal s k) d) (kflat (x2KeyMult s k 1) (x2KeyMult s k 2) y0 y1 y2) : ℚ) := by
  unfold x2Get3
  rw [dif_pos ⟨h0, h1, h2⟩]
  rfl

/-- The `GJ` columns of a key from candidate columns passing `gjCheck`. -/
theorem x2GJ_get3_cols (W : ℕ) (s : Fin 3) (k : x2Key s) (GJcols : List ℕ) (hW : 48 ≤ W)
    (h0 : 1 ≤ x2KeyMult s k 0) (h1 : 1 ≤ x2KeyMult s k 1) (h2 : 1 ≤ x2KeyMult s k 2)
    (hr0 : glRowOK s (x2KeyTypes s k 0) (x2KeyMult s k 0) 512 = true)
    (hr1 : glRowOK s (x2KeyTypes s k 1) (x2KeyMult s k 1) 512 = true)
    (hr2 : glRowOK s (x2KeyTypes s k 2) (x2KeyMult s k 2) 512 = true)
    (hchk : ∀ d < x2KeySize s k, gjCheck W s (x2KeyTypes s k 0) (x2KeyTypes s k 1) (x2KeyTypes s k 2)
      (x2KeyMult s k 0) (x2KeyMult s k 1) (x2KeyMult s k 2) (x2JCols (x2KeyGlobal s k) d) (GJcols.getD d 0) = true)
    (y0 y1 y2 : ℕ) (hy0 : y0 < x2KeyMult s k 0) (hy1 : y1 < x2KeyMult s k 1) (hy2 : y2 < x2KeyMult s k 2)
    (d : x2Col s k) :
    x2Get3 (x2GJ x2DataConcrete s k) y0 y1 y2 d =
      (ent W (W - 1) (GJcols.getD d 0) (kflat (x2KeyMult s k 1) (x2KeyMult s k 2) y0 y1 y2) : ℚ) := by
  obtain ⟨_, _, hval⟩ := gjCheck_sound W s _ _ _ _ _ _ _ _ hW h0 h1 h2 hr0 hr1 hr2 (hchk d d.isLt)
  rw [x2GJ_get3, kflat, hval y0 hy0 y1 hy1 y2 hy2]
  push_cast
  apply Finset.sum_congr rfl
  intro z0 hz0
  apply Finset.sum_congr rfl
  intro z1 hz1
  apply Finset.sum_congr rfl
  intro z2 hz2
  rw [x2Get3_image_kflat s k z0 z1 z2 d (Finset.mem_range.mp hz0) (Finset.mem_range.mp hz1)
    (Finset.mem_range.mp hz2), kflat]
  ring

/-- The integer factor with packed columns `Fcols` (80-bit slots, offset `2^79`). -/
def x2FactorOf (r n : ℕ) (Fcols : List ℕ) : Matrix (Fin r) (Fin n) ℤ :=
  Matrix.of fun i c => ent 80 79 (Fcols.getD c 0) i

/-- The `V = GJ F` columns of a key from candidate columns passing `vCheck` against checked `GJ`
columns. -/
theorem x2V_get3_cols (W : ℕ) (s : Fin 3) (k : x2Key s) (n : ℕ) (GJcols Fcols Vcols : List ℕ) (hW : 160 ≤ W)
    (h0 : 1 ≤ x2KeyMult s k 0) (h1 : 1 ≤ x2KeyMult s k 1) (h2 : 1 ≤ x2KeyMult s k 2)
    (hr0 : glRowOK s (x2KeyTypes s k 0) (x2KeyMult s k 0) 512 = true)
    (hr1 : glRowOK s (x2KeyTypes s k 1) (x2KeyMult s k 1) 512 = true)
    (hr2 : glRowOK s (x2KeyTypes s k 2) (x2KeyMult s k 2) 512 = true)
    (hlen : GJcols.length = x2KeySize s k) (hsz : x2KeySize s k ≤ 512)
    (hchk : ∀ d < x2KeySize s k, gjCheck W s (x2KeyTypes s k 0) (x2KeyTypes s k 1) (x2KeyTypes s k 2)
      (x2KeyMult s k 0) (x2KeyMult s k 1) (x2KeyMult s k 2) (x2JCols (x2KeyGlobal s k) d) (GJcols.getD d 0) = true)
    (hv : ∀ c < n, vCheck W (x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2) (x2KeySize s k) GJcols
      (Fcols.getD c 0) (Vcols.getD c 0) = true)
    (y0 y1 y2 : ℕ) (hy0 : y0 < x2KeyMult s k 0) (hy1 : y1 < x2KeyMult s k 1) (hy2 : y2 < x2KeyMult s k 2)
    (c : Fin n) :
    x2Get3 (x2GJ x2DataConcrete s k * (x2FactorOf (x2KeySize s k) n Fcols).map (Int.cast : ℤ → ℚ)) y0 y1 y2 c =
      (ent W (W - 1) (Vcols.getD c 0) (kflat (x2KeyMult s k 1) (x2KeyMult s k 2) y0 y1 y2) : ℚ) := by
  have hGJ : ∀ d < x2KeySize s k, GJcols.getD d 0 < 2 ^ (W * (x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2)) ∧
      ∀ t < x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2, |ent W (W - 1) (GJcols.getD d 0) t| ≤ 2 ^ 37 := by
    intro d hd
    obtain ⟨hl, hb, _⟩ := gjCheck_sound W s _ _ _ _ _ _ _ _ (by omega) h0 h1 h2 hr0 hr1 hr2 (hchk d hd)
    exact ⟨hl, hb⟩
  obtain ⟨_, _, hval⟩ := vCheck_sound W _ _ GJcols _ _ hW hlen hsz hGJ (hv c c.isLt)
  have hk : kflat (x2KeyMult s k 1) (x2KeyMult s k 2) y0 y1 y2 <
      x2KeyMult s k 0 * x2KeyMult s k 1 * x2KeyMult s k 2 := by
    unfold kflat
    have := site_idx_lt (x2KeyMult s k 0) (x2KeyMult s k 1) (x2KeyMult s k 2) y0 y1 y2 hy0 hy1 hy2
    rwa [← Nat.mul_assoc] at this
  rw [x2Get3_mul, hval _ hk]
  push_cast
  apply Finset.sum_congr rfl
  intro d _
  rw [x2GJ_get3_cols W s k GJcols (by omega) h0 h1 h2 hr0 hr1 hr2 hchk y0 y1 y2 hy0 hy1 hy2 d]
  simp only [Matrix.map_apply, x2FactorOf, Matrix.of_apply]
  ring

end X2
end ThreeCopyQutritWerner
