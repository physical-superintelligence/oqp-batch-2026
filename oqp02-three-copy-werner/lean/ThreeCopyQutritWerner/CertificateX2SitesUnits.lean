module

public import ThreeCopyQutritWerner.CertificateX2SitesUnit
public import ThreeCopyQutritWerner.CertificateX2SitesFrames
public import ThreeCopyQutritWerner.CertificateX2BridgeParity

@[expose] public section


/-!
# Unit coordinates, flat slots and the explicit unit weights

`x2sFlatU s u` (flat slot `off t + a m_t + b` of a unit `u : X2U s`), the weight tables and the
explicit unit weights `x2SitesW s u` (the bridge's `wU s u = ∑_{d ∈ piv} W_s[d, u] δ_{perms[d]}`).
-/

set_option maxRecDepth 100000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner.X2Sites

open X2

/-! ## Unit weights -/

/-- Slot offsets of the unit coordinates `X2U s` (types `Fin 8`; sector 1 has 8 types, sectors 0 and
2 seven, type 7 empty). -/
def x2sOffU (s : Fin 3) : Fin 8 → ℕ :=
  if s = 1 then x2sOff1 else ![0, 1, 17, 42, 67, 292, 392, 513]

/-- Flat slot of a unit coordinate: `off t + a m_t + b`. -/
def x2sFlatU (s : Fin 3) (u : X2U s) : ℕ := x2sOffU s u.1 + u.2.1 * x2Mult s u.1 + u.2.2

/-- Weight numerator tables (rows: units `u`, entries: pivots `p`, offset `2^25`). -/
noncomputable def x2sWTab (s : Fin 3) : List (List ℕ) := if s = 1 then x2sW1 else x2sW2

/-- Weight denominators. -/
def x2sDen (s : Fin 3) : ℕ := if s = 1 then 57153600 else 6350400

/-- The explicit unit weights: `x2SitesW s u σ = ∑_p [σ = perm (piv p)] W_s[p, u]`. -/
noncomputable def x2SitesW (s : Fin 3) (u : X2U s) (σ : Equiv.Perm (Fin 6)) : ℂ :=
  ∑ p : Fin 513, if σ = x2SitesPerm (x2SitesPiv p) then
    ((((x2sWTab s).getD (x2sFlatU s u) []).getD p 0 : ℂ) - 2 ^ 25) / (x2sDen s : ℂ) else 0

theorem sum_weight_collapse (c : Fin 513 → ℂ) (f : Equiv.Perm (Fin 6) → ℂ) :
    ∑ σ, (∑ p : Fin 513, if σ = x2SitesPerm (x2SitesPiv p) then c p else 0) * f σ =
      ∑ p : Fin 513, c p * f (x2SitesPerm (x2SitesPiv p)) := by
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_ite_eq' Finset.univ (x2SitesPerm (x2SitesPiv p)), if_pos (Finset.mem_univ _)]

/-! ## Index facts -/

theorem x2sMult1 : ∀ t : Fin 8, x2Mult 1 t = certificateDescendantFrames1SourceSize t := by decide +kernel

theorem x2sMult2 : ∀ t : Fin 7, x2Mult 2 (Fin.castSucc t) = certificateDescendantFrames2SourceSize t := by
  decide +kernel

theorem x2sMult0 : ∀ t : Fin 7, x2Mult 0 (Fin.castSucc t) = certificateDescendantFrames2SourceSize t := by
  decide +kernel

theorem x2sOffU_step : ∀ s : Fin 3, ∀ t t' : Fin 8, (t : ℕ) < t' →
    x2sOffU s t + x2Mult s t * x2Mult s t ≤ x2sOffU s t' := by decide +kernel

theorem x2sOffU_end : ∀ s : Fin 3, ∀ t : Fin 8, x2sOffU s t + x2Mult s t * x2Mult s t ≤ 513 := by
  decide +kernel

theorem x2sOffU1 : ∀ t : Fin 8, x2sOffU 1 t = x2sOff1 t := by decide +kernel

theorem x2sOffU2 : ∀ t : Fin 7, x2sOffU 2 (Fin.castSucc t) = x2sOff0 t := by decide +kernel

theorem x2sOffU0 : ∀ t : Fin 7, x2sOffU 0 (Fin.castSucc t) = x2sOff0 t := by decide +kernel

theorem x2sFlatU_lt (s : Fin 3) (u : X2U s) : x2sFlatU s u < 513 :=
  layout_lt (x2Mult s) (x2sOffU s) 513 (x2sOffU_end s) u.1 u.2.1 u.2.2

/-- A frame slot `(t', i, j)` of the unit layout of sector `s` equals the flat slot of `u` iff
the coordinates agree. -/
theorem x2sFlatU_iff (s : Fin 3) (u : X2U s) (t' : Fin 8) (i j : ℕ) (hi : i < x2Mult s t')
    (hj : j < x2Mult s t') :
    x2sOffU s t' + i * x2Mult s t' + j = x2sFlatU s u ↔
      (u.1 : ℕ) = t' ∧ (u.2.1 : ℕ) = i ∧ (u.2.2 : ℕ) = j := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := layout_inj (x2Mult s) (x2sOffU s) (x2sOffU_step s) t' u.1 ⟨i, hi⟩ ⟨j, hj⟩
      u.2.1 u.2.2 h
    exact ⟨congrArg Fin.val h1.symm, h2.symm, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩
    have ht : u.1 = t' := Fin.ext h1
    unfold x2sFlatU
    rw [h2, h3, ht]

theorem x2sWTab1 : x2sWTab 1 = x2sW1 := rfl
theorem x2sWTab2 : x2sWTab 2 = x2sW2 := rfl
theorem x2sDen1 : x2sDen 1 = 57153600 := rfl
theorem x2sDen2 : x2sDen 2 = 6350400 := rfl

end ThreeCopyQutritWerner.X2Sites
