module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 4, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x146
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k54 : x2Key 2 := ⟨54, by decide⟩
x2_gj_cols gj345 345 2 1 4 6 256
theorem gjc54_0 : (List.range 55).all (fun d => gjCheck 256 2 1 4 6 4 15 11 (x2JCols 345 (0 + d)) (gj345.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok54 : ∀ d < x2KeySize 2 k54, gjCheck 256 2 (x2KeyTypes 2 k54 0) (x2KeyTypes 2 k54 1) (x2KeyTypes 2 k54 2) (x2KeyMult 2 k54 0) (x2KeyMult 2 k54 1) (x2KeyMult 2 k54 2) (x2JCols (x2KeyGlobal 2 k54) d) (gj345.getD d 0) = true := by
  have hr : x2KeySize 2 k54 = 55 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 4 6 4 15 11 (x2JCols 345 d) (gj345.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 4 6 4 15 11 (x2JCols 345 d) (gj345.getD d 0)) 0 55 gjc54_0 d (Nat.zero_le d) (by omega)
x2_nat_list K2x146k0c "verification/matrix-literals/x2-transfer/corr-light/K2x146k0.hex"
x2_nat_list A2x146k0c "verification/matrix-literals/x2-transfer/corr-light/A2x146k0.hex"
x2_vk_cols u345 gj345 K2x146k0c 256 660
x2_ua_cols ua345 u345 A2x146k0c 660 55
theorem cchk54 : corrKeyChk 2 k54 55 gj345 K2x146k0c u345 A2x146k0c ua345 := by
  have h1 : x2KeyDegree 2 k54 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k54 0 ∧ 1 ≤ x2KeyMult 2 k54 1 ∧ 1 ≤ x2KeyMult 2 k54 2 ∧ glRowOK 2 (x2KeyTypes 2 k54 0) (x2KeyMult 2 k54 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k54 1) (x2KeyMult 2 k54 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k54 2) (x2KeyMult 2 k54 2) 512 = true ∧ gj345.length = x2KeySize 2 k54 ∧ x2KeySize 2 k54 ≤ 512 := by decide +kernel
  have h2 : ∀ c < 55, vCheck 256 (x2KeyMult 2 k54 0 * x2KeyMult 2 k54 1 * x2KeyMult 2 k54 2) (x2KeySize 2 k54) gj345 (K2x146k0c.getD c 0) (u345.getD c 0) = true ∧ slotBoundCheck 256 18 (x2KeyMult 2 k54 0 * x2KeyMult 2 k54 1 * x2KeyMult 2 k54 2) (u345.getD c 0) = true := by decide +kernel
  have h3 : u345.length = 55 ∧ ua345.length = 55 ∧ 55 ≤ 512 := by decide +kernel
  have h4 : ∀ c < 55, uaCheck (x2KeyMult 2 k54 0 * x2KeyMult 2 k54 1 * x2KeyMult 2 k54 2) 55 u345 (A2x146k0c.getD c 0) (ua345.getD c 0) = true := by decide +kernel
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h1
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, gjok54, h2, h3.1, h3.2.1, h3.2.2, h4⟩

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k54, ibFS [(ua345, u345, 3)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 4, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN54 : N k54 = x2CorrForm 2 k54 55 K2x146k0c A2x146k0c) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 4 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_corrChk 2 N k54 55 _ gj345 K2x146k0c u345 A2x146k0c ua345 (by decide) hN54 cchk54

end ThreeCopyQutritWerner.X2.InK2x146
