module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 0, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x006
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k3 : x2Key 1 := ⟨3, by decide⟩
x2_gj_cols gj125 125 1 0 0 6 256
theorem gjc3_0 : (List.range 3).all (fun d => gjCheck 256 1 0 0 6 1 1 17 (x2JCols 125 (0 + d)) (gj125.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok3 : ∀ d < x2KeySize 1 k3, gjCheck 256 1 (x2KeyTypes 1 k3 0) (x2KeyTypes 1 k3 1) (x2KeyTypes 1 k3 2) (x2KeyMult 1 k3 0) (x2KeyMult 1 k3 1) (x2KeyMult 1 k3 2) (x2JCols (x2KeyGlobal 1 k3) d) (gj125.getD d 0) = true := by
  have hr : x2KeySize 1 k3 = 3 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 0 6 1 1 17 (x2JCols 125 d) (gj125.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 0 6 1 1 17 (x2JCols 125 d) (gj125.getD d 0)) 0 3 gjc3_0 d (Nat.zero_le d) (by omega)
x2_nat_list K1x006k0c "verification/matrix-literals/x2-transfer/corr-light/K1x006k0.hex"
x2_nat_list A1x006k0c "verification/matrix-literals/x2-transfer/corr-light/A1x006k0.hex"
x2_vk_cols u125 gj125 K1x006k0c 256 17
x2_ua_cols ua125 u125 A1x006k0c 17 1
theorem cchk3 : corrKeyChk 1 k3 1 gj125 K1x006k0c u125 A1x006k0c ua125 := by
  have h1 : x2KeyDegree 1 k3 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k3 0 ∧ 1 ≤ x2KeyMult 1 k3 1 ∧ 1 ≤ x2KeyMult 1 k3 2 ∧ glRowOK 1 (x2KeyTypes 1 k3 0) (x2KeyMult 1 k3 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k3 1) (x2KeyMult 1 k3 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k3 2) (x2KeyMult 1 k3 2) 512 = true ∧ gj125.length = x2KeySize 1 k3 ∧ x2KeySize 1 k3 ≤ 512 := by decide +kernel
  have h2 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k3 0 * x2KeyMult 1 k3 1 * x2KeyMult 1 k3 2) (x2KeySize 1 k3) gj125 (K1x006k0c.getD c 0) (u125.getD c 0) = true ∧ slotBoundCheck 256 18 (x2KeyMult 1 k3 0 * x2KeyMult 1 k3 1 * x2KeyMult 1 k3 2) (u125.getD c 0) = true := by decide +kernel
  have h3 : u125.length = 1 ∧ ua125.length = 1 ∧ 1 ≤ 512 := by decide +kernel
  have h4 : ∀ c < 1, uaCheck (x2KeyMult 1 k3 0 * x2KeyMult 1 k3 1 * x2KeyMult 1 k3 2) 1 u125 (A1x006k0c.getD c 0) (ua125.getD c 0) = true := by decide +kernel
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h1
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, gjok3, h2, h3.1, h3.2.1, h3.2.2, h4⟩

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k3, ibFS [(ua125, u125, 3)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 0, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN3 : N k3 = x2CorrForm 1 k3 1 K1x006k0c A1x006k0c) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 0 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_corrChk 1 N k3 1 _ gj125 K1x006k0c u125 A1x006k0c ua125 (by decide) hN3 cchk3

end ThreeCopyQutritWerner.X2.InK1x006
