module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 5, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x456
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k140 : x2Key 1 := ⟨140, by decide⟩
x2_gj_cols gj262 262 1 4 5 6 256
theorem gjc140_0 : (List.range 122).all (fun d => gjCheck 256 1 4 5 6 7 7 17 (x2JCols 262 (0 + d)) (gj262.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc140_122 : (List.range 17).all (fun d => gjCheck 256 1 4 5 6 7 7 17 (x2JCols 262 (122 + d)) (gj262.getD (122 + d) 0)) = true := by decide +kernel
theorem gjok140 : ∀ d < x2KeySize 1 k140, gjCheck 256 1 (x2KeyTypes 1 k140 0) (x2KeyTypes 1 k140 1) (x2KeyTypes 1 k140 2) (x2KeyMult 1 k140 0) (x2KeyMult 1 k140 1) (x2KeyMult 1 k140 2) (x2JCols (x2KeyGlobal 1 k140) d) (gj262.getD d 0) = true := by
  have hr : x2KeySize 1 k140 = 139 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 5 6 7 7 17 (x2JCols 262 d) (gj262.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 122) ∨ (122 ≤ d ∧ d < 139)) with h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 4 5 6 7 7 17 (x2JCols 262 d) (gj262.getD d 0)) 0 122 gjc140_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 4 5 6 7 7 17 (x2JCols 262 d) (gj262.getD d 0)) 122 17 gjc140_122 d h.1 (by omega)
x2_nat_list K1x456k0c "verification/matrix-literals/x2-transfer/corr-light/K1x456k0.hex"
x2_nat_list A1x456k0c "verification/matrix-literals/x2-transfer/corr-light/A1x456k0.hex"
x2_vk_cols u262 gj262 K1x456k0c 256 833
x2_ua_cols ua262 u262 A1x456k0c 833 98
theorem cchk140 : corrKeyChk 1 k140 98 gj262 K1x456k0c u262 A1x456k0c ua262 := by
  have h1 : x2KeyDegree 1 k140 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k140 0 ∧ 1 ≤ x2KeyMult 1 k140 1 ∧ 1 ≤ x2KeyMult 1 k140 2 ∧ glRowOK 1 (x2KeyTypes 1 k140 0) (x2KeyMult 1 k140 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k140 1) (x2KeyMult 1 k140 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k140 2) (x2KeyMult 1 k140 2) 512 = true ∧ gj262.length = x2KeySize 1 k140 ∧ x2KeySize 1 k140 ≤ 512 := by decide +kernel
  have h2 : ∀ c < 98, vCheck 256 (x2KeyMult 1 k140 0 * x2KeyMult 1 k140 1 * x2KeyMult 1 k140 2) (x2KeySize 1 k140) gj262 (K1x456k0c.getD c 0) (u262.getD c 0) = true ∧ slotBoundCheck 256 18 (x2KeyMult 1 k140 0 * x2KeyMult 1 k140 1 * x2KeyMult 1 k140 2) (u262.getD c 0) = true := by decide +kernel
  have h3 : u262.length = 98 ∧ ua262.length = 98 ∧ 98 ≤ 512 := by decide +kernel
  have h4 : ∀ c < 98, uaCheck (x2KeyMult 1 k140 0 * x2KeyMult 1 k140 1 * x2KeyMult 1 k140 2) 98 u262 (A1x456k0c.getD c 0) (ua262.getD c 0) = true := by decide +kernel
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h1
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, gjok140, h2, h3.1, h3.2.1, h3.2.2, h4⟩

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k140, ibFS [(ua262, u262, 3)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![4, 5, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN140 : N k140 = x2CorrForm 1 k140 98 K1x456k0c A1x456k0c) :
    ∀ e ∈ ks, keyOK (x2Mult 1 4 * x2Mult 1 5 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_corrChk 1 N k140 98 _ gj262 K1x456k0c u262 A1x456k0c ua262 (by decide) hN140 cchk140

end ThreeCopyQutritWerner.X2.InK1x456
