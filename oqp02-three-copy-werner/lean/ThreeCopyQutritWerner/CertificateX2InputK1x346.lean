module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 4, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x346
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k118 : x2Key 1 := ⟨118, by decide⟩
x2_gj_cols gj240 240 1 3 4 6 256
theorem gjc118_0 : (List.range 95).all (fun d => gjCheck 256 1 3 4 6 9 7 17 (x2JCols 240 (0 + d)) (gj240.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc118_95 : (List.range 84).all (fun d => gjCheck 256 1 3 4 6 9 7 17 (x2JCols 240 (95 + d)) (gj240.getD (95 + d) 0)) = true := by decide +kernel
theorem gjok118 : ∀ d < x2KeySize 1 k118, gjCheck 256 1 (x2KeyTypes 1 k118 0) (x2KeyTypes 1 k118 1) (x2KeyTypes 1 k118 2) (x2KeyMult 1 k118 0) (x2KeyMult 1 k118 1) (x2KeyMult 1 k118 2) (x2JCols (x2KeyGlobal 1 k118) d) (gj240.getD d 0) = true := by
  have hr : x2KeySize 1 k118 = 179 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 4 6 9 7 17 (x2JCols 240 d) (gj240.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 95) ∨ (95 ≤ d ∧ d < 179)) with h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 4 6 9 7 17 (x2JCols 240 d) (gj240.getD d 0)) 0 95 gjc118_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 4 6 9 7 17 (x2JCols 240 d) (gj240.getD d 0)) 95 84 gjc118_95 d h.1 (by omega)
x2_nat_list K1x346k0c "verification/matrix-literals/x2-transfer/corr-light/K1x346k0.hex"
x2_nat_list A1x346k0c "verification/matrix-literals/x2-transfer/corr-light/A1x346k0.hex"
x2_vk_cols u240 gj240 K1x346k0c 256 1071
x2_ua_cols ua240 u240 A1x346k0c 1071 97
theorem cchk118 : corrKeyChk 1 k118 97 gj240 K1x346k0c u240 A1x346k0c ua240 := by
  have h1 : x2KeyDegree 1 k118 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k118 0 ∧ 1 ≤ x2KeyMult 1 k118 1 ∧ 1 ≤ x2KeyMult 1 k118 2 ∧ glRowOK 1 (x2KeyTypes 1 k118 0) (x2KeyMult 1 k118 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k118 1) (x2KeyMult 1 k118 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k118 2) (x2KeyMult 1 k118 2) 512 = true ∧ gj240.length = x2KeySize 1 k118 ∧ x2KeySize 1 k118 ≤ 512 := by decide +kernel
  have h2 : ∀ c < 97, vCheck 256 (x2KeyMult 1 k118 0 * x2KeyMult 1 k118 1 * x2KeyMult 1 k118 2) (x2KeySize 1 k118) gj240 (K1x346k0c.getD c 0) (u240.getD c 0) = true ∧ slotBoundCheck 256 18 (x2KeyMult 1 k118 0 * x2KeyMult 1 k118 1 * x2KeyMult 1 k118 2) (u240.getD c 0) = true := by decide +kernel
  have h3 : u240.length = 97 ∧ ua240.length = 97 ∧ 97 ≤ 512 := by decide +kernel
  have h4 : ∀ c < 97, uaCheck (x2KeyMult 1 k118 0 * x2KeyMult 1 k118 1 * x2KeyMult 1 k118 2) 97 u240 (A1x346k0c.getD c 0) (ua240.getD c 0) = true := by decide +kernel
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h1
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, gjok118, h2, h3.1, h3.2.1, h3.2.2, h4⟩

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k118, ibFS [(ua240, u240, 3)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 4, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN118 : N k118 = x2CorrForm 1 k118 97 K1x346k0c A1x346k0c) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 4 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_corrChk 1 N k118 97 _ gj240 K1x346k0c u240 A1x346k0c ua240 (by decide) hN118 cchk118

end ThreeCopyQutritWerner.X2.InK1x346
