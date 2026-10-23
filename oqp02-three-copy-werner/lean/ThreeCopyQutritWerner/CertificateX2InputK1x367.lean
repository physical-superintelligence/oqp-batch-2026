module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 6, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x367
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k126 : x2Key 1 := ⟨126, by decide⟩
x2_gj_cols gj248 248 1 3 6 7 256
theorem gjc126_0 : (List.range 111).all (fun d => gjCheck 256 1 3 6 7 9 17 6 (x2JCols 248 (0 + d)) (gj248.getD (0 + d) 0)) = true := by decide +kernel
theorem gjc126_111 : (List.range 42).all (fun d => gjCheck 256 1 3 6 7 9 17 6 (x2JCols 248 (111 + d)) (gj248.getD (111 + d) 0)) = true := by decide +kernel
theorem gjok126 : ∀ d < x2KeySize 1 k126, gjCheck 256 1 (x2KeyTypes 1 k126 0) (x2KeyTypes 1 k126 1) (x2KeyTypes 1 k126 2) (x2KeyMult 1 k126 0) (x2KeyMult 1 k126 1) (x2KeyMult 1 k126 2) (x2JCols (x2KeyGlobal 1 k126) d) (gj248.getD d 0) = true := by
  have hr : x2KeySize 1 k126 = 153 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 6 7 9 17 6 (x2JCols 248 d) (gj248.getD d 0) = true
  rcases (by omega : (0 ≤ d ∧ d < 111) ∨ (111 ≤ d ∧ d < 153)) with h | h
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 6 7 9 17 6 (x2JCols 248 d) (gj248.getD d 0)) 0 111 gjc126_0 d h.1 (by omega)
  · exact rangeAll_sound (fun d => gjCheck 256 1 3 6 7 9 17 6 (x2JCols 248 d) (gj248.getD d 0)) 111 42 gjc126_111 d h.1 (by omega)
x2_v_cols v248 gj248 248 256 918
theorem vc126_0 : (List.range 55).all (fun c => vCheck 256 918 153 gj248 (x2Trial_248.getD (0 + c) 0) (v248.getD (0 + c) 0)) = true := by decide +kernel
theorem vc126_55 : (List.range 31).all (fun c => vCheck 256 918 153 gj248 (x2Trial_248.getD (55 + c) 0) (v248.getD (55 + c) 0)) = true := by decide +kernel
theorem vok126 : ∀ c < 86, vCheck 256 (x2KeyMult 1 k126 0 * x2KeyMult 1 k126 1 * x2KeyMult 1 k126 2) (x2KeySize 1 k126) gj248 (x2Trial_248.getD c 0) (v248.getD c 0) = true := by
  intro c hc
  show vCheck 256 918 153 gj248 (x2Trial_248.getD c 0) (v248.getD c 0) = true
  rcases (by omega : (0 ≤ c ∧ c < 55) ∨ (55 ≤ c ∧ c < 86)) with h | h
  · exact rangeAll_sound (fun c => vCheck 256 918 153 gj248 (x2Trial_248.getD c 0) (v248.getD c 0)) 0 55 vc126_0 c h.1 (by omega)
  · exact rangeAll_sound (fun c => vCheck 256 918 153 gj248 (x2Trial_248.getD c 0) (v248.getD c 0)) 55 31 vc126_55 c h.1 (by omega)
theorem small126 : x2KeyDegree 1 k126 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k126 0 ∧ 1 ≤ x2KeyMult 1 k126 1 ∧ 1 ≤ x2KeyMult 1 k126 2 ∧ glRowOK 1 (x2KeyTypes 1 k126 0) (x2KeyMult 1 k126 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k126 1) (x2KeyMult 1 k126 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k126 2) (x2KeyMult 1 k126 2) 512 = true ∧ gj248.length = x2KeySize 1 k126 ∧ x2KeySize 1 k126 ≤ 512 ∧ v248.length = 86 := by decide +kernel
theorem chk126 : trialKeyChk 1 k126 86 gj248 x2Trial_248 v248 :=
  trialKeyChk_intro 1 k126 86 gj248 x2Trial_248 v248 small126 gjok126 vok126

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k126, ibFS [(v248, v248, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 6, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN126 : N k126 = x2TrialForm 1 k126) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 6 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k126 86 _ gj248 x2Trial_248 v248 (by decide) (by rw [hN126]; exact trialForm_eq 1 k126 86 x2Trial_248 (by decide) rfl) chk126

end ThreeCopyQutritWerner.X2.InK1x367
