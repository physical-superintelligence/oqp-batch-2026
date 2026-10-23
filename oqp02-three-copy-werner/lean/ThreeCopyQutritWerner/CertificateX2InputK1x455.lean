module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 5, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x455
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k138 : x2Key 1 := ⟨138, by decide⟩
x2_gj_cols gj260 260 1 4 5 5 256
theorem gjc138_0 : (List.range 34).all (fun d => gjCheck 256 1 4 5 5 7 7 7 (x2JCols 260 (0 + d)) (gj260.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok138 : ∀ d < x2KeySize 1 k138, gjCheck 256 1 (x2KeyTypes 1 k138 0) (x2KeyTypes 1 k138 1) (x2KeyTypes 1 k138 2) (x2KeyMult 1 k138 0) (x2KeyMult 1 k138 1) (x2KeyMult 1 k138 2) (x2JCols (x2KeyGlobal 1 k138) d) (gj260.getD d 0) = true := by
  have hr : x2KeySize 1 k138 = 34 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 5 5 7 7 7 (x2JCols 260 d) (gj260.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 5 5 7 7 7 (x2JCols 260 d) (gj260.getD d 0)) 0 34 gjc138_0 d (Nat.zero_le d) (by omega)
x2_v_cols v260 gj260 260 256 343
theorem vc138_0 : (List.range 24).all (fun c => vCheck 256 343 34 gj260 (x2Trial_260.getD (0 + c) 0) (v260.getD (0 + c) 0)) = true := by decide +kernel
theorem vok138 : ∀ c < 24, vCheck 256 (x2KeyMult 1 k138 0 * x2KeyMult 1 k138 1 * x2KeyMult 1 k138 2) (x2KeySize 1 k138) gj260 (x2Trial_260.getD c 0) (v260.getD c 0) = true := by
  intro c hc
  show vCheck 256 343 34 gj260 (x2Trial_260.getD c 0) (v260.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 343 34 gj260 (x2Trial_260.getD c 0) (v260.getD c 0)) 0 24 vc138_0 c (Nat.zero_le c) (by omega)
theorem small138 : x2KeyDegree 1 k138 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k138 0 ∧ 1 ≤ x2KeyMult 1 k138 1 ∧ 1 ≤ x2KeyMult 1 k138 2 ∧ glRowOK 1 (x2KeyTypes 1 k138 0) (x2KeyMult 1 k138 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k138 1) (x2KeyMult 1 k138 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k138 2) (x2KeyMult 1 k138 2) 512 = true ∧ gj260.length = x2KeySize 1 k138 ∧ x2KeySize 1 k138 ≤ 512 ∧ v260.length = 24 := by decide +kernel
theorem chk138 : trialKeyChk 1 k138 24 gj260 x2Trial_260 v260 :=
  trialKeyChk_intro 1 k138 24 gj260 x2Trial_260 v260 small138 gjok138 vok138
def k139 : x2Key 1 := ⟨139, by decide⟩
x2_gj_cols gj261 261 1 4 5 5 256
theorem gjc139_0 : (List.range 24).all (fun d => gjCheck 256 1 4 5 5 7 7 7 (x2JCols 261 (0 + d)) (gj261.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok139 : ∀ d < x2KeySize 1 k139, gjCheck 256 1 (x2KeyTypes 1 k139 0) (x2KeyTypes 1 k139 1) (x2KeyTypes 1 k139 2) (x2KeyMult 1 k139 0) (x2KeyMult 1 k139 1) (x2KeyMult 1 k139 2) (x2JCols (x2KeyGlobal 1 k139) d) (gj261.getD d 0) = true := by
  have hr : x2KeySize 1 k139 = 24 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 5 5 7 7 7 (x2JCols 261 d) (gj261.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 5 5 7 7 7 (x2JCols 261 d) (gj261.getD d 0)) 0 24 gjc139_0 d (Nat.zero_le d) (by omega)
x2_v_cols v261 gj261 261 256 343
theorem vc139_0 : (List.range 14).all (fun c => vCheck 256 343 24 gj261 (x2Trial_261.getD (0 + c) 0) (v261.getD (0 + c) 0)) = true := by decide +kernel
theorem vok139 : ∀ c < 14, vCheck 256 (x2KeyMult 1 k139 0 * x2KeyMult 1 k139 1 * x2KeyMult 1 k139 2) (x2KeySize 1 k139) gj261 (x2Trial_261.getD c 0) (v261.getD c 0) = true := by
  intro c hc
  show vCheck 256 343 24 gj261 (x2Trial_261.getD c 0) (v261.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 343 24 gj261 (x2Trial_261.getD c 0) (v261.getD c 0)) 0 14 vc139_0 c (Nat.zero_le c) (by omega)
theorem small139 : x2KeyDegree 1 k139 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k139 0 ∧ 1 ≤ x2KeyMult 1 k139 1 ∧ 1 ≤ x2KeyMult 1 k139 2 ∧ glRowOK 1 (x2KeyTypes 1 k139 0) (x2KeyMult 1 k139 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k139 1) (x2KeyMult 1 k139 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k139 2) (x2KeyMult 1 k139 2) 512 = true ∧ gj261.length = x2KeySize 1 k139 ∧ x2KeySize 1 k139 ≤ 512 ∧ v261.length = 14 := by decide +kernel
theorem chk139 : trialKeyChk 1 k139 14 gj261 x2Trial_261 v261 :=
  trialKeyChk_intro 1 k139 14 gj261 x2Trial_261 v261 small139 gjok139 vok139

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k138, ibFS [(v260, v260, 94810963968000)]), (k139, ibFS [(v261, v261, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![4, 5, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN138 : N k138 = x2TrialForm 1 k138) (hN139 : N k139 = x2TrialForm 1 k139) :
    ∀ e ∈ ks, keyOK (x2Mult 1 4 * x2Mult 1 5 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k138 24 _ gj260 x2Trial_260 v260 (by decide) (by rw [hN138]; exact trialForm_eq 1 k138 24 x2Trial_260 (by decide) rfl) chk138
  · exact keyOK_of_trialChk 1 N k139 14 _ gj261 x2Trial_261 v261 (by decide) (by rw [hN139]; exact trialForm_eq 1 k139 14 x2Trial_261 (by decide) rfl) chk139

end ThreeCopyQutritWerner.X2.InK1x455
