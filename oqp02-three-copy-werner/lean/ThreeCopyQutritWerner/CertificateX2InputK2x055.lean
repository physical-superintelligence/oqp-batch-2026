module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 5, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x055
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k23 : x2Key 2 := ⟨23, by decide⟩
x2_gj_cols gj314 314 2 0 5 5 256
theorem gjc23_0 : (List.range 6).all (fun d => gjCheck 256 2 0 5 5 1 10 10 (x2JCols 314 (0 + d)) (gj314.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok23 : ∀ d < x2KeySize 2 k23, gjCheck 256 2 (x2KeyTypes 2 k23 0) (x2KeyTypes 2 k23 1) (x2KeyTypes 2 k23 2) (x2KeyMult 2 k23 0) (x2KeyMult 2 k23 1) (x2KeyMult 2 k23 2) (x2JCols (x2KeyGlobal 2 k23) d) (gj314.getD d 0) = true := by
  have hr : x2KeySize 2 k23 = 6 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 5 5 1 10 10 (x2JCols 314 d) (gj314.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 5 5 1 10 10 (x2JCols 314 d) (gj314.getD d 0)) 0 6 gjc23_0 d (Nat.zero_le d) (by omega)
x2_v_cols v314 gj314 314 256 100
theorem vc23_0 : (List.range 4).all (fun c => vCheck 256 100 6 gj314 (x2Trial_314.getD (0 + c) 0) (v314.getD (0 + c) 0)) = true := by decide +kernel
theorem vok23 : ∀ c < 4, vCheck 256 (x2KeyMult 2 k23 0 * x2KeyMult 2 k23 1 * x2KeyMult 2 k23 2) (x2KeySize 2 k23) gj314 (x2Trial_314.getD c 0) (v314.getD c 0) = true := by
  intro c hc
  show vCheck 256 100 6 gj314 (x2Trial_314.getD c 0) (v314.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 100 6 gj314 (x2Trial_314.getD c 0) (v314.getD c 0)) 0 4 vc23_0 c (Nat.zero_le c) (by omega)
theorem small23 : x2KeyDegree 2 k23 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k23 0 ∧ 1 ≤ x2KeyMult 2 k23 1 ∧ 1 ≤ x2KeyMult 2 k23 2 ∧ glRowOK 2 (x2KeyTypes 2 k23 0) (x2KeyMult 2 k23 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k23 1) (x2KeyMult 2 k23 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k23 2) (x2KeyMult 2 k23 2) 512 = true ∧ gj314.length = x2KeySize 2 k23 ∧ x2KeySize 2 k23 ≤ 512 ∧ v314.length = 4 := by decide +kernel
theorem chk23 : trialKeyChk 2 k23 4 gj314 x2Trial_314 v314 :=
  trialKeyChk_intro 2 k23 4 gj314 x2Trial_314 v314 small23 gjok23 vok23
def k24 : x2Key 2 := ⟨24, by decide⟩
x2_gj_cols gj315 315 2 0 5 5 256
theorem gjc24_0 : (List.range 2).all (fun d => gjCheck 256 2 0 5 5 1 10 10 (x2JCols 315 (0 + d)) (gj315.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok24 : ∀ d < x2KeySize 2 k24, gjCheck 256 2 (x2KeyTypes 2 k24 0) (x2KeyTypes 2 k24 1) (x2KeyTypes 2 k24 2) (x2KeyMult 2 k24 0) (x2KeyMult 2 k24 1) (x2KeyMult 2 k24 2) (x2JCols (x2KeyGlobal 2 k24) d) (gj315.getD d 0) = true := by
  have hr : x2KeySize 2 k24 = 2 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 5 5 1 10 10 (x2JCols 315 d) (gj315.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 5 5 1 10 10 (x2JCols 315 d) (gj315.getD d 0)) 0 2 gjc24_0 d (Nat.zero_le d) (by omega)
x2_v_cols v315 gj315 315 256 100
theorem vc24_0 : (List.range 2).all (fun c => vCheck 256 100 2 gj315 (x2Trial_315.getD (0 + c) 0) (v315.getD (0 + c) 0)) = true := by decide +kernel
theorem vok24 : ∀ c < 2, vCheck 256 (x2KeyMult 2 k24 0 * x2KeyMult 2 k24 1 * x2KeyMult 2 k24 2) (x2KeySize 2 k24) gj315 (x2Trial_315.getD c 0) (v315.getD c 0) = true := by
  intro c hc
  show vCheck 256 100 2 gj315 (x2Trial_315.getD c 0) (v315.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 100 2 gj315 (x2Trial_315.getD c 0) (v315.getD c 0)) 0 2 vc24_0 c (Nat.zero_le c) (by omega)
theorem small24 : x2KeyDegree 2 k24 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k24 0 ∧ 1 ≤ x2KeyMult 2 k24 1 ∧ 1 ≤ x2KeyMult 2 k24 2 ∧ glRowOK 2 (x2KeyTypes 2 k24 0) (x2KeyMult 2 k24 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k24 1) (x2KeyMult 2 k24 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k24 2) (x2KeyMult 2 k24 2) 512 = true ∧ gj315.length = x2KeySize 2 k24 ∧ x2KeySize 2 k24 ≤ 512 ∧ v315.length = 2 := by decide +kernel
theorem chk24 : trialKeyChk 2 k24 2 gj315 x2Trial_315 v315 :=
  trialKeyChk_intro 2 k24 2 gj315 x2Trial_315 v315 small24 gjok24 vok24

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k23, ibFS [(v314, v314, 94810963968000)]), (k24, ibFS [(v315, v315, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 5, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN23 : N k23 = x2TrialForm 2 k23) (hN24 : N k24 = x2TrialForm 2 k24) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 5 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k23 4 _ gj314 x2Trial_314 v314 (by decide) (by rw [hN23]; exact trialForm_eq 2 k23 4 x2Trial_314 (by decide) rfl) chk23
  · exact keyOK_of_trialChk 2 N k24 2 _ gj315 x2Trial_315 v315 (by decide) (by rw [hN24]; exact trialForm_eq 2 k24 2 x2Trial_315 (by decide) rfl) chk24

end ThreeCopyQutritWerner.X2.InK2x055
