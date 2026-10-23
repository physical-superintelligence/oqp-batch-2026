module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 2, 2) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x222
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k60 : x2Key 2 := ⟨60, by decide⟩
x2_gj_cols gj351 351 2 2 2 2 256
theorem gjc60_0 : (List.range 2).all (fun d => gjCheck 256 2 2 2 2 5 5 5 (x2JCols 351 (0 + d)) (gj351.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok60 : ∀ d < x2KeySize 2 k60, gjCheck 256 2 (x2KeyTypes 2 k60 0) (x2KeyTypes 2 k60 1) (x2KeyTypes 2 k60 2) (x2KeyMult 2 k60 0) (x2KeyMult 2 k60 1) (x2KeyMult 2 k60 2) (x2JCols (x2KeyGlobal 2 k60) d) (gj351.getD d 0) = true := by
  have hr : x2KeySize 2 k60 = 2 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 2 2 5 5 5 (x2JCols 351 d) (gj351.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 2 2 5 5 5 (x2JCols 351 d) (gj351.getD d 0)) 0 2 gjc60_0 d (Nat.zero_le d) (by omega)
x2_v_cols v351 gj351 351 256 125
theorem vc60_0 : (List.range 1).all (fun c => vCheck 256 125 2 gj351 (x2Trial_351.getD (0 + c) 0) (v351.getD (0 + c) 0)) = true := by decide +kernel
theorem vok60 : ∀ c < 1, vCheck 256 (x2KeyMult 2 k60 0 * x2KeyMult 2 k60 1 * x2KeyMult 2 k60 2) (x2KeySize 2 k60) gj351 (x2Trial_351.getD c 0) (v351.getD c 0) = true := by
  intro c hc
  show vCheck 256 125 2 gj351 (x2Trial_351.getD c 0) (v351.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 125 2 gj351 (x2Trial_351.getD c 0) (v351.getD c 0)) 0 1 vc60_0 c (Nat.zero_le c) (by omega)
theorem small60 : x2KeyDegree 2 k60 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k60 0 ∧ 1 ≤ x2KeyMult 2 k60 1 ∧ 1 ≤ x2KeyMult 2 k60 2 ∧ glRowOK 2 (x2KeyTypes 2 k60 0) (x2KeyMult 2 k60 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k60 1) (x2KeyMult 2 k60 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k60 2) (x2KeyMult 2 k60 2) 512 = true ∧ gj351.length = x2KeySize 2 k60 ∧ x2KeySize 2 k60 ≤ 512 ∧ v351.length = 1 := by decide +kernel
theorem chk60 : trialKeyChk 2 k60 1 gj351 x2Trial_351 v351 :=
  trialKeyChk_intro 2 k60 1 gj351 x2Trial_351 v351 small60 gjok60 vok60
def k61 : x2Key 2 := ⟨61, by decide⟩
x2_gj_cols gj352 352 2 2 2 2 256
theorem gjc61_0 : (List.range 3).all (fun d => gjCheck 256 2 2 2 2 5 5 5 (x2JCols 352 (0 + d)) (gj352.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok61 : ∀ d < x2KeySize 2 k61, gjCheck 256 2 (x2KeyTypes 2 k61 0) (x2KeyTypes 2 k61 1) (x2KeyTypes 2 k61 2) (x2KeyMult 2 k61 0) (x2KeyMult 2 k61 1) (x2KeyMult 2 k61 2) (x2JCols (x2KeyGlobal 2 k61) d) (gj352.getD d 0) = true := by
  have hr : x2KeySize 2 k61 = 3 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 2 2 5 5 5 (x2JCols 352 d) (gj352.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 2 2 5 5 5 (x2JCols 352 d) (gj352.getD d 0)) 0 3 gjc61_0 d (Nat.zero_le d) (by omega)
x2_v_cols v352 gj352 352 256 125
theorem vc61_0 : (List.range 2).all (fun c => vCheck 256 125 3 gj352 (x2Trial_352.getD (0 + c) 0) (v352.getD (0 + c) 0)) = true := by decide +kernel
theorem vok61 : ∀ c < 2, vCheck 256 (x2KeyMult 2 k61 0 * x2KeyMult 2 k61 1 * x2KeyMult 2 k61 2) (x2KeySize 2 k61) gj352 (x2Trial_352.getD c 0) (v352.getD c 0) = true := by
  intro c hc
  show vCheck 256 125 3 gj352 (x2Trial_352.getD c 0) (v352.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 125 3 gj352 (x2Trial_352.getD c 0) (v352.getD c 0)) 0 2 vc61_0 c (Nat.zero_le c) (by omega)
x2_p_cols p352 v352 5
theorem pok61 : ∀ c < 2, partnerCheck (x2KeyMult 2 k61 0) (v352.getD c 0) (p352.getD c 0) = true := by
  intro c hc
  show partnerCheck 5 (v352.getD c 0) (p352.getD c 0) = true
  have h : (List.range 2).all (fun c => partnerCheck 5 (v352.getD c 0) (p352.getD c 0)) = true := by
    decide +kernel
  exact List.all_eq_true.mp h c (List.mem_range.mpr hc)
theorem small61 : x2KeyDegree 2 k61 = 2 ∧ x2KeyMult 2 k61 0 = x2KeyMult 2 k61 1 ∧ x2KeyMult 2 k61 1 = x2KeyMult 2 k61 2 ∧ 1 ≤ x2KeyMult 2 k61 0 ∧ glRowOK 2 (x2KeyTypes 2 k61 0) (x2KeyMult 2 k61 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k61 1) (x2KeyMult 2 k61 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k61 2) (x2KeyMult 2 k61 2) 512 = true ∧ gj352.length = x2KeySize 2 k61 ∧ x2KeySize 2 k61 ≤ 512 ∧ v352.length = 2 ∧ p352.length = 2 := by decide +kernel
theorem chk61 : trial2KeyChk 2 k61 2 gj352 x2Trial_352 v352 p352 :=
  trial2KeyChk_intro 2 k61 2 gj352 x2Trial_352 v352 p352 small61 gjok61 vok61 pok61

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k60, ibFS [(v351, v351, 94810963968000)]), (k61, ibFS [(v352, v352, 94810963968000), (p352, p352, 31603654656000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 2, 2] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN60 : N k60 = x2TrialForm 2 k60) (hN61 : N k61 = x2TrialForm 2 k61) :
    ∀ e ∈ ks, keyOK (x2Mult 2 2 * x2Mult 2 2 * x2Mult 2 2) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k60 1 _ gj351 x2Trial_351 v351 (by decide) (by rw [hN60]; exact trialForm_eq 2 k60 1 x2Trial_351 (by decide) rfl) chk60
  · exact keyOK_of_trial2Chk 2 N k61 2 _ gj352 x2Trial_352 v352 p352 (by decide) (by rw [hN61]; exact trialForm_eq 2 k61 2 x2Trial_352 (by decide) rfl) chk61

end ThreeCopyQutritWerner.X2.InK2x222
