module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (5, 7, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x577
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k157 : x2Key 1 := ⟨157, by decide⟩
x2_gj_cols gj279 279 1 5 7 7 256
theorem gjc157_0 : (List.range 23).all (fun d => gjCheck 256 1 5 7 7 7 6 6 (x2JCols 279 (0 + d)) (gj279.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok157 : ∀ d < x2KeySize 1 k157, gjCheck 256 1 (x2KeyTypes 1 k157 0) (x2KeyTypes 1 k157 1) (x2KeyTypes 1 k157 2) (x2KeyMult 1 k157 0) (x2KeyMult 1 k157 1) (x2KeyMult 1 k157 2) (x2JCols (x2KeyGlobal 1 k157) d) (gj279.getD d 0) = true := by
  have hr : x2KeySize 1 k157 = 23 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 5 7 7 7 6 6 (x2JCols 279 d) (gj279.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 5 7 7 7 6 6 (x2JCols 279 d) (gj279.getD d 0)) 0 23 gjc157_0 d (Nat.zero_le d) (by omega)
x2_v_cols v279 gj279 279 256 252
theorem vc157_0 : (List.range 16).all (fun c => vCheck 256 252 23 gj279 (x2Trial_279.getD (0 + c) 0) (v279.getD (0 + c) 0)) = true := by decide +kernel
theorem vok157 : ∀ c < 16, vCheck 256 (x2KeyMult 1 k157 0 * x2KeyMult 1 k157 1 * x2KeyMult 1 k157 2) (x2KeySize 1 k157) gj279 (x2Trial_279.getD c 0) (v279.getD c 0) = true := by
  intro c hc
  show vCheck 256 252 23 gj279 (x2Trial_279.getD c 0) (v279.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 252 23 gj279 (x2Trial_279.getD c 0) (v279.getD c 0)) 0 16 vc157_0 c (Nat.zero_le c) (by omega)
theorem small157 : x2KeyDegree 1 k157 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k157 0 ∧ 1 ≤ x2KeyMult 1 k157 1 ∧ 1 ≤ x2KeyMult 1 k157 2 ∧ glRowOK 1 (x2KeyTypes 1 k157 0) (x2KeyMult 1 k157 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k157 1) (x2KeyMult 1 k157 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k157 2) (x2KeyMult 1 k157 2) 512 = true ∧ gj279.length = x2KeySize 1 k157 ∧ x2KeySize 1 k157 ≤ 512 ∧ v279.length = 16 := by decide +kernel
theorem chk157 : trialKeyChk 1 k157 16 gj279 x2Trial_279 v279 :=
  trialKeyChk_intro 1 k157 16 gj279 x2Trial_279 v279 small157 gjok157 vok157
def k158 : x2Key 1 := ⟨158, by decide⟩
x2_gj_cols gj280 280 1 5 7 7 256
theorem gjc158_0 : (List.range 19).all (fun d => gjCheck 256 1 5 7 7 7 6 6 (x2JCols 280 (0 + d)) (gj280.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok158 : ∀ d < x2KeySize 1 k158, gjCheck 256 1 (x2KeyTypes 1 k158 0) (x2KeyTypes 1 k158 1) (x2KeyTypes 1 k158 2) (x2KeyMult 1 k158 0) (x2KeyMult 1 k158 1) (x2KeyMult 1 k158 2) (x2JCols (x2KeyGlobal 1 k158) d) (gj280.getD d 0) = true := by
  have hr : x2KeySize 1 k158 = 19 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 5 7 7 7 6 6 (x2JCols 280 d) (gj280.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 5 7 7 7 6 6 (x2JCols 280 d) (gj280.getD d 0)) 0 19 gjc158_0 d (Nat.zero_le d) (by omega)
x2_v_cols v280 gj280 280 256 252
theorem vc158_0 : (List.range 12).all (fun c => vCheck 256 252 19 gj280 (x2Trial_280.getD (0 + c) 0) (v280.getD (0 + c) 0)) = true := by decide +kernel
theorem vok158 : ∀ c < 12, vCheck 256 (x2KeyMult 1 k158 0 * x2KeyMult 1 k158 1 * x2KeyMult 1 k158 2) (x2KeySize 1 k158) gj280 (x2Trial_280.getD c 0) (v280.getD c 0) = true := by
  intro c hc
  show vCheck 256 252 19 gj280 (x2Trial_280.getD c 0) (v280.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 252 19 gj280 (x2Trial_280.getD c 0) (v280.getD c 0)) 0 12 vc158_0 c (Nat.zero_le c) (by omega)
theorem small158 : x2KeyDegree 1 k158 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k158 0 ∧ 1 ≤ x2KeyMult 1 k158 1 ∧ 1 ≤ x2KeyMult 1 k158 2 ∧ glRowOK 1 (x2KeyTypes 1 k158 0) (x2KeyMult 1 k158 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k158 1) (x2KeyMult 1 k158 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k158 2) (x2KeyMult 1 k158 2) 512 = true ∧ gj280.length = x2KeySize 1 k158 ∧ x2KeySize 1 k158 ≤ 512 ∧ v280.length = 12 := by decide +kernel
theorem chk158 : trialKeyChk 1 k158 12 gj280 x2Trial_280 v280 :=
  trialKeyChk_intro 1 k158 12 gj280 x2Trial_280 v280 small158 gjok158 vok158

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k157, ibFS [(v279, v279, 94810963968000)]), (k158, ibFS [(v280, v280, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![5, 7, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN157 : N k157 = x2TrialForm 1 k157) (hN158 : N k158 = x2TrialForm 1 k158) :
    ∀ e ∈ ks, keyOK (x2Mult 1 5 * x2Mult 1 7 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k157 16 _ gj279 x2Trial_279 v279 (by decide) (by rw [hN157]; exact trialForm_eq 1 k157 16 x2Trial_279 (by decide) rfl) chk157
  · exact keyOK_of_trialChk 1 N k158 12 _ gj280 x2Trial_280 v280 (by decide) (by rw [hN158]; exact trialForm_eq 1 k158 12 x2Trial_280 (by decide) rfl) chk158

end ThreeCopyQutritWerner.X2.InK1x577
