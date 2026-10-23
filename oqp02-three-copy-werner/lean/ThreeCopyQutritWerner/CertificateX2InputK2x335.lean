module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 3, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x335
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k88 : x2Key 2 := ⟨88, by decide⟩
x2_gj_cols gj379 379 2 3 3 5 256
theorem gjc88_0 : (List.range 14).all (fun d => gjCheck 256 2 3 3 5 5 5 10 (x2JCols 379 (0 + d)) (gj379.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok88 : ∀ d < x2KeySize 2 k88, gjCheck 256 2 (x2KeyTypes 2 k88 0) (x2KeyTypes 2 k88 1) (x2KeyTypes 2 k88 2) (x2KeyMult 2 k88 0) (x2KeyMult 2 k88 1) (x2KeyMult 2 k88 2) (x2JCols (x2KeyGlobal 2 k88) d) (gj379.getD d 0) = true := by
  have hr : x2KeySize 2 k88 = 14 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 3 5 5 5 10 (x2JCols 379 d) (gj379.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 3 5 5 5 10 (x2JCols 379 d) (gj379.getD d 0)) 0 14 gjc88_0 d (Nat.zero_le d) (by omega)
x2_v_cols v379 gj379 379 256 250
theorem vc88_0 : (List.range 6).all (fun c => vCheck 256 250 14 gj379 (x2Trial_379.getD (0 + c) 0) (v379.getD (0 + c) 0)) = true := by decide +kernel
theorem vok88 : ∀ c < 6, vCheck 256 (x2KeyMult 2 k88 0 * x2KeyMult 2 k88 1 * x2KeyMult 2 k88 2) (x2KeySize 2 k88) gj379 (x2Trial_379.getD c 0) (v379.getD c 0) = true := by
  intro c hc
  show vCheck 256 250 14 gj379 (x2Trial_379.getD c 0) (v379.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 250 14 gj379 (x2Trial_379.getD c 0) (v379.getD c 0)) 0 6 vc88_0 c (Nat.zero_le c) (by omega)
theorem small88 : x2KeyDegree 2 k88 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k88 0 ∧ 1 ≤ x2KeyMult 2 k88 1 ∧ 1 ≤ x2KeyMult 2 k88 2 ∧ glRowOK 2 (x2KeyTypes 2 k88 0) (x2KeyMult 2 k88 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k88 1) (x2KeyMult 2 k88 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k88 2) (x2KeyMult 2 k88 2) 512 = true ∧ gj379.length = x2KeySize 2 k88 ∧ x2KeySize 2 k88 ≤ 512 ∧ v379.length = 6 := by decide +kernel
theorem chk88 : trialKeyChk 2 k88 6 gj379 x2Trial_379 v379 :=
  trialKeyChk_intro 2 k88 6 gj379 x2Trial_379 v379 small88 gjok88 vok88
def k89 : x2Key 2 := ⟨89, by decide⟩
x2_gj_cols gj380 380 2 3 3 5 256
theorem gjc89_0 : (List.range 8).all (fun d => gjCheck 256 2 3 3 5 5 5 10 (x2JCols 380 (0 + d)) (gj380.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok89 : ∀ d < x2KeySize 2 k89, gjCheck 256 2 (x2KeyTypes 2 k89 0) (x2KeyTypes 2 k89 1) (x2KeyTypes 2 k89 2) (x2KeyMult 2 k89 0) (x2KeyMult 2 k89 1) (x2KeyMult 2 k89 2) (x2JCols (x2KeyGlobal 2 k89) d) (gj380.getD d 0) = true := by
  have hr : x2KeySize 2 k89 = 8 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 3 3 5 5 5 10 (x2JCols 380 d) (gj380.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 3 3 5 5 5 10 (x2JCols 380 d) (gj380.getD d 0)) 0 8 gjc89_0 d (Nat.zero_le d) (by omega)
x2_v_cols v380 gj380 380 256 250
theorem vc89_0 : (List.range 3).all (fun c => vCheck 256 250 8 gj380 (x2Trial_380.getD (0 + c) 0) (v380.getD (0 + c) 0)) = true := by decide +kernel
theorem vok89 : ∀ c < 3, vCheck 256 (x2KeyMult 2 k89 0 * x2KeyMult 2 k89 1 * x2KeyMult 2 k89 2) (x2KeySize 2 k89) gj380 (x2Trial_380.getD c 0) (v380.getD c 0) = true := by
  intro c hc
  show vCheck 256 250 8 gj380 (x2Trial_380.getD c 0) (v380.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 250 8 gj380 (x2Trial_380.getD c 0) (v380.getD c 0)) 0 3 vc89_0 c (Nat.zero_le c) (by omega)
theorem small89 : x2KeyDegree 2 k89 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k89 0 ∧ 1 ≤ x2KeyMult 2 k89 1 ∧ 1 ≤ x2KeyMult 2 k89 2 ∧ glRowOK 2 (x2KeyTypes 2 k89 0) (x2KeyMult 2 k89 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k89 1) (x2KeyMult 2 k89 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k89 2) (x2KeyMult 2 k89 2) 512 = true ∧ gj380.length = x2KeySize 2 k89 ∧ x2KeySize 2 k89 ≤ 512 ∧ v380.length = 3 := by decide +kernel
theorem chk89 : trialKeyChk 2 k89 3 gj380 x2Trial_380 v380 :=
  trialKeyChk_intro 2 k89 3 gj380 x2Trial_380 v380 small89 gjok89 vok89

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k88, ibFS [(v379, v379, 94810963968000)]), (k89, ibFS [(v380, v380, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![3, 3, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN88 : N k88 = x2TrialForm 2 k88) (hN89 : N k89 = x2TrialForm 2 k89) :
    ∀ e ∈ ks, keyOK (x2Mult 2 3 * x2Mult 2 3 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k88 6 _ gj379 x2Trial_379 v379 (by decide) (by rw [hN88]; exact trialForm_eq 2 k88 6 x2Trial_379 (by decide) rfl) chk88
  · exact keyOK_of_trialChk 2 N k89 3 _ gj380 x2Trial_380 v380 (by decide) (by rw [hN89]; exact trialForm_eq 2 k89 3 x2Trial_380 (by decide) rfl) chk89

end ThreeCopyQutritWerner.X2.InK2x335
