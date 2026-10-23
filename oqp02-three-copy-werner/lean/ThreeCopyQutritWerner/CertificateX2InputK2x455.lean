module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 5, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x455
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k108 : x2Key 2 := ⟨108, by decide⟩
x2_gj_cols gj399 399 2 4 5 5 256
theorem gjc108_0 : (List.range 67).all (fun d => gjCheck 256 2 4 5 5 15 10 10 (x2JCols 399 (0 + d)) (gj399.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok108 : ∀ d < x2KeySize 2 k108, gjCheck 256 2 (x2KeyTypes 2 k108 0) (x2KeyTypes 2 k108 1) (x2KeyTypes 2 k108 2) (x2KeyMult 2 k108 0) (x2KeyMult 2 k108 1) (x2KeyMult 2 k108 2) (x2JCols (x2KeyGlobal 2 k108) d) (gj399.getD d 0) = true := by
  have hr : x2KeySize 2 k108 = 67 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 4 5 5 15 10 10 (x2JCols 399 d) (gj399.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 4 5 5 15 10 10 (x2JCols 399 d) (gj399.getD d 0)) 0 67 gjc108_0 d (Nat.zero_le d) (by omega)
x2_v_cols v399 gj399 399 256 1500
theorem vc108_0 : (List.range 59).all (fun c => vCheck 256 1500 67 gj399 (x2Trial_399.getD (0 + c) 0) (v399.getD (0 + c) 0)) = true := by decide +kernel
theorem vok108 : ∀ c < 59, vCheck 256 (x2KeyMult 2 k108 0 * x2KeyMult 2 k108 1 * x2KeyMult 2 k108 2) (x2KeySize 2 k108) gj399 (x2Trial_399.getD c 0) (v399.getD c 0) = true := by
  intro c hc
  show vCheck 256 1500 67 gj399 (x2Trial_399.getD c 0) (v399.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1500 67 gj399 (x2Trial_399.getD c 0) (v399.getD c 0)) 0 59 vc108_0 c (Nat.zero_le c) (by omega)
theorem small108 : x2KeyDegree 2 k108 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k108 0 ∧ 1 ≤ x2KeyMult 2 k108 1 ∧ 1 ≤ x2KeyMult 2 k108 2 ∧ glRowOK 2 (x2KeyTypes 2 k108 0) (x2KeyMult 2 k108 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k108 1) (x2KeyMult 2 k108 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k108 2) (x2KeyMult 2 k108 2) 512 = true ∧ gj399.length = x2KeySize 2 k108 ∧ x2KeySize 2 k108 ≤ 512 ∧ v399.length = 59 := by decide +kernel
theorem chk108 : trialKeyChk 2 k108 59 gj399 x2Trial_399 v399 :=
  trialKeyChk_intro 2 k108 59 gj399 x2Trial_399 v399 small108 gjok108 vok108
def k109 : x2Key 2 := ⟨109, by decide⟩
x2_gj_cols gj400 400 2 4 5 5 256
theorem gjc109_0 : (List.range 57).all (fun d => gjCheck 256 2 4 5 5 15 10 10 (x2JCols 400 (0 + d)) (gj400.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok109 : ∀ d < x2KeySize 2 k109, gjCheck 256 2 (x2KeyTypes 2 k109 0) (x2KeyTypes 2 k109 1) (x2KeyTypes 2 k109 2) (x2KeyMult 2 k109 0) (x2KeyMult 2 k109 1) (x2KeyMult 2 k109 2) (x2JCols (x2KeyGlobal 2 k109) d) (gj400.getD d 0) = true := by
  have hr : x2KeySize 2 k109 = 57 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 4 5 5 15 10 10 (x2JCols 400 d) (gj400.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 4 5 5 15 10 10 (x2JCols 400 d) (gj400.getD d 0)) 0 57 gjc109_0 d (Nat.zero_le d) (by omega)
x2_v_cols v400 gj400 400 256 1500
theorem vc109_0 : (List.range 49).all (fun c => vCheck 256 1500 57 gj400 (x2Trial_400.getD (0 + c) 0) (v400.getD (0 + c) 0)) = true := by decide +kernel
theorem vok109 : ∀ c < 49, vCheck 256 (x2KeyMult 2 k109 0 * x2KeyMult 2 k109 1 * x2KeyMult 2 k109 2) (x2KeySize 2 k109) gj400 (x2Trial_400.getD c 0) (v400.getD c 0) = true := by
  intro c hc
  show vCheck 256 1500 57 gj400 (x2Trial_400.getD c 0) (v400.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1500 57 gj400 (x2Trial_400.getD c 0) (v400.getD c 0)) 0 49 vc109_0 c (Nat.zero_le c) (by omega)
theorem small109 : x2KeyDegree 2 k109 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k109 0 ∧ 1 ≤ x2KeyMult 2 k109 1 ∧ 1 ≤ x2KeyMult 2 k109 2 ∧ glRowOK 2 (x2KeyTypes 2 k109 0) (x2KeyMult 2 k109 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k109 1) (x2KeyMult 2 k109 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k109 2) (x2KeyMult 2 k109 2) 512 = true ∧ gj400.length = x2KeySize 2 k109 ∧ x2KeySize 2 k109 ≤ 512 ∧ v400.length = 49 := by decide +kernel
theorem chk109 : trialKeyChk 2 k109 49 gj400 x2Trial_400 v400 :=
  trialKeyChk_intro 2 k109 49 gj400 x2Trial_400 v400 small109 gjok109 vok109

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k108, ibFS [(v399, v399, 94810963968000)]), (k109, ibFS [(v400, v400, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![4, 5, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN108 : N k108 = x2TrialForm 2 k108) (hN109 : N k109 = x2TrialForm 2 k109) :
    ∀ e ∈ ks, keyOK (x2Mult 2 4 * x2Mult 2 5 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k108 59 _ gj399 x2Trial_399 v399 (by decide) (by rw [hN108]; exact trialForm_eq 2 k108 59 x2Trial_399 (by decide) rfl) chk108
  · exact keyOK_of_trialChk 2 N k109 49 _ gj400 x2Trial_400 v400 (by decide) (by rw [hN109]; exact trialForm_eq 2 k109 49 x2Trial_400 (by decide) rfl) chk109

end ThreeCopyQutritWerner.X2.InK2x455
