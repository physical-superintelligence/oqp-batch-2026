module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (3, 3, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x335
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k109 : x2Key 1 := ⟨109, by decide⟩
x2_gj_cols gj231 231 1 3 3 5 256
theorem gjc109_0 : (List.range 48).all (fun d => gjCheck 256 1 3 3 5 9 9 7 (x2JCols 231 (0 + d)) (gj231.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok109 : ∀ d < x2KeySize 1 k109, gjCheck 256 1 (x2KeyTypes 1 k109 0) (x2KeyTypes 1 k109 1) (x2KeyTypes 1 k109 2) (x2KeyMult 1 k109 0) (x2KeyMult 1 k109 1) (x2KeyMult 1 k109 2) (x2JCols (x2KeyGlobal 1 k109) d) (gj231.getD d 0) = true := by
  have hr : x2KeySize 1 k109 = 48 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 3 5 9 9 7 (x2JCols 231 d) (gj231.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 3 5 9 9 7 (x2JCols 231 d) (gj231.getD d 0)) 0 48 gjc109_0 d (Nat.zero_le d) (by omega)
x2_v_cols v231 gj231 231 256 567
theorem vc109_0 : (List.range 14).all (fun c => vCheck 256 567 48 gj231 (x2Trial_231.getD (0 + c) 0) (v231.getD (0 + c) 0)) = true := by decide +kernel
theorem vok109 : ∀ c < 14, vCheck 256 (x2KeyMult 1 k109 0 * x2KeyMult 1 k109 1 * x2KeyMult 1 k109 2) (x2KeySize 1 k109) gj231 (x2Trial_231.getD c 0) (v231.getD c 0) = true := by
  intro c hc
  show vCheck 256 567 48 gj231 (x2Trial_231.getD c 0) (v231.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 567 48 gj231 (x2Trial_231.getD c 0) (v231.getD c 0)) 0 14 vc109_0 c (Nat.zero_le c) (by omega)
theorem small109 : x2KeyDegree 1 k109 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k109 0 ∧ 1 ≤ x2KeyMult 1 k109 1 ∧ 1 ≤ x2KeyMult 1 k109 2 ∧ glRowOK 1 (x2KeyTypes 1 k109 0) (x2KeyMult 1 k109 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k109 1) (x2KeyMult 1 k109 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k109 2) (x2KeyMult 1 k109 2) 512 = true ∧ gj231.length = x2KeySize 1 k109 ∧ x2KeySize 1 k109 ≤ 512 ∧ v231.length = 14 := by decide +kernel
theorem chk109 : trialKeyChk 1 k109 14 gj231 x2Trial_231 v231 :=
  trialKeyChk_intro 1 k109 14 gj231 x2Trial_231 v231 small109 gjok109 vok109
def k110 : x2Key 1 := ⟨110, by decide⟩
x2_gj_cols gj232 232 1 3 3 5 256
theorem gjc110_0 : (List.range 42).all (fun d => gjCheck 256 1 3 3 5 9 9 7 (x2JCols 232 (0 + d)) (gj232.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok110 : ∀ d < x2KeySize 1 k110, gjCheck 256 1 (x2KeyTypes 1 k110 0) (x2KeyTypes 1 k110 1) (x2KeyTypes 1 k110 2) (x2KeyMult 1 k110 0) (x2KeyMult 1 k110 1) (x2KeyMult 1 k110 2) (x2JCols (x2KeyGlobal 1 k110) d) (gj232.getD d 0) = true := by
  have hr : x2KeySize 1 k110 = 42 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 3 3 5 9 9 7 (x2JCols 232 d) (gj232.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 3 3 5 9 9 7 (x2JCols 232 d) (gj232.getD d 0)) 0 42 gjc110_0 d (Nat.zero_le d) (by omega)
x2_v_cols v232 gj232 232 256 567
theorem vc110_0 : (List.range 10).all (fun c => vCheck 256 567 42 gj232 (x2Trial_232.getD (0 + c) 0) (v232.getD (0 + c) 0)) = true := by decide +kernel
theorem vok110 : ∀ c < 10, vCheck 256 (x2KeyMult 1 k110 0 * x2KeyMult 1 k110 1 * x2KeyMult 1 k110 2) (x2KeySize 1 k110) gj232 (x2Trial_232.getD c 0) (v232.getD c 0) = true := by
  intro c hc
  show vCheck 256 567 42 gj232 (x2Trial_232.getD c 0) (v232.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 567 42 gj232 (x2Trial_232.getD c 0) (v232.getD c 0)) 0 10 vc110_0 c (Nat.zero_le c) (by omega)
theorem small110 : x2KeyDegree 1 k110 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k110 0 ∧ 1 ≤ x2KeyMult 1 k110 1 ∧ 1 ≤ x2KeyMult 1 k110 2 ∧ glRowOK 1 (x2KeyTypes 1 k110 0) (x2KeyMult 1 k110 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k110 1) (x2KeyMult 1 k110 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k110 2) (x2KeyMult 1 k110 2) 512 = true ∧ gj232.length = x2KeySize 1 k110 ∧ x2KeySize 1 k110 ≤ 512 ∧ v232.length = 10 := by decide +kernel
theorem chk110 : trialKeyChk 1 k110 10 gj232 x2Trial_232 v232 :=
  trialKeyChk_intro 1 k110 10 gj232 x2Trial_232 v232 small110 gjok110 vok110

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k109, ibFS [(v231, v231, 94810963968000)]), (k110, ibFS [(v232, v232, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![3, 3, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN109 : N k109 = x2TrialForm 1 k109) (hN110 : N k110 = x2TrialForm 1 k110) :
    ∀ e ∈ ks, keyOK (x2Mult 1 3 * x2Mult 1 3 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k109 14 _ gj231 x2Trial_231 v231 (by decide) (by rw [hN109]; exact trialForm_eq 1 k109 14 x2Trial_231 (by decide) rfl) chk109
  · exact keyOK_of_trialChk 1 N k110 10 _ gj232 x2Trial_232 v232 (by decide) (by rw [hN110]; exact trialForm_eq 1 k110 10 x2Trial_232 (by decide) rfl) chk110

end ThreeCopyQutritWerner.X2.InK1x335
