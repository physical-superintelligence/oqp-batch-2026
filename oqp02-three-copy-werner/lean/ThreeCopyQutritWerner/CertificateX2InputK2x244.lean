module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 4, 4) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x244
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k75 : x2Key 2 := ⟨75, by decide⟩
x2_gj_cols gj366 366 2 2 4 4 256
theorem gjc75_0 : (List.range 52).all (fun d => gjCheck 256 2 2 4 4 5 15 15 (x2JCols 366 (0 + d)) (gj366.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok75 : ∀ d < x2KeySize 2 k75, gjCheck 256 2 (x2KeyTypes 2 k75 0) (x2KeyTypes 2 k75 1) (x2KeyTypes 2 k75 2) (x2KeyMult 2 k75 0) (x2KeyMult 2 k75 1) (x2KeyMult 2 k75 2) (x2JCols (x2KeyGlobal 2 k75) d) (gj366.getD d 0) = true := by
  have hr : x2KeySize 2 k75 = 52 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 4 4 5 15 15 (x2JCols 366 d) (gj366.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 4 4 5 15 15 (x2JCols 366 d) (gj366.getD d 0)) 0 52 gjc75_0 d (Nat.zero_le d) (by omega)
x2_v_cols v366 gj366 366 256 1125
theorem vc75_0 : (List.range 41).all (fun c => vCheck 256 1125 52 gj366 (x2Trial_366.getD (0 + c) 0) (v366.getD (0 + c) 0)) = true := by decide +kernel
theorem vok75 : ∀ c < 41, vCheck 256 (x2KeyMult 2 k75 0 * x2KeyMult 2 k75 1 * x2KeyMult 2 k75 2) (x2KeySize 2 k75) gj366 (x2Trial_366.getD c 0) (v366.getD c 0) = true := by
  intro c hc
  show vCheck 256 1125 52 gj366 (x2Trial_366.getD c 0) (v366.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1125 52 gj366 (x2Trial_366.getD c 0) (v366.getD c 0)) 0 41 vc75_0 c (Nat.zero_le c) (by omega)
theorem small75 : x2KeyDegree 2 k75 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k75 0 ∧ 1 ≤ x2KeyMult 2 k75 1 ∧ 1 ≤ x2KeyMult 2 k75 2 ∧ glRowOK 2 (x2KeyTypes 2 k75 0) (x2KeyMult 2 k75 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k75 1) (x2KeyMult 2 k75 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k75 2) (x2KeyMult 2 k75 2) 512 = true ∧ gj366.length = x2KeySize 2 k75 ∧ x2KeySize 2 k75 ≤ 512 ∧ v366.length = 41 := by decide +kernel
theorem chk75 : trialKeyChk 2 k75 41 gj366 x2Trial_366 v366 :=
  trialKeyChk_intro 2 k75 41 gj366 x2Trial_366 v366 small75 gjok75 vok75
def k76 : x2Key 2 := ⟨76, by decide⟩
x2_gj_cols gj367 367 2 2 4 4 256
theorem gjc76_0 : (List.range 42).all (fun d => gjCheck 256 2 2 4 4 5 15 15 (x2JCols 367 (0 + d)) (gj367.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok76 : ∀ d < x2KeySize 2 k76, gjCheck 256 2 (x2KeyTypes 2 k76 0) (x2KeyTypes 2 k76 1) (x2KeyTypes 2 k76 2) (x2KeyMult 2 k76 0) (x2KeyMult 2 k76 1) (x2KeyMult 2 k76 2) (x2JCols (x2KeyGlobal 2 k76) d) (gj367.getD d 0) = true := by
  have hr : x2KeySize 2 k76 = 42 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 4 4 5 15 15 (x2JCols 367 d) (gj367.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 4 4 5 15 15 (x2JCols 367 d) (gj367.getD d 0)) 0 42 gjc76_0 d (Nat.zero_le d) (by omega)
x2_v_cols v367 gj367 367 256 1125
theorem vc76_0 : (List.range 34).all (fun c => vCheck 256 1125 42 gj367 (x2Trial_367.getD (0 + c) 0) (v367.getD (0 + c) 0)) = true := by decide +kernel
theorem vok76 : ∀ c < 34, vCheck 256 (x2KeyMult 2 k76 0 * x2KeyMult 2 k76 1 * x2KeyMult 2 k76 2) (x2KeySize 2 k76) gj367 (x2Trial_367.getD c 0) (v367.getD c 0) = true := by
  intro c hc
  show vCheck 256 1125 42 gj367 (x2Trial_367.getD c 0) (v367.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 1125 42 gj367 (x2Trial_367.getD c 0) (v367.getD c 0)) 0 34 vc76_0 c (Nat.zero_le c) (by omega)
theorem small76 : x2KeyDegree 2 k76 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k76 0 ∧ 1 ≤ x2KeyMult 2 k76 1 ∧ 1 ≤ x2KeyMult 2 k76 2 ∧ glRowOK 2 (x2KeyTypes 2 k76 0) (x2KeyMult 2 k76 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k76 1) (x2KeyMult 2 k76 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k76 2) (x2KeyMult 2 k76 2) 512 = true ∧ gj367.length = x2KeySize 2 k76 ∧ x2KeySize 2 k76 ≤ 512 ∧ v367.length = 34 := by decide +kernel
theorem chk76 : trialKeyChk 2 k76 34 gj367 x2Trial_367 v367 :=
  trialKeyChk_intro 2 k76 34 gj367 x2Trial_367 v367 small76 gjok76 vok76

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k75, ibFS [(v366, v366, 94810963968000)]), (k76, ibFS [(v367, v367, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 4, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN75 : N k75 = x2TrialForm 2 k75) (hN76 : N k76 = x2TrialForm 2 k76) :
    ∀ e ∈ ks, keyOK (x2Mult 2 2 * x2Mult 2 4 * x2Mult 2 4) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k75 41 _ gj366 x2Trial_366 v366 (by decide) (by rw [hN75]; exact trialForm_eq 2 k75 41 x2Trial_366 (by decide) rfl) chk75
  · exact keyOK_of_trialChk 2 N k76 34 _ gj367 x2Trial_367 v367 (by decide) (by rw [hN76]; exact trialForm_eq 2 k76 34 x2Trial_367 (by decide) rfl) chk76

end ThreeCopyQutritWerner.X2.InK2x244
