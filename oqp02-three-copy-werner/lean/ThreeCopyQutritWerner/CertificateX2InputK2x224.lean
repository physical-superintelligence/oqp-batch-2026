module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 2, 4) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x224
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k64 : x2Key 2 := ⟨64, by decide⟩
x2_gj_cols gj355 355 2 2 2 4 256
theorem gjc64_0 : (List.range 18).all (fun d => gjCheck 256 2 2 2 4 5 5 15 (x2JCols 355 (0 + d)) (gj355.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok64 : ∀ d < x2KeySize 2 k64, gjCheck 256 2 (x2KeyTypes 2 k64 0) (x2KeyTypes 2 k64 1) (x2KeyTypes 2 k64 2) (x2KeyMult 2 k64 0) (x2KeyMult 2 k64 1) (x2KeyMult 2 k64 2) (x2JCols (x2KeyGlobal 2 k64) d) (gj355.getD d 0) = true := by
  have hr : x2KeySize 2 k64 = 18 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 2 4 5 5 15 (x2JCols 355 d) (gj355.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 2 4 5 5 15 (x2JCols 355 d) (gj355.getD d 0)) 0 18 gjc64_0 d (Nat.zero_le d) (by omega)
x2_v_cols v355 gj355 355 256 375
theorem vc64_0 : (List.range 12).all (fun c => vCheck 256 375 18 gj355 (x2Trial_355.getD (0 + c) 0) (v355.getD (0 + c) 0)) = true := by decide +kernel
theorem vok64 : ∀ c < 12, vCheck 256 (x2KeyMult 2 k64 0 * x2KeyMult 2 k64 1 * x2KeyMult 2 k64 2) (x2KeySize 2 k64) gj355 (x2Trial_355.getD c 0) (v355.getD c 0) = true := by
  intro c hc
  show vCheck 256 375 18 gj355 (x2Trial_355.getD c 0) (v355.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 375 18 gj355 (x2Trial_355.getD c 0) (v355.getD c 0)) 0 12 vc64_0 c (Nat.zero_le c) (by omega)
theorem small64 : x2KeyDegree 2 k64 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k64 0 ∧ 1 ≤ x2KeyMult 2 k64 1 ∧ 1 ≤ x2KeyMult 2 k64 2 ∧ glRowOK 2 (x2KeyTypes 2 k64 0) (x2KeyMult 2 k64 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k64 1) (x2KeyMult 2 k64 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k64 2) (x2KeyMult 2 k64 2) 512 = true ∧ gj355.length = x2KeySize 2 k64 ∧ x2KeySize 2 k64 ≤ 512 ∧ v355.length = 12 := by decide +kernel
theorem chk64 : trialKeyChk 2 k64 12 gj355 x2Trial_355 v355 :=
  trialKeyChk_intro 2 k64 12 gj355 x2Trial_355 v355 small64 gjok64 vok64
def k65 : x2Key 2 := ⟨65, by decide⟩
x2_gj_cols gj356 356 2 2 2 4 256
theorem gjc65_0 : (List.range 13).all (fun d => gjCheck 256 2 2 2 4 5 5 15 (x2JCols 356 (0 + d)) (gj356.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok65 : ∀ d < x2KeySize 2 k65, gjCheck 256 2 (x2KeyTypes 2 k65 0) (x2KeyTypes 2 k65 1) (x2KeyTypes 2 k65 2) (x2KeyMult 2 k65 0) (x2KeyMult 2 k65 1) (x2KeyMult 2 k65 2) (x2JCols (x2KeyGlobal 2 k65) d) (gj356.getD d 0) = true := by
  have hr : x2KeySize 2 k65 = 13 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 2 4 5 5 15 (x2JCols 356 d) (gj356.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 2 4 5 5 15 (x2JCols 356 d) (gj356.getD d 0)) 0 13 gjc65_0 d (Nat.zero_le d) (by omega)
x2_v_cols v356 gj356 356 256 375
theorem vc65_0 : (List.range 8).all (fun c => vCheck 256 375 13 gj356 (x2Trial_356.getD (0 + c) 0) (v356.getD (0 + c) 0)) = true := by decide +kernel
theorem vok65 : ∀ c < 8, vCheck 256 (x2KeyMult 2 k65 0 * x2KeyMult 2 k65 1 * x2KeyMult 2 k65 2) (x2KeySize 2 k65) gj356 (x2Trial_356.getD c 0) (v356.getD c 0) = true := by
  intro c hc
  show vCheck 256 375 13 gj356 (x2Trial_356.getD c 0) (v356.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 375 13 gj356 (x2Trial_356.getD c 0) (v356.getD c 0)) 0 8 vc65_0 c (Nat.zero_le c) (by omega)
theorem small65 : x2KeyDegree 2 k65 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k65 0 ∧ 1 ≤ x2KeyMult 2 k65 1 ∧ 1 ≤ x2KeyMult 2 k65 2 ∧ glRowOK 2 (x2KeyTypes 2 k65 0) (x2KeyMult 2 k65 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k65 1) (x2KeyMult 2 k65 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k65 2) (x2KeyMult 2 k65 2) 512 = true ∧ gj356.length = x2KeySize 2 k65 ∧ x2KeySize 2 k65 ≤ 512 ∧ v356.length = 8 := by decide +kernel
theorem chk65 : trialKeyChk 2 k65 8 gj356 x2Trial_356 v356 :=
  trialKeyChk_intro 2 k65 8 gj356 x2Trial_356 v356 small65 gjok65 vok65

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k64, ibFS [(v355, v355, 94810963968000)]), (k65, ibFS [(v356, v356, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 2, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN64 : N k64 = x2TrialForm 2 k64) (hN65 : N k65 = x2TrialForm 2 k65) :
    ∀ e ∈ ks, keyOK (x2Mult 2 2 * x2Mult 2 2 * x2Mult 2 4) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k64 12 _ gj355 x2Trial_355 v355 (by decide) (by rw [hN64]; exact trialForm_eq 2 k64 12 x2Trial_355 (by decide) rfl) chk64
  · exact keyOK_of_trialChk 2 N k65 8 _ gj356 x2Trial_356 v356 (by decide) (by rw [hN65]; exact trialForm_eq 2 k65 8 x2Trial_356 (by decide) rfl) chk65

end ThreeCopyQutritWerner.X2.InK2x224
