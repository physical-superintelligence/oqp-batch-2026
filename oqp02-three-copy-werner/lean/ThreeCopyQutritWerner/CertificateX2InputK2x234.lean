module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 3, 4) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x234
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k72 : x2Key 2 := ⟨72, by decide⟩
x2_gj_cols gj363 363 2 2 3 4 256
theorem gjc72_0 : (List.range 31).all (fun d => gjCheck 256 2 2 3 4 5 5 15 (x2JCols 363 (0 + d)) (gj363.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok72 : ∀ d < x2KeySize 2 k72, gjCheck 256 2 (x2KeyTypes 2 k72 0) (x2KeyTypes 2 k72 1) (x2KeyTypes 2 k72 2) (x2KeyMult 2 k72 0) (x2KeyMult 2 k72 1) (x2KeyMult 2 k72 2) (x2JCols (x2KeyGlobal 2 k72) d) (gj363.getD d 0) = true := by
  have hr : x2KeySize 2 k72 = 31 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 2 3 4 5 5 15 (x2JCols 363 d) (gj363.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 2 3 4 5 5 15 (x2JCols 363 d) (gj363.getD d 0)) 0 31 gjc72_0 d (Nat.zero_le d) (by omega)
x2_v_cols v363 gj363 363 256 375
theorem vc72_0 : (List.range 11).all (fun c => vCheck 256 375 31 gj363 (x2Trial_363.getD (0 + c) 0) (v363.getD (0 + c) 0)) = true := by decide +kernel
theorem vok72 : ∀ c < 11, vCheck 256 (x2KeyMult 2 k72 0 * x2KeyMult 2 k72 1 * x2KeyMult 2 k72 2) (x2KeySize 2 k72) gj363 (x2Trial_363.getD c 0) (v363.getD c 0) = true := by
  intro c hc
  show vCheck 256 375 31 gj363 (x2Trial_363.getD c 0) (v363.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 375 31 gj363 (x2Trial_363.getD c 0) (v363.getD c 0)) 0 11 vc72_0 c (Nat.zero_le c) (by omega)
theorem small72 : x2KeyDegree 2 k72 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k72 0 ∧ 1 ≤ x2KeyMult 2 k72 1 ∧ 1 ≤ x2KeyMult 2 k72 2 ∧ glRowOK 2 (x2KeyTypes 2 k72 0) (x2KeyMult 2 k72 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k72 1) (x2KeyMult 2 k72 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k72 2) (x2KeyMult 2 k72 2) 512 = true ∧ gj363.length = x2KeySize 2 k72 ∧ x2KeySize 2 k72 ≤ 512 ∧ v363.length = 11 := by decide +kernel
theorem chk72 : trialKeyChk 2 k72 11 gj363 x2Trial_363 v363 :=
  trialKeyChk_intro 2 k72 11 gj363 x2Trial_363 v363 small72 gjok72 vok72

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k72, ibFS [(v363, v363, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![2, 3, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN72 : N k72 = x2TrialForm 2 k72) :
    ∀ e ∈ ks, keyOK (x2Mult 2 2 * x2Mult 2 3 * x2Mult 2 4) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k72 11 _ gj363 x2Trial_363 v363 (by decide) (by rw [hN72]; exact trialForm_eq 2 k72 11 x2Trial_363 (by decide) rfl) chk72

end ThreeCopyQutritWerner.X2.InK2x234
