module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 1, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x115
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k36 : x2Key 2 := ⟨36, by decide⟩
x2_gj_cols gj327 327 2 1 1 5 256
theorem gjc36_0 : (List.range 10).all (fun d => gjCheck 256 2 1 1 5 4 4 10 (x2JCols 327 (0 + d)) (gj327.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok36 : ∀ d < x2KeySize 2 k36, gjCheck 256 2 (x2KeyTypes 2 k36 0) (x2KeyTypes 2 k36 1) (x2KeyTypes 2 k36 2) (x2KeyMult 2 k36 0) (x2KeyMult 2 k36 1) (x2KeyMult 2 k36 2) (x2JCols (x2KeyGlobal 2 k36) d) (gj327.getD d 0) = true := by
  have hr : x2KeySize 2 k36 = 10 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 1 5 4 4 10 (x2JCols 327 d) (gj327.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 1 5 4 4 10 (x2JCols 327 d) (gj327.getD d 0)) 0 10 gjc36_0 d (Nat.zero_le d) (by omega)
x2_v_cols v327 gj327 327 256 160
theorem vc36_0 : (List.range 5).all (fun c => vCheck 256 160 10 gj327 (x2Trial_327.getD (0 + c) 0) (v327.getD (0 + c) 0)) = true := by decide +kernel
theorem vok36 : ∀ c < 5, vCheck 256 (x2KeyMult 2 k36 0 * x2KeyMult 2 k36 1 * x2KeyMult 2 k36 2) (x2KeySize 2 k36) gj327 (x2Trial_327.getD c 0) (v327.getD c 0) = true := by
  intro c hc
  show vCheck 256 160 10 gj327 (x2Trial_327.getD c 0) (v327.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 160 10 gj327 (x2Trial_327.getD c 0) (v327.getD c 0)) 0 5 vc36_0 c (Nat.zero_le c) (by omega)
theorem small36 : x2KeyDegree 2 k36 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k36 0 ∧ 1 ≤ x2KeyMult 2 k36 1 ∧ 1 ≤ x2KeyMult 2 k36 2 ∧ glRowOK 2 (x2KeyTypes 2 k36 0) (x2KeyMult 2 k36 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k36 1) (x2KeyMult 2 k36 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k36 2) (x2KeyMult 2 k36 2) 512 = true ∧ gj327.length = x2KeySize 2 k36 ∧ x2KeySize 2 k36 ≤ 512 ∧ v327.length = 5 := by decide +kernel
theorem chk36 : trialKeyChk 2 k36 5 gj327 x2Trial_327 v327 :=
  trialKeyChk_intro 2 k36 5 gj327 x2Trial_327 v327 small36 gjok36 vok36
def k37 : x2Key 2 := ⟨37, by decide⟩
x2_gj_cols gj328 328 2 1 1 5 256
theorem gjc37_0 : (List.range 4).all (fun d => gjCheck 256 2 1 1 5 4 4 10 (x2JCols 328 (0 + d)) (gj328.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok37 : ∀ d < x2KeySize 2 k37, gjCheck 256 2 (x2KeyTypes 2 k37 0) (x2KeyTypes 2 k37 1) (x2KeyTypes 2 k37 2) (x2KeyMult 2 k37 0) (x2KeyMult 2 k37 1) (x2KeyMult 2 k37 2) (x2JCols (x2KeyGlobal 2 k37) d) (gj328.getD d 0) = true := by
  have hr : x2KeySize 2 k37 = 4 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 1 5 4 4 10 (x2JCols 328 d) (gj328.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 1 5 4 4 10 (x2JCols 328 d) (gj328.getD d 0)) 0 4 gjc37_0 d (Nat.zero_le d) (by omega)
x2_v_cols v328 gj328 328 256 160
theorem vc37_0 : (List.range 2).all (fun c => vCheck 256 160 4 gj328 (x2Trial_328.getD (0 + c) 0) (v328.getD (0 + c) 0)) = true := by decide +kernel
theorem vok37 : ∀ c < 2, vCheck 256 (x2KeyMult 2 k37 0 * x2KeyMult 2 k37 1 * x2KeyMult 2 k37 2) (x2KeySize 2 k37) gj328 (x2Trial_328.getD c 0) (v328.getD c 0) = true := by
  intro c hc
  show vCheck 256 160 4 gj328 (x2Trial_328.getD c 0) (v328.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 160 4 gj328 (x2Trial_328.getD c 0) (v328.getD c 0)) 0 2 vc37_0 c (Nat.zero_le c) (by omega)
theorem small37 : x2KeyDegree 2 k37 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k37 0 ∧ 1 ≤ x2KeyMult 2 k37 1 ∧ 1 ≤ x2KeyMult 2 k37 2 ∧ glRowOK 2 (x2KeyTypes 2 k37 0) (x2KeyMult 2 k37 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k37 1) (x2KeyMult 2 k37 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k37 2) (x2KeyMult 2 k37 2) 512 = true ∧ gj328.length = x2KeySize 2 k37 ∧ x2KeySize 2 k37 ≤ 512 ∧ v328.length = 2 := by decide +kernel
theorem chk37 : trialKeyChk 2 k37 2 gj328 x2Trial_328 v328 :=
  trialKeyChk_intro 2 k37 2 gj328 x2Trial_328 v328 small37 gjok37 vok37

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k36, ibFS [(v327, v327, 94810963968000)]), (k37, ibFS [(v328, v328, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 1, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN36 : N k36 = x2TrialForm 2 k36) (hN37 : N k37 = x2TrialForm 2 k37) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 1 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k36 5 _ gj327 x2Trial_327 v327 (by decide) (by rw [hN36]; exact trialForm_eq 2 k36 5 x2Trial_327 (by decide) rfl) chk36
  · exact keyOK_of_trialChk 2 N k37 2 _ gj328 x2Trial_328 v328 (by decide) (by rw [hN37]; exact trialForm_eq 2 k37 2 x2Trial_328 (by decide) rfl) chk37

end ThreeCopyQutritWerner.X2.InK2x115
