module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 7, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x477
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k145 : x2Key 1 := ⟨145, by decide⟩
x2_gj_cols gj267 267 1 4 7 7 256
theorem gjc145_0 : (List.range 25).all (fun d => gjCheck 256 1 4 7 7 7 6 6 (x2JCols 267 (0 + d)) (gj267.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok145 : ∀ d < x2KeySize 1 k145, gjCheck 256 1 (x2KeyTypes 1 k145 0) (x2KeyTypes 1 k145 1) (x2KeyTypes 1 k145 2) (x2KeyMult 1 k145 0) (x2KeyMult 1 k145 1) (x2KeyMult 1 k145 2) (x2JCols (x2KeyGlobal 1 k145) d) (gj267.getD d 0) = true := by
  have hr : x2KeySize 1 k145 = 25 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 7 7 7 6 6 (x2JCols 267 d) (gj267.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 7 7 7 6 6 (x2JCols 267 d) (gj267.getD d 0)) 0 25 gjc145_0 d (Nat.zero_le d) (by omega)
x2_v_cols v267 gj267 267 256 252
theorem vc145_0 : (List.range 18).all (fun c => vCheck 256 252 25 gj267 (x2Trial_267.getD (0 + c) 0) (v267.getD (0 + c) 0)) = true := by decide +kernel
theorem vok145 : ∀ c < 18, vCheck 256 (x2KeyMult 1 k145 0 * x2KeyMult 1 k145 1 * x2KeyMult 1 k145 2) (x2KeySize 1 k145) gj267 (x2Trial_267.getD c 0) (v267.getD c 0) = true := by
  intro c hc
  show vCheck 256 252 25 gj267 (x2Trial_267.getD c 0) (v267.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 252 25 gj267 (x2Trial_267.getD c 0) (v267.getD c 0)) 0 18 vc145_0 c (Nat.zero_le c) (by omega)
theorem small145 : x2KeyDegree 1 k145 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k145 0 ∧ 1 ≤ x2KeyMult 1 k145 1 ∧ 1 ≤ x2KeyMult 1 k145 2 ∧ glRowOK 1 (x2KeyTypes 1 k145 0) (x2KeyMult 1 k145 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k145 1) (x2KeyMult 1 k145 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k145 2) (x2KeyMult 1 k145 2) 512 = true ∧ gj267.length = x2KeySize 1 k145 ∧ x2KeySize 1 k145 ≤ 512 ∧ v267.length = 18 := by decide +kernel
theorem chk145 : trialKeyChk 1 k145 18 gj267 x2Trial_267 v267 :=
  trialKeyChk_intro 1 k145 18 gj267 x2Trial_267 v267 small145 gjok145 vok145
def k146 : x2Key 1 := ⟨146, by decide⟩
x2_gj_cols gj268 268 1 4 7 7 256
theorem gjc146_0 : (List.range 17).all (fun d => gjCheck 256 1 4 7 7 7 6 6 (x2JCols 268 (0 + d)) (gj268.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok146 : ∀ d < x2KeySize 1 k146, gjCheck 256 1 (x2KeyTypes 1 k146 0) (x2KeyTypes 1 k146 1) (x2KeyTypes 1 k146 2) (x2KeyMult 1 k146 0) (x2KeyMult 1 k146 1) (x2KeyMult 1 k146 2) (x2JCols (x2KeyGlobal 1 k146) d) (gj268.getD d 0) = true := by
  have hr : x2KeySize 1 k146 = 17 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 7 7 7 6 6 (x2JCols 268 d) (gj268.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 7 7 7 6 6 (x2JCols 268 d) (gj268.getD d 0)) 0 17 gjc146_0 d (Nat.zero_le d) (by omega)
x2_v_cols v268 gj268 268 256 252
theorem vc146_0 : (List.range 10).all (fun c => vCheck 256 252 17 gj268 (x2Trial_268.getD (0 + c) 0) (v268.getD (0 + c) 0)) = true := by decide +kernel
theorem vok146 : ∀ c < 10, vCheck 256 (x2KeyMult 1 k146 0 * x2KeyMult 1 k146 1 * x2KeyMult 1 k146 2) (x2KeySize 1 k146) gj268 (x2Trial_268.getD c 0) (v268.getD c 0) = true := by
  intro c hc
  show vCheck 256 252 17 gj268 (x2Trial_268.getD c 0) (v268.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 252 17 gj268 (x2Trial_268.getD c 0) (v268.getD c 0)) 0 10 vc146_0 c (Nat.zero_le c) (by omega)
theorem small146 : x2KeyDegree 1 k146 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k146 0 ∧ 1 ≤ x2KeyMult 1 k146 1 ∧ 1 ≤ x2KeyMult 1 k146 2 ∧ glRowOK 1 (x2KeyTypes 1 k146 0) (x2KeyMult 1 k146 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k146 1) (x2KeyMult 1 k146 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k146 2) (x2KeyMult 1 k146 2) 512 = true ∧ gj268.length = x2KeySize 1 k146 ∧ x2KeySize 1 k146 ≤ 512 ∧ v268.length = 10 := by decide +kernel
theorem chk146 : trialKeyChk 1 k146 10 gj268 x2Trial_268 v268 :=
  trialKeyChk_intro 1 k146 10 gj268 x2Trial_268 v268 small146 gjok146 vok146

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k145, ibFS [(v267, v267, 94810963968000)]), (k146, ibFS [(v268, v268, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![4, 7, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN145 : N k145 = x2TrialForm 1 k145) (hN146 : N k146 = x2TrialForm 1 k146) :
    ∀ e ∈ ks, keyOK (x2Mult 1 4 * x2Mult 1 7 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k145 18 _ gj267 x2Trial_267 v267 (by decide) (by rw [hN145]; exact trialForm_eq 1 k145 18 x2Trial_267 (by decide) rfl) chk145
  · exact keyOK_of_trialChk 1 N k146 10 _ gj268 x2Trial_268 v268 (by decide) (by rw [hN146]; exact trialForm_eq 1 k146 10 x2Trial_268 (by decide) rfl) chk146

end ThreeCopyQutritWerner.X2.InK1x477
