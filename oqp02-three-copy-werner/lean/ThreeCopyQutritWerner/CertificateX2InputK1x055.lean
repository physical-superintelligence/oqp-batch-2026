module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 5, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x055
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k27 : x2Key 1 := ⟨27, by decide⟩
x2_gj_cols gj149 149 1 0 5 5 256
theorem gjc27_0 : (List.range 3).all (fun d => gjCheck 256 1 0 5 5 1 7 7 (x2JCols 149 (0 + d)) (gj149.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok27 : ∀ d < x2KeySize 1 k27, gjCheck 256 1 (x2KeyTypes 1 k27 0) (x2KeyTypes 1 k27 1) (x2KeyTypes 1 k27 2) (x2KeyMult 1 k27 0) (x2KeyMult 1 k27 1) (x2KeyMult 1 k27 2) (x2JCols (x2KeyGlobal 1 k27) d) (gj149.getD d 0) = true := by
  have hr : x2KeySize 1 k27 = 3 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 5 5 1 7 7 (x2JCols 149 d) (gj149.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 5 5 1 7 7 (x2JCols 149 d) (gj149.getD d 0)) 0 3 gjc27_0 d (Nat.zero_le d) (by omega)
x2_v_cols v149 gj149 149 256 49
theorem vc27_0 : (List.range 1).all (fun c => vCheck 256 49 3 gj149 (x2Trial_149.getD (0 + c) 0) (v149.getD (0 + c) 0)) = true := by decide +kernel
theorem vok27 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k27 0 * x2KeyMult 1 k27 1 * x2KeyMult 1 k27 2) (x2KeySize 1 k27) gj149 (x2Trial_149.getD c 0) (v149.getD c 0) = true := by
  intro c hc
  show vCheck 256 49 3 gj149 (x2Trial_149.getD c 0) (v149.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 49 3 gj149 (x2Trial_149.getD c 0) (v149.getD c 0)) 0 1 vc27_0 c (Nat.zero_le c) (by omega)
theorem small27 : x2KeyDegree 1 k27 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k27 0 ∧ 1 ≤ x2KeyMult 1 k27 1 ∧ 1 ≤ x2KeyMult 1 k27 2 ∧ glRowOK 1 (x2KeyTypes 1 k27 0) (x2KeyMult 1 k27 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k27 1) (x2KeyMult 1 k27 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k27 2) (x2KeyMult 1 k27 2) 512 = true ∧ gj149.length = x2KeySize 1 k27 ∧ x2KeySize 1 k27 ≤ 512 ∧ v149.length = 1 := by decide +kernel
theorem chk27 : trialKeyChk 1 k27 1 gj149 x2Trial_149 v149 :=
  trialKeyChk_intro 1 k27 1 gj149 x2Trial_149 v149 small27 gjok27 vok27
def k28 : x2Key 1 := ⟨28, by decide⟩
x2_gj_cols gj150 150 1 0 5 5 256
theorem gjc28_0 : (List.range 3).all (fun d => gjCheck 256 1 0 5 5 1 7 7 (x2JCols 150 (0 + d)) (gj150.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok28 : ∀ d < x2KeySize 1 k28, gjCheck 256 1 (x2KeyTypes 1 k28 0) (x2KeyTypes 1 k28 1) (x2KeyTypes 1 k28 2) (x2KeyMult 1 k28 0) (x2KeyMult 1 k28 1) (x2KeyMult 1 k28 2) (x2JCols (x2KeyGlobal 1 k28) d) (gj150.getD d 0) = true := by
  have hr : x2KeySize 1 k28 = 3 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 5 5 1 7 7 (x2JCols 150 d) (gj150.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 5 5 1 7 7 (x2JCols 150 d) (gj150.getD d 0)) 0 3 gjc28_0 d (Nat.zero_le d) (by omega)
x2_v_cols v150 gj150 150 256 49
theorem vc28_0 : (List.range 1).all (fun c => vCheck 256 49 3 gj150 (x2Trial_150.getD (0 + c) 0) (v150.getD (0 + c) 0)) = true := by decide +kernel
theorem vok28 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k28 0 * x2KeyMult 1 k28 1 * x2KeyMult 1 k28 2) (x2KeySize 1 k28) gj150 (x2Trial_150.getD c 0) (v150.getD c 0) = true := by
  intro c hc
  show vCheck 256 49 3 gj150 (x2Trial_150.getD c 0) (v150.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 49 3 gj150 (x2Trial_150.getD c 0) (v150.getD c 0)) 0 1 vc28_0 c (Nat.zero_le c) (by omega)
theorem small28 : x2KeyDegree 1 k28 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k28 0 ∧ 1 ≤ x2KeyMult 1 k28 1 ∧ 1 ≤ x2KeyMult 1 k28 2 ∧ glRowOK 1 (x2KeyTypes 1 k28 0) (x2KeyMult 1 k28 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k28 1) (x2KeyMult 1 k28 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k28 2) (x2KeyMult 1 k28 2) 512 = true ∧ gj150.length = x2KeySize 1 k28 ∧ x2KeySize 1 k28 ≤ 512 ∧ v150.length = 1 := by decide +kernel
theorem chk28 : trialKeyChk 1 k28 1 gj150 x2Trial_150 v150 :=
  trialKeyChk_intro 1 k28 1 gj150 x2Trial_150 v150 small28 gjok28 vok28

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k27, ibFS [(v149, v149, 94810963968000)]), (k28, ibFS [(v150, v150, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 5, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN27 : N k27 = x2TrialForm 1 k27) (hN28 : N k28 = x2TrialForm 1 k28) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 5 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k27 1 _ gj149 x2Trial_149 v149 (by decide) (by rw [hN27]; exact trialForm_eq 1 k27 1 x2Trial_149 (by decide) rfl) chk27
  · exact keyOK_of_trialChk 1 N k28 1 _ gj150 x2Trial_150 v150 (by decide) (by rw [hN28]; exact trialForm_eq 1 k28 1 x2Trial_150 (by decide) rfl) chk28

end ThreeCopyQutritWerner.X2.InK1x055
