module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 5, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x155
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k65 : x2Key 1 := ⟨65, by decide⟩
x2_gj_cols gj187 187 1 1 5 5 256
theorem gjc65_0 : (List.range 9).all (fun d => gjCheck 256 1 1 5 5 2 7 7 (x2JCols 187 (0 + d)) (gj187.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok65 : ∀ d < x2KeySize 1 k65, gjCheck 256 1 (x2KeyTypes 1 k65 0) (x2KeyTypes 1 k65 1) (x2KeyTypes 1 k65 2) (x2KeyMult 1 k65 0) (x2KeyMult 1 k65 1) (x2KeyMult 1 k65 2) (x2JCols (x2KeyGlobal 1 k65) d) (gj187.getD d 0) = true := by
  have hr : x2KeySize 1 k65 = 9 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 5 5 2 7 7 (x2JCols 187 d) (gj187.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 5 5 2 7 7 (x2JCols 187 d) (gj187.getD d 0)) 0 9 gjc65_0 d (Nat.zero_le d) (by omega)
x2_v_cols v187 gj187 187 256 98
theorem vc65_0 : (List.range 3).all (fun c => vCheck 256 98 9 gj187 (x2Trial_187.getD (0 + c) 0) (v187.getD (0 + c) 0)) = true := by decide +kernel
theorem vok65 : ∀ c < 3, vCheck 256 (x2KeyMult 1 k65 0 * x2KeyMult 1 k65 1 * x2KeyMult 1 k65 2) (x2KeySize 1 k65) gj187 (x2Trial_187.getD c 0) (v187.getD c 0) = true := by
  intro c hc
  show vCheck 256 98 9 gj187 (x2Trial_187.getD c 0) (v187.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 98 9 gj187 (x2Trial_187.getD c 0) (v187.getD c 0)) 0 3 vc65_0 c (Nat.zero_le c) (by omega)
theorem small65 : x2KeyDegree 1 k65 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k65 0 ∧ 1 ≤ x2KeyMult 1 k65 1 ∧ 1 ≤ x2KeyMult 1 k65 2 ∧ glRowOK 1 (x2KeyTypes 1 k65 0) (x2KeyMult 1 k65 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k65 1) (x2KeyMult 1 k65 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k65 2) (x2KeyMult 1 k65 2) 512 = true ∧ gj187.length = x2KeySize 1 k65 ∧ x2KeySize 1 k65 ≤ 512 ∧ v187.length = 3 := by decide +kernel
theorem chk65 : trialKeyChk 1 k65 3 gj187 x2Trial_187 v187 :=
  trialKeyChk_intro 1 k65 3 gj187 x2Trial_187 v187 small65 gjok65 vok65
def k66 : x2Key 1 := ⟨66, by decide⟩
x2_gj_cols gj188 188 1 1 5 5 256
theorem gjc66_0 : (List.range 6).all (fun d => gjCheck 256 1 1 5 5 2 7 7 (x2JCols 188 (0 + d)) (gj188.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok66 : ∀ d < x2KeySize 1 k66, gjCheck 256 1 (x2KeyTypes 1 k66 0) (x2KeyTypes 1 k66 1) (x2KeyTypes 1 k66 2) (x2KeyMult 1 k66 0) (x2KeyMult 1 k66 1) (x2KeyMult 1 k66 2) (x2JCols (x2KeyGlobal 1 k66) d) (gj188.getD d 0) = true := by
  have hr : x2KeySize 1 k66 = 6 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 5 5 2 7 7 (x2JCols 188 d) (gj188.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 5 5 2 7 7 (x2JCols 188 d) (gj188.getD d 0)) 0 6 gjc66_0 d (Nat.zero_le d) (by omega)
x2_v_cols v188 gj188 188 256 98
theorem vc66_0 : (List.range 3).all (fun c => vCheck 256 98 6 gj188 (x2Trial_188.getD (0 + c) 0) (v188.getD (0 + c) 0)) = true := by decide +kernel
theorem vok66 : ∀ c < 3, vCheck 256 (x2KeyMult 1 k66 0 * x2KeyMult 1 k66 1 * x2KeyMult 1 k66 2) (x2KeySize 1 k66) gj188 (x2Trial_188.getD c 0) (v188.getD c 0) = true := by
  intro c hc
  show vCheck 256 98 6 gj188 (x2Trial_188.getD c 0) (v188.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 98 6 gj188 (x2Trial_188.getD c 0) (v188.getD c 0)) 0 3 vc66_0 c (Nat.zero_le c) (by omega)
theorem small66 : x2KeyDegree 1 k66 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k66 0 ∧ 1 ≤ x2KeyMult 1 k66 1 ∧ 1 ≤ x2KeyMult 1 k66 2 ∧ glRowOK 1 (x2KeyTypes 1 k66 0) (x2KeyMult 1 k66 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k66 1) (x2KeyMult 1 k66 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k66 2) (x2KeyMult 1 k66 2) 512 = true ∧ gj188.length = x2KeySize 1 k66 ∧ x2KeySize 1 k66 ≤ 512 ∧ v188.length = 3 := by decide +kernel
theorem chk66 : trialKeyChk 1 k66 3 gj188 x2Trial_188 v188 :=
  trialKeyChk_intro 1 k66 3 gj188 x2Trial_188 v188 small66 gjok66 vok66

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k65, ibFS [(v187, v187, 94810963968000)]), (k66, ibFS [(v188, v188, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 5, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN65 : N k65 = x2TrialForm 1 k65) (hN66 : N k66 = x2TrialForm 1 k66) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 5 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k65 3 _ gj187 x2Trial_187 v187 (by decide) (by rw [hN65]; exact trialForm_eq 1 k65 3 x2Trial_187 (by decide) rfl) chk65
  · exact keyOK_of_trialChk 1 N k66 3 _ gj188 x2Trial_188 v188 (by decide) (by rw [hN66]; exact trialForm_eq 1 k66 3 x2Trial_188 (by decide) rfl) chk66

end ThreeCopyQutritWerner.X2.InK1x155
