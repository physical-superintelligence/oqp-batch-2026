module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 1, 4) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x114
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k34 : x2Key 2 := ⟨34, by decide⟩
x2_gj_cols gj325 325 2 1 1 4 256
theorem gjc34_0 : (List.range 12).all (fun d => gjCheck 256 2 1 1 4 4 4 15 (x2JCols 325 (0 + d)) (gj325.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok34 : ∀ d < x2KeySize 2 k34, gjCheck 256 2 (x2KeyTypes 2 k34 0) (x2KeyTypes 2 k34 1) (x2KeyTypes 2 k34 2) (x2KeyMult 2 k34 0) (x2KeyMult 2 k34 1) (x2KeyMult 2 k34 2) (x2JCols (x2KeyGlobal 2 k34) d) (gj325.getD d 0) = true := by
  have hr : x2KeySize 2 k34 = 12 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 1 4 4 4 15 (x2JCols 325 d) (gj325.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 1 4 4 4 15 (x2JCols 325 d) (gj325.getD d 0)) 0 12 gjc34_0 d (Nat.zero_le d) (by omega)
x2_v_cols v325 gj325 325 256 240
theorem vc34_0 : (List.range 4).all (fun c => vCheck 256 240 12 gj325 (x2Trial_325.getD (0 + c) 0) (v325.getD (0 + c) 0)) = true := by decide +kernel
theorem vok34 : ∀ c < 4, vCheck 256 (x2KeyMult 2 k34 0 * x2KeyMult 2 k34 1 * x2KeyMult 2 k34 2) (x2KeySize 2 k34) gj325 (x2Trial_325.getD c 0) (v325.getD c 0) = true := by
  intro c hc
  show vCheck 256 240 12 gj325 (x2Trial_325.getD c 0) (v325.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 240 12 gj325 (x2Trial_325.getD c 0) (v325.getD c 0)) 0 4 vc34_0 c (Nat.zero_le c) (by omega)
theorem small34 : x2KeyDegree 2 k34 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k34 0 ∧ 1 ≤ x2KeyMult 2 k34 1 ∧ 1 ≤ x2KeyMult 2 k34 2 ∧ glRowOK 2 (x2KeyTypes 2 k34 0) (x2KeyMult 2 k34 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k34 1) (x2KeyMult 2 k34 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k34 2) (x2KeyMult 2 k34 2) 512 = true ∧ gj325.length = x2KeySize 2 k34 ∧ x2KeySize 2 k34 ≤ 512 ∧ v325.length = 4 := by decide +kernel
theorem chk34 : trialKeyChk 2 k34 4 gj325 x2Trial_325 v325 :=
  trialKeyChk_intro 2 k34 4 gj325 x2Trial_325 v325 small34 gjok34 vok34
def k35 : x2Key 2 := ⟨35, by decide⟩
x2_gj_cols gj326 326 2 1 1 4 256
theorem gjc35_0 : (List.range 8).all (fun d => gjCheck 256 2 1 1 4 4 4 15 (x2JCols 326 (0 + d)) (gj326.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok35 : ∀ d < x2KeySize 2 k35, gjCheck 256 2 (x2KeyTypes 2 k35 0) (x2KeyTypes 2 k35 1) (x2KeyTypes 2 k35 2) (x2KeyMult 2 k35 0) (x2KeyMult 2 k35 1) (x2KeyMult 2 k35 2) (x2JCols (x2KeyGlobal 2 k35) d) (gj326.getD d 0) = true := by
  have hr : x2KeySize 2 k35 = 8 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 1 4 4 4 15 (x2JCols 326 d) (gj326.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 1 4 4 4 15 (x2JCols 326 d) (gj326.getD d 0)) 0 8 gjc35_0 d (Nat.zero_le d) (by omega)
x2_v_cols v326 gj326 326 256 240
theorem vc35_0 : (List.range 4).all (fun c => vCheck 256 240 8 gj326 (x2Trial_326.getD (0 + c) 0) (v326.getD (0 + c) 0)) = true := by decide +kernel
theorem vok35 : ∀ c < 4, vCheck 256 (x2KeyMult 2 k35 0 * x2KeyMult 2 k35 1 * x2KeyMult 2 k35 2) (x2KeySize 2 k35) gj326 (x2Trial_326.getD c 0) (v326.getD c 0) = true := by
  intro c hc
  show vCheck 256 240 8 gj326 (x2Trial_326.getD c 0) (v326.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 240 8 gj326 (x2Trial_326.getD c 0) (v326.getD c 0)) 0 4 vc35_0 c (Nat.zero_le c) (by omega)
theorem small35 : x2KeyDegree 2 k35 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k35 0 ∧ 1 ≤ x2KeyMult 2 k35 1 ∧ 1 ≤ x2KeyMult 2 k35 2 ∧ glRowOK 2 (x2KeyTypes 2 k35 0) (x2KeyMult 2 k35 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k35 1) (x2KeyMult 2 k35 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k35 2) (x2KeyMult 2 k35 2) 512 = true ∧ gj326.length = x2KeySize 2 k35 ∧ x2KeySize 2 k35 ≤ 512 ∧ v326.length = 4 := by decide +kernel
theorem chk35 : trialKeyChk 2 k35 4 gj326 x2Trial_326 v326 :=
  trialKeyChk_intro 2 k35 4 gj326 x2Trial_326 v326 small35 gjok35 vok35

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k34, ibFS [(v325, v325, 94810963968000)]), (k35, ibFS [(v326, v326, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 1, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN34 : N k34 = x2TrialForm 2 k34) (hN35 : N k35 = x2TrialForm 2 k35) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 1 * x2Mult 2 4) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 2 N k34 4 _ gj325 x2Trial_325 v325 (by decide) (by rw [hN34]; exact trialForm_eq 2 k34 4 x2Trial_325 (by decide) rfl) chk34
  · exact keyOK_of_trialChk 2 N k35 4 _ gj326 x2Trial_326 v326 (by decide) (by rw [hN35]; exact trialForm_eq 2 k35 4 x2Trial_326 (by decide) rfl) chk35

end ThreeCopyQutritWerner.X2.InK2x114
