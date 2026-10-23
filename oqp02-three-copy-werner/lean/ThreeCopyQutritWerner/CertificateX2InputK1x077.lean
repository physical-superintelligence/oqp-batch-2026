module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 7, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x077
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k34 : x2Key 1 := ⟨34, by decide⟩
x2_gj_cols gj156 156 1 0 7 7 256
theorem gjc34_0 : (List.range 3).all (fun d => gjCheck 256 1 0 7 7 1 6 6 (x2JCols 156 (0 + d)) (gj156.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok34 : ∀ d < x2KeySize 1 k34, gjCheck 256 1 (x2KeyTypes 1 k34 0) (x2KeyTypes 1 k34 1) (x2KeyTypes 1 k34 2) (x2KeyMult 1 k34 0) (x2KeyMult 1 k34 1) (x2KeyMult 1 k34 2) (x2JCols (x2KeyGlobal 1 k34) d) (gj156.getD d 0) = true := by
  have hr : x2KeySize 1 k34 = 3 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 7 7 1 6 6 (x2JCols 156 d) (gj156.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 7 7 1 6 6 (x2JCols 156 d) (gj156.getD d 0)) 0 3 gjc34_0 d (Nat.zero_le d) (by omega)
x2_v_cols v156 gj156 156 256 36
theorem vc34_0 : (List.range 1).all (fun c => vCheck 256 36 3 gj156 (x2Trial_156.getD (0 + c) 0) (v156.getD (0 + c) 0)) = true := by decide +kernel
theorem vok34 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k34 0 * x2KeyMult 1 k34 1 * x2KeyMult 1 k34 2) (x2KeySize 1 k34) gj156 (x2Trial_156.getD c 0) (v156.getD c 0) = true := by
  intro c hc
  show vCheck 256 36 3 gj156 (x2Trial_156.getD c 0) (v156.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 36 3 gj156 (x2Trial_156.getD c 0) (v156.getD c 0)) 0 1 vc34_0 c (Nat.zero_le c) (by omega)
theorem small34 : x2KeyDegree 1 k34 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k34 0 ∧ 1 ≤ x2KeyMult 1 k34 1 ∧ 1 ≤ x2KeyMult 1 k34 2 ∧ glRowOK 1 (x2KeyTypes 1 k34 0) (x2KeyMult 1 k34 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k34 1) (x2KeyMult 1 k34 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k34 2) (x2KeyMult 1 k34 2) 512 = true ∧ gj156.length = x2KeySize 1 k34 ∧ x2KeySize 1 k34 ≤ 512 ∧ v156.length = 1 := by decide +kernel
theorem chk34 : trialKeyChk 1 k34 1 gj156 x2Trial_156 v156 :=
  trialKeyChk_intro 1 k34 1 gj156 x2Trial_156 v156 small34 gjok34 vok34
def k35 : x2Key 1 := ⟨35, by decide⟩
x2_gj_cols gj157 157 1 0 7 7 256
theorem gjc35_0 : (List.range 3).all (fun d => gjCheck 256 1 0 7 7 1 6 6 (x2JCols 157 (0 + d)) (gj157.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok35 : ∀ d < x2KeySize 1 k35, gjCheck 256 1 (x2KeyTypes 1 k35 0) (x2KeyTypes 1 k35 1) (x2KeyTypes 1 k35 2) (x2KeyMult 1 k35 0) (x2KeyMult 1 k35 1) (x2KeyMult 1 k35 2) (x2JCols (x2KeyGlobal 1 k35) d) (gj157.getD d 0) = true := by
  have hr : x2KeySize 1 k35 = 3 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 7 7 1 6 6 (x2JCols 157 d) (gj157.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 7 7 1 6 6 (x2JCols 157 d) (gj157.getD d 0)) 0 3 gjc35_0 d (Nat.zero_le d) (by omega)
x2_v_cols v157 gj157 157 256 36
theorem vc35_0 : (List.range 1).all (fun c => vCheck 256 36 3 gj157 (x2Trial_157.getD (0 + c) 0) (v157.getD (0 + c) 0)) = true := by decide +kernel
theorem vok35 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k35 0 * x2KeyMult 1 k35 1 * x2KeyMult 1 k35 2) (x2KeySize 1 k35) gj157 (x2Trial_157.getD c 0) (v157.getD c 0) = true := by
  intro c hc
  show vCheck 256 36 3 gj157 (x2Trial_157.getD c 0) (v157.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 36 3 gj157 (x2Trial_157.getD c 0) (v157.getD c 0)) 0 1 vc35_0 c (Nat.zero_le c) (by omega)
theorem small35 : x2KeyDegree 1 k35 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k35 0 ∧ 1 ≤ x2KeyMult 1 k35 1 ∧ 1 ≤ x2KeyMult 1 k35 2 ∧ glRowOK 1 (x2KeyTypes 1 k35 0) (x2KeyMult 1 k35 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k35 1) (x2KeyMult 1 k35 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k35 2) (x2KeyMult 1 k35 2) 512 = true ∧ gj157.length = x2KeySize 1 k35 ∧ x2KeySize 1 k35 ≤ 512 ∧ v157.length = 1 := by decide +kernel
theorem chk35 : trialKeyChk 1 k35 1 gj157 x2Trial_157 v157 :=
  trialKeyChk_intro 1 k35 1 gj157 x2Trial_157 v157 small35 gjok35 vok35

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k34, ibFS [(v156, v156, 94810963968000)]), (k35, ibFS [(v157, v157, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 7, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN34 : N k34 = x2TrialForm 1 k34) (hN35 : N k35 = x2TrialForm 1 k35) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 7 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact keyOK_of_trialChk 1 N k34 1 _ gj156 x2Trial_156 v156 (by decide) (by rw [hN34]; exact trialForm_eq 1 k34 1 x2Trial_156 (by decide) rfl) chk34
  · exact keyOK_of_trialChk 1 N k35 1 _ gj157 x2Trial_157 v157 (by decide) (by rw [hN35]; exact trialForm_eq 1 k35 1 x2Trial_157 (by decide) rfl) chk35

end ThreeCopyQutritWerner.X2.InK1x077
