module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 3, 5) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x035
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k19 : x2Key 1 := ⟨19, by decide⟩
x2_gj_cols gj141 141 1 0 3 5 256
theorem gjc19_0 : (List.range 9).all (fun d => gjCheck 256 1 0 3 5 1 9 7 (x2JCols 141 (0 + d)) (gj141.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok19 : ∀ d < x2KeySize 1 k19, gjCheck 256 1 (x2KeyTypes 1 k19 0) (x2KeyTypes 1 k19 1) (x2KeyTypes 1 k19 2) (x2KeyMult 1 k19 0) (x2KeyMult 1 k19 1) (x2KeyMult 1 k19 2) (x2JCols (x2KeyGlobal 1 k19) d) (gj141.getD d 0) = true := by
  have hr : x2KeySize 1 k19 = 9 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 3 5 1 9 7 (x2JCols 141 d) (gj141.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 3 5 1 9 7 (x2JCols 141 d) (gj141.getD d 0)) 0 9 gjc19_0 d (Nat.zero_le d) (by omega)
x2_v_cols v141 gj141 141 256 63
theorem vc19_0 : (List.range 1).all (fun c => vCheck 256 63 9 gj141 (x2Trial_141.getD (0 + c) 0) (v141.getD (0 + c) 0)) = true := by decide +kernel
theorem vok19 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k19 0 * x2KeyMult 1 k19 1 * x2KeyMult 1 k19 2) (x2KeySize 1 k19) gj141 (x2Trial_141.getD c 0) (v141.getD c 0) = true := by
  intro c hc
  show vCheck 256 63 9 gj141 (x2Trial_141.getD c 0) (v141.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 63 9 gj141 (x2Trial_141.getD c 0) (v141.getD c 0)) 0 1 vc19_0 c (Nat.zero_le c) (by omega)
theorem small19 : x2KeyDegree 1 k19 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k19 0 ∧ 1 ≤ x2KeyMult 1 k19 1 ∧ 1 ≤ x2KeyMult 1 k19 2 ∧ glRowOK 1 (x2KeyTypes 1 k19 0) (x2KeyMult 1 k19 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k19 1) (x2KeyMult 1 k19 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k19 2) (x2KeyMult 1 k19 2) 512 = true ∧ gj141.length = x2KeySize 1 k19 ∧ x2KeySize 1 k19 ≤ 512 ∧ v141.length = 1 := by decide +kernel
theorem chk19 : trialKeyChk 1 k19 1 gj141 x2Trial_141 v141 :=
  trialKeyChk_intro 1 k19 1 gj141 x2Trial_141 v141 small19 gjok19 vok19

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k19, ibFS [(v141, v141, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 3, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN19 : N k19 = x2TrialForm 1 k19) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 3 * x2Mult 1 5) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k19 1 _ gj141 x2Trial_141 v141 (by decide) (by rw [hN19]; exact trialForm_eq 1 k19 1 x2Trial_141 (by decide) rfl) chk19

end ThreeCopyQutritWerner.X2.InK1x035
