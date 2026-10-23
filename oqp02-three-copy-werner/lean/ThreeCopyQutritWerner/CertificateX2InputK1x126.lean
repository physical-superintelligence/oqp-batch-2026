module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 2, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x126
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k52 : x2Key 1 := ⟨52, by decide⟩
x2_gj_cols gj174 174 1 1 2 6 256
theorem gjc52_0 : (List.range 11).all (fun d => gjCheck 256 1 1 2 6 2 2 17 (x2JCols 174 (0 + d)) (gj174.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok52 : ∀ d < x2KeySize 1 k52, gjCheck 256 1 (x2KeyTypes 1 k52 0) (x2KeyTypes 1 k52 1) (x2KeyTypes 1 k52 2) (x2KeyMult 1 k52 0) (x2KeyMult 1 k52 1) (x2KeyMult 1 k52 2) (x2JCols (x2KeyGlobal 1 k52) d) (gj174.getD d 0) = true := by
  have hr : x2KeySize 1 k52 = 11 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 1 2 6 2 2 17 (x2JCols 174 d) (gj174.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 1 2 6 2 2 17 (x2JCols 174 d) (gj174.getD d 0)) 0 11 gjc52_0 d (Nat.zero_le d) (by omega)
x2_v_cols v174 gj174 174 256 68
theorem vc52_0 : (List.range 3).all (fun c => vCheck 256 68 11 gj174 (x2Trial_174.getD (0 + c) 0) (v174.getD (0 + c) 0)) = true := by decide +kernel
theorem vok52 : ∀ c < 3, vCheck 256 (x2KeyMult 1 k52 0 * x2KeyMult 1 k52 1 * x2KeyMult 1 k52 2) (x2KeySize 1 k52) gj174 (x2Trial_174.getD c 0) (v174.getD c 0) = true := by
  intro c hc
  show vCheck 256 68 11 gj174 (x2Trial_174.getD c 0) (v174.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 68 11 gj174 (x2Trial_174.getD c 0) (v174.getD c 0)) 0 3 vc52_0 c (Nat.zero_le c) (by omega)
theorem small52 : x2KeyDegree 1 k52 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k52 0 ∧ 1 ≤ x2KeyMult 1 k52 1 ∧ 1 ≤ x2KeyMult 1 k52 2 ∧ glRowOK 1 (x2KeyTypes 1 k52 0) (x2KeyMult 1 k52 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k52 1) (x2KeyMult 1 k52 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k52 2) (x2KeyMult 1 k52 2) 512 = true ∧ gj174.length = x2KeySize 1 k52 ∧ x2KeySize 1 k52 ≤ 512 ∧ v174.length = 3 := by decide +kernel
theorem chk52 : trialKeyChk 1 k52 3 gj174 x2Trial_174 v174 :=
  trialKeyChk_intro 1 k52 3 gj174 x2Trial_174 v174 small52 gjok52 vok52

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k52, ibFS [(v174, v174, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![1, 2, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN52 : N k52 = x2TrialForm 1 k52) :
    ∀ e ∈ ks, keyOK (x2Mult 1 1 * x2Mult 1 2 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k52 3 _ gj174 x2Trial_174 v174 (by decide) (by rw [hN52]; exact trialForm_eq 1 k52 3 x2Trial_174 (by decide) rfl) chk52

end ThreeCopyQutritWerner.X2.InK1x126
