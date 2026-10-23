module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 2, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x126
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k45 : x2Key 2 := ⟨45, by decide⟩
x2_gj_cols gj336 336 2 1 2 6 256
theorem gjc45_0 : (List.range 19).all (fun d => gjCheck 256 2 1 2 6 4 5 11 (x2JCols 336 (0 + d)) (gj336.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok45 : ∀ d < x2KeySize 2 k45, gjCheck 256 2 (x2KeyTypes 2 k45 0) (x2KeyTypes 2 k45 1) (x2KeyTypes 2 k45 2) (x2KeyMult 2 k45 0) (x2KeyMult 2 k45 1) (x2KeyMult 2 k45 2) (x2JCols (x2KeyGlobal 2 k45) d) (gj336.getD d 0) = true := by
  have hr : x2KeySize 2 k45 = 19 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 2 6 4 5 11 (x2JCols 336 d) (gj336.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 2 6 4 5 11 (x2JCols 336 d) (gj336.getD d 0)) 0 19 gjc45_0 d (Nat.zero_le d) (by omega)
x2_v_cols v336 gj336 336 256 220
theorem vc45_0 : (List.range 19).all (fun c => vCheck 256 220 19 gj336 (x2Trial_336.getD (0 + c) 0) (v336.getD (0 + c) 0)) = true := by decide +kernel
theorem vok45 : ∀ c < 19, vCheck 256 (x2KeyMult 2 k45 0 * x2KeyMult 2 k45 1 * x2KeyMult 2 k45 2) (x2KeySize 2 k45) gj336 (x2Trial_336.getD c 0) (v336.getD c 0) = true := by
  intro c hc
  show vCheck 256 220 19 gj336 (x2Trial_336.getD c 0) (v336.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 220 19 gj336 (x2Trial_336.getD c 0) (v336.getD c 0)) 0 19 vc45_0 c (Nat.zero_le c) (by omega)
theorem small45 : x2KeyDegree 2 k45 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k45 0 ∧ 1 ≤ x2KeyMult 2 k45 1 ∧ 1 ≤ x2KeyMult 2 k45 2 ∧ glRowOK 2 (x2KeyTypes 2 k45 0) (x2KeyMult 2 k45 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k45 1) (x2KeyMult 2 k45 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k45 2) (x2KeyMult 2 k45 2) 512 = true ∧ gj336.length = x2KeySize 2 k45 ∧ x2KeySize 2 k45 ≤ 512 ∧ v336.length = 19 := by decide +kernel
theorem chk45 : trialKeyChk 2 k45 19 gj336 x2Trial_336 v336 :=
  trialKeyChk_intro 2 k45 19 gj336 x2Trial_336 v336 small45 gjok45 vok45

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k45, ibFS [(v336, v336, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 2, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN45 : N k45 = x2TrialForm 2 k45) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 2 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k45 19 _ gj336 x2Trial_336 v336 (by decide) (by rw [hN45]; exact trialForm_eq 2 k45 19 x2Trial_336 (by decide) rfl) chk45

end ThreeCopyQutritWerner.X2.InK2x126
