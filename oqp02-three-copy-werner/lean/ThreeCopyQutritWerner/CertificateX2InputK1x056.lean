module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 5, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x056
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k29 : x2Key 1 := ⟨29, by decide⟩
x2_gj_cols gj151 151 1 0 5 6 256
theorem gjc29_0 : (List.range 19).all (fun d => gjCheck 256 1 0 5 6 1 7 17 (x2JCols 151 (0 + d)) (gj151.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok29 : ∀ d < x2KeySize 1 k29, gjCheck 256 1 (x2KeyTypes 1 k29 0) (x2KeyTypes 1 k29 1) (x2KeyTypes 1 k29 2) (x2KeyMult 1 k29 0) (x2KeyMult 1 k29 1) (x2KeyMult 1 k29 2) (x2JCols (x2KeyGlobal 1 k29) d) (gj151.getD d 0) = true := by
  have hr : x2KeySize 1 k29 = 19 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 5 6 1 7 17 (x2JCols 151 d) (gj151.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 5 6 1 7 17 (x2JCols 151 d) (gj151.getD d 0)) 0 19 gjc29_0 d (Nat.zero_le d) (by omega)
x2_v_cols v151 gj151 151 256 119
theorem vc29_0 : (List.range 8).all (fun c => vCheck 256 119 19 gj151 (x2Trial_151.getD (0 + c) 0) (v151.getD (0 + c) 0)) = true := by decide +kernel
theorem vok29 : ∀ c < 8, vCheck 256 (x2KeyMult 1 k29 0 * x2KeyMult 1 k29 1 * x2KeyMult 1 k29 2) (x2KeySize 1 k29) gj151 (x2Trial_151.getD c 0) (v151.getD c 0) = true := by
  intro c hc
  show vCheck 256 119 19 gj151 (x2Trial_151.getD c 0) (v151.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 119 19 gj151 (x2Trial_151.getD c 0) (v151.getD c 0)) 0 8 vc29_0 c (Nat.zero_le c) (by omega)
theorem small29 : x2KeyDegree 1 k29 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k29 0 ∧ 1 ≤ x2KeyMult 1 k29 1 ∧ 1 ≤ x2KeyMult 1 k29 2 ∧ glRowOK 1 (x2KeyTypes 1 k29 0) (x2KeyMult 1 k29 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k29 1) (x2KeyMult 1 k29 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k29 2) (x2KeyMult 1 k29 2) 512 = true ∧ gj151.length = x2KeySize 1 k29 ∧ x2KeySize 1 k29 ≤ 512 ∧ v151.length = 8 := by decide +kernel
theorem chk29 : trialKeyChk 1 k29 8 gj151 x2Trial_151 v151 :=
  trialKeyChk_intro 1 k29 8 gj151 x2Trial_151 v151 small29 gjok29 vok29

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k29, ibFS [(v151, v151, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 5, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN29 : N k29 = x2TrialForm 1 k29) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 5 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k29 8 _ gj151 x2Trial_151 v151 (by decide) (by rw [hN29]; exact trialForm_eq 1 k29 8 x2Trial_151 (by decide) rfl) chk29

end ThreeCopyQutritWerner.X2.InK1x056
