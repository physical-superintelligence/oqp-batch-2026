module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 0, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x005
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k2 : x2Key 2 := ⟨2, by decide⟩
x2_gj_cols gj293 293 2 0 0 5 256
theorem gjc2_0 : (List.range 2).all (fun d => gjCheck 256 2 0 0 5 1 1 10 (x2JCols 293 (0 + d)) (gj293.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok2 : ∀ d < x2KeySize 2 k2, gjCheck 256 2 (x2KeyTypes 2 k2 0) (x2KeyTypes 2 k2 1) (x2KeyTypes 2 k2 2) (x2KeyMult 2 k2 0) (x2KeyMult 2 k2 1) (x2KeyMult 2 k2 2) (x2JCols (x2KeyGlobal 2 k2) d) (gj293.getD d 0) = true := by
  have hr : x2KeySize 2 k2 = 2 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 0 5 1 1 10 (x2JCols 293 d) (gj293.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 0 5 1 1 10 (x2JCols 293 d) (gj293.getD d 0)) 0 2 gjc2_0 d (Nat.zero_le d) (by omega)
x2_v_cols v293 gj293 293 256 10
theorem vc2_0 : (List.range 1).all (fun c => vCheck 256 10 2 gj293 (x2Trial_293.getD (0 + c) 0) (v293.getD (0 + c) 0)) = true := by decide +kernel
theorem vok2 : ∀ c < 1, vCheck 256 (x2KeyMult 2 k2 0 * x2KeyMult 2 k2 1 * x2KeyMult 2 k2 2) (x2KeySize 2 k2) gj293 (x2Trial_293.getD c 0) (v293.getD c 0) = true := by
  intro c hc
  show vCheck 256 10 2 gj293 (x2Trial_293.getD c 0) (v293.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 10 2 gj293 (x2Trial_293.getD c 0) (v293.getD c 0)) 0 1 vc2_0 c (Nat.zero_le c) (by omega)
theorem small2 : x2KeyDegree 2 k2 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k2 0 ∧ 1 ≤ x2KeyMult 2 k2 1 ∧ 1 ≤ x2KeyMult 2 k2 2 ∧ glRowOK 2 (x2KeyTypes 2 k2 0) (x2KeyMult 2 k2 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k2 1) (x2KeyMult 2 k2 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k2 2) (x2KeyMult 2 k2 2) 512 = true ∧ gj293.length = x2KeySize 2 k2 ∧ x2KeySize 2 k2 ≤ 512 ∧ v293.length = 1 := by decide +kernel
theorem chk2 : trialKeyChk 2 k2 1 gj293 x2Trial_293 v293 :=
  trialKeyChk_intro 2 k2 1 gj293 x2Trial_293 v293 small2 gjok2 vok2

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k2, ibFS [(v293, v293, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 0, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN2 : N k2 = x2TrialForm 2 k2) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 0 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k2 1 _ gj293 x2Trial_293 v293 (by decide) (by rw [hN2]; exact trialForm_eq 2 k2 1 x2Trial_293 (by decide) rfl) chk2

end ThreeCopyQutritWerner.X2.InK2x005
