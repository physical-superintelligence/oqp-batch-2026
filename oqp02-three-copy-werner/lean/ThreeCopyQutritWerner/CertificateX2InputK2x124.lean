module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (1, 2, 4) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x124
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k43 : x2Key 2 := ⟨43, by decide⟩
x2_gj_cols gj334 334 2 1 2 4 256
theorem gjc43_0 : (List.range 25).all (fun d => gjCheck 256 2 1 2 4 4 5 15 (x2JCols 334 (0 + d)) (gj334.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok43 : ∀ d < x2KeySize 2 k43, gjCheck 256 2 (x2KeyTypes 2 k43 0) (x2KeyTypes 2 k43 1) (x2KeyTypes 2 k43 2) (x2KeyMult 2 k43 0) (x2KeyMult 2 k43 1) (x2KeyMult 2 k43 2) (x2JCols (x2KeyGlobal 2 k43) d) (gj334.getD d 0) = true := by
  have hr : x2KeySize 2 k43 = 25 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 1 2 4 4 5 15 (x2JCols 334 d) (gj334.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 1 2 4 4 5 15 (x2JCols 334 d) (gj334.getD d 0)) 0 25 gjc43_0 d (Nat.zero_le d) (by omega)
x2_v_cols v334 gj334 334 256 300
theorem vc43_0 : (List.range 10).all (fun c => vCheck 256 300 25 gj334 (x2Trial_334.getD (0 + c) 0) (v334.getD (0 + c) 0)) = true := by decide +kernel
theorem vok43 : ∀ c < 10, vCheck 256 (x2KeyMult 2 k43 0 * x2KeyMult 2 k43 1 * x2KeyMult 2 k43 2) (x2KeySize 2 k43) gj334 (x2Trial_334.getD c 0) (v334.getD c 0) = true := by
  intro c hc
  show vCheck 256 300 25 gj334 (x2Trial_334.getD c 0) (v334.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 300 25 gj334 (x2Trial_334.getD c 0) (v334.getD c 0)) 0 10 vc43_0 c (Nat.zero_le c) (by omega)
theorem small43 : x2KeyDegree 2 k43 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k43 0 ∧ 1 ≤ x2KeyMult 2 k43 1 ∧ 1 ≤ x2KeyMult 2 k43 2 ∧ glRowOK 2 (x2KeyTypes 2 k43 0) (x2KeyMult 2 k43 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k43 1) (x2KeyMult 2 k43 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k43 2) (x2KeyMult 2 k43 2) 512 = true ∧ gj334.length = x2KeySize 2 k43 ∧ x2KeySize 2 k43 ≤ 512 ∧ v334.length = 10 := by decide +kernel
theorem chk43 : trialKeyChk 2 k43 10 gj334 x2Trial_334 v334 :=
  trialKeyChk_intro 2 k43 10 gj334 x2Trial_334 v334 small43 gjok43 vok43

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k43, ibFS [(v334, v334, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![1, 2, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN43 : N k43 = x2TrialForm 2 k43) :
    ∀ e ∈ ks, keyOK (x2Mult 2 1 * x2Mult 2 2 * x2Mult 2 4) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k43 10 _ gj334 x2Trial_334 v334 (by decide) (by rw [hN43]; exact trialForm_eq 2 k43 10 x2Trial_334 (by decide) rfl) chk43

end ThreeCopyQutritWerner.X2.InK2x124
