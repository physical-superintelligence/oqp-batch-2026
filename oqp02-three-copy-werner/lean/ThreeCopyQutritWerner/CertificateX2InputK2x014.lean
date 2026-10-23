module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 1, 4) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x014
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k7 : x2Key 2 := ⟨7, by decide⟩
x2_gj_cols gj298 298 2 0 1 4 256
theorem gjc7_0 : (List.range 5).all (fun d => gjCheck 256 2 0 1 4 1 4 15 (x2JCols 298 (0 + d)) (gj298.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok7 : ∀ d < x2KeySize 2 k7, gjCheck 256 2 (x2KeyTypes 2 k7 0) (x2KeyTypes 2 k7 1) (x2KeyTypes 2 k7 2) (x2KeyMult 2 k7 0) (x2KeyMult 2 k7 1) (x2KeyMult 2 k7 2) (x2JCols (x2KeyGlobal 2 k7) d) (gj298.getD d 0) = true := by
  have hr : x2KeySize 2 k7 = 5 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 1 4 1 4 15 (x2JCols 298 d) (gj298.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 1 4 1 4 15 (x2JCols 298 d) (gj298.getD d 0)) 0 5 gjc7_0 d (Nat.zero_le d) (by omega)
x2_v_cols v298 gj298 298 256 60
theorem vc7_0 : (List.range 2).all (fun c => vCheck 256 60 5 gj298 (x2Trial_298.getD (0 + c) 0) (v298.getD (0 + c) 0)) = true := by decide +kernel
theorem vok7 : ∀ c < 2, vCheck 256 (x2KeyMult 2 k7 0 * x2KeyMult 2 k7 1 * x2KeyMult 2 k7 2) (x2KeySize 2 k7) gj298 (x2Trial_298.getD c 0) (v298.getD c 0) = true := by
  intro c hc
  show vCheck 256 60 5 gj298 (x2Trial_298.getD c 0) (v298.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 60 5 gj298 (x2Trial_298.getD c 0) (v298.getD c 0)) 0 2 vc7_0 c (Nat.zero_le c) (by omega)
theorem small7 : x2KeyDegree 2 k7 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k7 0 ∧ 1 ≤ x2KeyMult 2 k7 1 ∧ 1 ≤ x2KeyMult 2 k7 2 ∧ glRowOK 2 (x2KeyTypes 2 k7 0) (x2KeyMult 2 k7 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k7 1) (x2KeyMult 2 k7 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k7 2) (x2KeyMult 2 k7 2) 512 = true ∧ gj298.length = x2KeySize 2 k7 ∧ x2KeySize 2 k7 ≤ 512 ∧ v298.length = 2 := by decide +kernel
theorem chk7 : trialKeyChk 2 k7 2 gj298 x2Trial_298 v298 :=
  trialKeyChk_intro 2 k7 2 gj298 x2Trial_298 v298 small7 gjok7 vok7

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k7, ibFS [(v298, v298, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 1, 4] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN7 : N k7 = x2TrialForm 2 k7) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 1 * x2Mult 2 4) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k7 2 _ gj298 x2Trial_298 v298 (by decide) (by rw [hN7]; exact trialForm_eq 2 k7 2 x2Trial_298 (by decide) rfl) chk7

end ThreeCopyQutritWerner.X2.InK2x014
