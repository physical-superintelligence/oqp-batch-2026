module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 4, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x046
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k25 : x2Key 1 := ⟨25, by decide⟩
x2_gj_cols gj147 147 1 0 4 6 256
theorem gjc25_0 : (List.range 20).all (fun d => gjCheck 256 1 0 4 6 1 7 17 (x2JCols 147 (0 + d)) (gj147.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok25 : ∀ d < x2KeySize 1 k25, gjCheck 256 1 (x2KeyTypes 1 k25 0) (x2KeyTypes 1 k25 1) (x2KeyTypes 1 k25 2) (x2KeyMult 1 k25 0) (x2KeyMult 1 k25 1) (x2KeyMult 1 k25 2) (x2JCols (x2KeyGlobal 1 k25) d) (gj147.getD d 0) = true := by
  have hr : x2KeySize 1 k25 = 20 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 4 6 1 7 17 (x2JCols 147 d) (gj147.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 4 6 1 7 17 (x2JCols 147 d) (gj147.getD d 0)) 0 20 gjc25_0 d (Nat.zero_le d) (by omega)
x2_v_cols v147 gj147 147 256 119
theorem vc25_0 : (List.range 7).all (fun c => vCheck 256 119 20 gj147 (x2Trial_147.getD (0 + c) 0) (v147.getD (0 + c) 0)) = true := by decide +kernel
theorem vok25 : ∀ c < 7, vCheck 256 (x2KeyMult 1 k25 0 * x2KeyMult 1 k25 1 * x2KeyMult 1 k25 2) (x2KeySize 1 k25) gj147 (x2Trial_147.getD c 0) (v147.getD c 0) = true := by
  intro c hc
  show vCheck 256 119 20 gj147 (x2Trial_147.getD c 0) (v147.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 119 20 gj147 (x2Trial_147.getD c 0) (v147.getD c 0)) 0 7 vc25_0 c (Nat.zero_le c) (by omega)
theorem small25 : x2KeyDegree 1 k25 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k25 0 ∧ 1 ≤ x2KeyMult 1 k25 1 ∧ 1 ≤ x2KeyMult 1 k25 2 ∧ glRowOK 1 (x2KeyTypes 1 k25 0) (x2KeyMult 1 k25 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k25 1) (x2KeyMult 1 k25 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k25 2) (x2KeyMult 1 k25 2) 512 = true ∧ gj147.length = x2KeySize 1 k25 ∧ x2KeySize 1 k25 ≤ 512 ∧ v147.length = 7 := by decide +kernel
theorem chk25 : trialKeyChk 1 k25 7 gj147 x2Trial_147 v147 :=
  trialKeyChk_intro 1 k25 7 gj147 x2Trial_147 v147 small25 gjok25 vok25

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k25, ibFS [(v147, v147, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 4, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN25 : N k25 = x2TrialForm 1 k25) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 4 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k25 7 _ gj147 x2Trial_147 v147 (by decide) (by rw [hN25]; exact trialForm_eq 1 k25 7 x2Trial_147 (by decide) rfl) chk25

end ThreeCopyQutritWerner.X2.InK1x046
