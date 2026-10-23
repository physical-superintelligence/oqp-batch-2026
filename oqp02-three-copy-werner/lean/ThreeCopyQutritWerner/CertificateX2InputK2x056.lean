module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 5, 6) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x056
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k25 : x2Key 2 := ⟨25, by decide⟩
x2_gj_cols gj316 316 2 0 5 6 256
theorem gjc25_0 : (List.range 8).all (fun d => gjCheck 256 2 0 5 6 1 10 11 (x2JCols 316 (0 + d)) (gj316.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok25 : ∀ d < x2KeySize 2 k25, gjCheck 256 2 (x2KeyTypes 2 k25 0) (x2KeyTypes 2 k25 1) (x2KeyTypes 2 k25 2) (x2KeyMult 2 k25 0) (x2KeyMult 2 k25 1) (x2KeyMult 2 k25 2) (x2JCols (x2KeyGlobal 2 k25) d) (gj316.getD d 0) = true := by
  have hr : x2KeySize 2 k25 = 8 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 5 6 1 10 11 (x2JCols 316 d) (gj316.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 5 6 1 10 11 (x2JCols 316 d) (gj316.getD d 0)) 0 8 gjc25_0 d (Nat.zero_le d) (by omega)
x2_v_cols v316 gj316 316 256 110
theorem vc25_0 : (List.range 8).all (fun c => vCheck 256 110 8 gj316 (x2Trial_316.getD (0 + c) 0) (v316.getD (0 + c) 0)) = true := by decide +kernel
theorem vok25 : ∀ c < 8, vCheck 256 (x2KeyMult 2 k25 0 * x2KeyMult 2 k25 1 * x2KeyMult 2 k25 2) (x2KeySize 2 k25) gj316 (x2Trial_316.getD c 0) (v316.getD c 0) = true := by
  intro c hc
  show vCheck 256 110 8 gj316 (x2Trial_316.getD c 0) (v316.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 110 8 gj316 (x2Trial_316.getD c 0) (v316.getD c 0)) 0 8 vc25_0 c (Nat.zero_le c) (by omega)
theorem small25 : x2KeyDegree 2 k25 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k25 0 ∧ 1 ≤ x2KeyMult 2 k25 1 ∧ 1 ≤ x2KeyMult 2 k25 2 ∧ glRowOK 2 (x2KeyTypes 2 k25 0) (x2KeyMult 2 k25 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k25 1) (x2KeyMult 2 k25 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k25 2) (x2KeyMult 2 k25 2) 512 = true ∧ gj316.length = x2KeySize 2 k25 ∧ x2KeySize 2 k25 ≤ 512 ∧ v316.length = 8 := by decide +kernel
theorem chk25 : trialKeyChk 2 k25 8 gj316 x2Trial_316 v316 :=
  trialKeyChk_intro 2 k25 8 gj316 x2Trial_316 v316 small25 gjok25 vok25

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k25, ibFS [(v316, v316, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 5, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN25 : N k25 = x2TrialForm 2 k25) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 5 * x2Mult 2 6) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k25 8 _ gj316 x2Trial_316 v316 (by decide) (by rw [hN25]; exact trialForm_eq 2 k25 8 x2Trial_316 (by decide) rfl) chk25

end ThreeCopyQutritWerner.X2.InK2x056
