module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (4, 6, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x467
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k144 : x2Key 1 := ⟨144, by decide⟩
x2_gj_cols gj266 266 1 4 6 7 256
theorem gjc144_0 : (List.range 119).all (fun d => gjCheck 256 1 4 6 7 7 17 6 (x2JCols 266 (0 + d)) (gj266.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok144 : ∀ d < x2KeySize 1 k144, gjCheck 256 1 (x2KeyTypes 1 k144 0) (x2KeyTypes 1 k144 1) (x2KeyTypes 1 k144 2) (x2KeyMult 1 k144 0) (x2KeyMult 1 k144 1) (x2KeyMult 1 k144 2) (x2JCols (x2KeyGlobal 1 k144) d) (gj266.getD d 0) = true := by
  have hr : x2KeySize 1 k144 = 119 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 4 6 7 7 17 6 (x2JCols 266 d) (gj266.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 4 6 7 7 17 6 (x2JCols 266 d) (gj266.getD d 0)) 0 119 gjc144_0 d (Nat.zero_le d) (by omega)
x2_v_cols v266 gj266 266 256 714
theorem vc144_0 : (List.range 80).all (fun c => vCheck 256 714 119 gj266 (x2Trial_266.getD (0 + c) 0) (v266.getD (0 + c) 0)) = true := by decide +kernel
theorem vok144 : ∀ c < 80, vCheck 256 (x2KeyMult 1 k144 0 * x2KeyMult 1 k144 1 * x2KeyMult 1 k144 2) (x2KeySize 1 k144) gj266 (x2Trial_266.getD c 0) (v266.getD c 0) = true := by
  intro c hc
  show vCheck 256 714 119 gj266 (x2Trial_266.getD c 0) (v266.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 714 119 gj266 (x2Trial_266.getD c 0) (v266.getD c 0)) 0 80 vc144_0 c (Nat.zero_le c) (by omega)
theorem small144 : x2KeyDegree 1 k144 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k144 0 ∧ 1 ≤ x2KeyMult 1 k144 1 ∧ 1 ≤ x2KeyMult 1 k144 2 ∧ glRowOK 1 (x2KeyTypes 1 k144 0) (x2KeyMult 1 k144 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k144 1) (x2KeyMult 1 k144 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k144 2) (x2KeyMult 1 k144 2) 512 = true ∧ gj266.length = x2KeySize 1 k144 ∧ x2KeySize 1 k144 ≤ 512 ∧ v266.length = 80 := by decide +kernel
theorem chk144 : trialKeyChk 1 k144 80 gj266 x2Trial_266 v266 :=
  trialKeyChk_intro 1 k144 80 gj266 x2Trial_266 v266 small144 gjok144 vok144

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k144, ibFS [(v266, v266, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![4, 6, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN144 : N k144 = x2TrialForm 1 k144) :
    ∀ e ∈ ks, keyOK (x2Mult 1 4 * x2Mult 1 6 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k144 80 _ gj266 x2Trial_266 v266 (by decide) (by rw [hN144]; exact trialForm_eq 1 k144 80 x2Trial_266 (by decide) rfl) chk144

end ThreeCopyQutritWerner.X2.InK1x467
