module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 2, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x025
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k13 : x2Key 2 := ⟨13, by decide⟩
x2_gj_cols gj304 304 2 0 2 5 256
theorem gjc13_0 : (List.range 6).all (fun d => gjCheck 256 2 0 2 5 1 5 10 (x2JCols 304 (0 + d)) (gj304.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok13 : ∀ d < x2KeySize 2 k13, gjCheck 256 2 (x2KeyTypes 2 k13 0) (x2KeyTypes 2 k13 1) (x2KeyTypes 2 k13 2) (x2KeyMult 2 k13 0) (x2KeyMult 2 k13 1) (x2KeyMult 2 k13 2) (x2JCols (x2KeyGlobal 2 k13) d) (gj304.getD d 0) = true := by
  have hr : x2KeySize 2 k13 = 6 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 2 5 1 5 10 (x2JCols 304 d) (gj304.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 2 5 1 5 10 (x2JCols 304 d) (gj304.getD d 0)) 0 6 gjc13_0 d (Nat.zero_le d) (by omega)
x2_v_cols v304 gj304 304 256 50
theorem vc13_0 : (List.range 3).all (fun c => vCheck 256 50 6 gj304 (x2Trial_304.getD (0 + c) 0) (v304.getD (0 + c) 0)) = true := by decide +kernel
theorem vok13 : ∀ c < 3, vCheck 256 (x2KeyMult 2 k13 0 * x2KeyMult 2 k13 1 * x2KeyMult 2 k13 2) (x2KeySize 2 k13) gj304 (x2Trial_304.getD c 0) (v304.getD c 0) = true := by
  intro c hc
  show vCheck 256 50 6 gj304 (x2Trial_304.getD c 0) (v304.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 50 6 gj304 (x2Trial_304.getD c 0) (v304.getD c 0)) 0 3 vc13_0 c (Nat.zero_le c) (by omega)
theorem small13 : x2KeyDegree 2 k13 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k13 0 ∧ 1 ≤ x2KeyMult 2 k13 1 ∧ 1 ≤ x2KeyMult 2 k13 2 ∧ glRowOK 2 (x2KeyTypes 2 k13 0) (x2KeyMult 2 k13 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k13 1) (x2KeyMult 2 k13 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k13 2) (x2KeyMult 2 k13 2) 512 = true ∧ gj304.length = x2KeySize 2 k13 ∧ x2KeySize 2 k13 ≤ 512 ∧ v304.length = 3 := by decide +kernel
theorem chk13 : trialKeyChk 2 k13 3 gj304 x2Trial_304 v304 :=
  trialKeyChk_intro 2 k13 3 gj304 x2Trial_304 v304 small13 gjok13 vok13

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k13, ibFS [(v304, v304, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 2, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN13 : N k13 = x2TrialForm 2 k13) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 2 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k13 3 _ gj304 x2Trial_304 v304 (by decide) (by rw [hN13]; exact trialForm_eq 2 k13 3 x2Trial_304 (by decide) rfl) chk13

end ThreeCopyQutritWerner.X2.InK2x025
