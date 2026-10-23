module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 2, 7) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x027
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k15 : x2Key 1 := ⟨15, by decide⟩
x2_gj_cols gj137 137 1 0 2 7 256
theorem gjc15_0 : (List.range 2).all (fun d => gjCheck 256 1 0 2 7 1 2 6 (x2JCols 137 (0 + d)) (gj137.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok15 : ∀ d < x2KeySize 1 k15, gjCheck 256 1 (x2KeyTypes 1 k15 0) (x2KeyTypes 1 k15 1) (x2KeyTypes 1 k15 2) (x2KeyMult 1 k15 0) (x2KeyMult 1 k15 1) (x2KeyMult 1 k15 2) (x2JCols (x2KeyGlobal 1 k15) d) (gj137.getD d 0) = true := by
  have hr : x2KeySize 1 k15 = 2 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 2 7 1 2 6 (x2JCols 137 d) (gj137.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 2 7 1 2 6 (x2JCols 137 d) (gj137.getD d 0)) 0 2 gjc15_0 d (Nat.zero_le d) (by omega)
x2_v_cols v137 gj137 137 256 12
theorem vc15_0 : (List.range 1).all (fun c => vCheck 256 12 2 gj137 (x2Trial_137.getD (0 + c) 0) (v137.getD (0 + c) 0)) = true := by decide +kernel
theorem vok15 : ∀ c < 1, vCheck 256 (x2KeyMult 1 k15 0 * x2KeyMult 1 k15 1 * x2KeyMult 1 k15 2) (x2KeySize 1 k15) gj137 (x2Trial_137.getD c 0) (v137.getD c 0) = true := by
  intro c hc
  show vCheck 256 12 2 gj137 (x2Trial_137.getD c 0) (v137.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 12 2 gj137 (x2Trial_137.getD c 0) (v137.getD c 0)) 0 1 vc15_0 c (Nat.zero_le c) (by omega)
theorem small15 : x2KeyDegree 1 k15 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k15 0 ∧ 1 ≤ x2KeyMult 1 k15 1 ∧ 1 ≤ x2KeyMult 1 k15 2 ∧ glRowOK 1 (x2KeyTypes 1 k15 0) (x2KeyMult 1 k15 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k15 1) (x2KeyMult 1 k15 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k15 2) (x2KeyMult 1 k15 2) 512 = true ∧ gj137.length = x2KeySize 1 k15 ∧ x2KeySize 1 k15 ≤ 512 ∧ v137.length = 1 := by decide +kernel
theorem chk15 : trialKeyChk 1 k15 1 gj137 x2Trial_137 v137 :=
  trialKeyChk_intro 1 k15 1 gj137 x2Trial_137 v137 small15 gjok15 vok15

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k15, ibFS [(v137, v137, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 2, 7] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN15 : N k15 = x2TrialForm 1 k15) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 2 * x2Mult 1 7) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k15 1 _ gj137 x2Trial_137 v137 (by decide) (by rw [hN15]; exact trialForm_eq 1 k15 1 x2Trial_137 (by decide) rfl) chk15

end ThreeCopyQutritWerner.X2.InK1x027
