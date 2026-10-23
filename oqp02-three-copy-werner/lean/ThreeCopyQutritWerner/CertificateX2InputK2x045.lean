module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 4, 5) of sector 2, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK2x045
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k21 : x2Key 2 := ⟨21, by decide⟩
x2_gj_cols gj312 312 2 0 4 5 256
theorem gjc21_0 : (List.range 12).all (fun d => gjCheck 256 2 0 4 5 1 15 10 (x2JCols 312 (0 + d)) (gj312.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok21 : ∀ d < x2KeySize 2 k21, gjCheck 256 2 (x2KeyTypes 2 k21 0) (x2KeyTypes 2 k21 1) (x2KeyTypes 2 k21 2) (x2KeyMult 2 k21 0) (x2KeyMult 2 k21 1) (x2KeyMult 2 k21 2) (x2JCols (x2KeyGlobal 2 k21) d) (gj312.getD d 0) = true := by
  have hr : x2KeySize 2 k21 = 12 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 2 0 4 5 1 15 10 (x2JCols 312 d) (gj312.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 2 0 4 5 1 15 10 (x2JCols 312 d) (gj312.getD d 0)) 0 12 gjc21_0 d (Nat.zero_le d) (by omega)
x2_v_cols v312 gj312 312 256 150
theorem vc21_0 : (List.range 8).all (fun c => vCheck 256 150 12 gj312 (x2Trial_312.getD (0 + c) 0) (v312.getD (0 + c) 0)) = true := by decide +kernel
theorem vok21 : ∀ c < 8, vCheck 256 (x2KeyMult 2 k21 0 * x2KeyMult 2 k21 1 * x2KeyMult 2 k21 2) (x2KeySize 2 k21) gj312 (x2Trial_312.getD c 0) (v312.getD c 0) = true := by
  intro c hc
  show vCheck 256 150 12 gj312 (x2Trial_312.getD c 0) (v312.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 150 12 gj312 (x2Trial_312.getD c 0) (v312.getD c 0)) 0 8 vc21_0 c (Nat.zero_le c) (by omega)
theorem small21 : x2KeyDegree 2 k21 ≠ 2 ∧ 1 ≤ x2KeyMult 2 k21 0 ∧ 1 ≤ x2KeyMult 2 k21 1 ∧ 1 ≤ x2KeyMult 2 k21 2 ∧ glRowOK 2 (x2KeyTypes 2 k21 0) (x2KeyMult 2 k21 0) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k21 1) (x2KeyMult 2 k21 1) 512 = true ∧ glRowOK 2 (x2KeyTypes 2 k21 2) (x2KeyMult 2 k21 2) 512 = true ∧ gj312.length = x2KeySize 2 k21 ∧ x2KeySize 2 k21 ≤ 512 ∧ v312.length = 8 := by decide +kernel
theorem chk21 : trialKeyChk 2 k21 8 gj312 x2Trial_312 v312 :=
  trialKeyChk_intro 2 k21 8 gj312 x2Trial_312 v312 small21 gjok21 vok21

noncomputable def ks : List (x2Key 2 × List (ℕ × ℕ × ℕ)) := [(k21, ibFS [(v312, v312, 94810963968000)])]
theorem hks : ∀ k : x2Key 2, x2KeyTypes 2 k = ![0, 4, 5] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 2) (hN21 : N k21 = x2TrialForm 2 k21) :
    ∀ e ∈ ks, keyOK (x2Mult 2 0 * x2Mult 2 4 * x2Mult 2 5) 2 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 2 N k21 8 _ gj312 x2Trial_312 v312 (by decide) (by rw [hN21]; exact trialForm_eq 2 k21 8 x2Trial_312 (by decide) rfl) chk21

end ThreeCopyQutritWerner.X2.InK2x045
