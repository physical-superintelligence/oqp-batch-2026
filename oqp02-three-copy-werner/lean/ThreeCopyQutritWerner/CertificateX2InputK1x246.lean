module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (2, 4, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x246
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k93 : x2Key 1 := ⟨93, by decide⟩
x2_gj_cols gj215 215 1 2 4 6 256
theorem gjc93_0 : (List.range 40).all (fun d => gjCheck 256 1 2 4 6 2 7 17 (x2JCols 215 (0 + d)) (gj215.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok93 : ∀ d < x2KeySize 1 k93, gjCheck 256 1 (x2KeyTypes 1 k93 0) (x2KeyTypes 1 k93 1) (x2KeyTypes 1 k93 2) (x2KeyMult 1 k93 0) (x2KeyMult 1 k93 1) (x2KeyMult 1 k93 2) (x2JCols (x2KeyGlobal 1 k93) d) (gj215.getD d 0) = true := by
  have hr : x2KeySize 1 k93 = 40 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 2 4 6 2 7 17 (x2JCols 215 d) (gj215.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 2 4 6 2 7 17 (x2JCols 215 d) (gj215.getD d 0)) 0 40 gjc93_0 d (Nat.zero_le d) (by omega)
x2_v_cols v215 gj215 215 256 238
theorem vc93_0 : (List.range 18).all (fun c => vCheck 256 238 40 gj215 (x2Trial_215.getD (0 + c) 0) (v215.getD (0 + c) 0)) = true := by decide +kernel
theorem vok93 : ∀ c < 18, vCheck 256 (x2KeyMult 1 k93 0 * x2KeyMult 1 k93 1 * x2KeyMult 1 k93 2) (x2KeySize 1 k93) gj215 (x2Trial_215.getD c 0) (v215.getD c 0) = true := by
  intro c hc
  show vCheck 256 238 40 gj215 (x2Trial_215.getD c 0) (v215.getD c 0) = true
  exact rangeAll_sound (fun c => vCheck 256 238 40 gj215 (x2Trial_215.getD c 0) (v215.getD c 0)) 0 18 vc93_0 c (Nat.zero_le c) (by omega)
theorem small93 : x2KeyDegree 1 k93 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k93 0 ∧ 1 ≤ x2KeyMult 1 k93 1 ∧ 1 ≤ x2KeyMult 1 k93 2 ∧ glRowOK 1 (x2KeyTypes 1 k93 0) (x2KeyMult 1 k93 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k93 1) (x2KeyMult 1 k93 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k93 2) (x2KeyMult 1 k93 2) 512 = true ∧ gj215.length = x2KeySize 1 k93 ∧ x2KeySize 1 k93 ≤ 512 ∧ v215.length = 18 := by decide +kernel
theorem chk93 : trialKeyChk 1 k93 18 gj215 x2Trial_215 v215 :=
  trialKeyChk_intro 1 k93 18 gj215 x2Trial_215 v215 small93 gjok93 vok93

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k93, ibFS [(v215, v215, 94810963968000)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![2, 4, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN93 : N k93 = x2TrialForm 1 k93) :
    ∀ e ∈ ks, keyOK (x2Mult 1 2 * x2Mult 1 4 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_trialChk 1 N k93 18 _ gj215 x2Trial_215 v215 (by decide) (by rw [hN93]; exact trialForm_eq 1 k93 18 x2Trial_215 (by decide) rfl) chk93

end ThreeCopyQutritWerner.X2.InK1x246
