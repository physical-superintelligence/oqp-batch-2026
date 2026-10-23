module

public import ThreeCopyQutritWerner.CertificateX2InputLab
public import ThreeCopyQutritWerner.CertificateX2InputTripGen
public import ThreeCopyQutritWerner.CertificateX2Images
public import ThreeCopyQutritWerner.CertificateX2FacesTrialData

@[expose] public section


/-! The keys of the sorted type triple (0, 3, 6) of sector 1, their checked columns and key facts. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

open scoped Matrix

namespace ThreeCopyQutritWerner.X2.InK1x036
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

def k20 : x2Key 1 := ⟨20, by decide⟩
x2_gj_cols gj142 142 1 0 3 6 256
theorem gjc20_0 : (List.range 25).all (fun d => gjCheck 256 1 0 3 6 1 9 17 (x2JCols 142 (0 + d)) (gj142.getD (0 + d) 0)) = true := by decide +kernel
theorem gjok20 : ∀ d < x2KeySize 1 k20, gjCheck 256 1 (x2KeyTypes 1 k20 0) (x2KeyTypes 1 k20 1) (x2KeyTypes 1 k20 2) (x2KeyMult 1 k20 0) (x2KeyMult 1 k20 1) (x2KeyMult 1 k20 2) (x2JCols (x2KeyGlobal 1 k20) d) (gj142.getD d 0) = true := by
  have hr : x2KeySize 1 k20 = 25 := by decide
  rw [hr]
  intro d hd
  show gjCheck 256 1 0 3 6 1 9 17 (x2JCols 142 d) (gj142.getD d 0) = true
  exact rangeAll_sound (fun d => gjCheck 256 1 0 3 6 1 9 17 (x2JCols 142 d) (gj142.getD d 0)) 0 25 gjc20_0 d (Nat.zero_le d) (by omega)
x2_nat_list K1x036k0c "verification/matrix-literals/x2-transfer/corr-light/K1x036k0.hex"
x2_nat_list A1x036k0c "verification/matrix-literals/x2-transfer/corr-light/A1x036k0.hex"
x2_vk_cols u142 gj142 K1x036k0c 256 153
x2_ua_cols ua142 u142 A1x036k0c 153 7
theorem cchk20 : corrKeyChk 1 k20 7 gj142 K1x036k0c u142 A1x036k0c ua142 := by
  have h1 : x2KeyDegree 1 k20 ≠ 2 ∧ 1 ≤ x2KeyMult 1 k20 0 ∧ 1 ≤ x2KeyMult 1 k20 1 ∧ 1 ≤ x2KeyMult 1 k20 2 ∧ glRowOK 1 (x2KeyTypes 1 k20 0) (x2KeyMult 1 k20 0) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k20 1) (x2KeyMult 1 k20 1) 512 = true ∧ glRowOK 1 (x2KeyTypes 1 k20 2) (x2KeyMult 1 k20 2) 512 = true ∧ gj142.length = x2KeySize 1 k20 ∧ x2KeySize 1 k20 ≤ 512 := by decide +kernel
  have h2 : ∀ c < 7, vCheck 256 (x2KeyMult 1 k20 0 * x2KeyMult 1 k20 1 * x2KeyMult 1 k20 2) (x2KeySize 1 k20) gj142 (K1x036k0c.getD c 0) (u142.getD c 0) = true ∧ slotBoundCheck 256 18 (x2KeyMult 1 k20 0 * x2KeyMult 1 k20 1 * x2KeyMult 1 k20 2) (u142.getD c 0) = true := by decide +kernel
  have h3 : u142.length = 7 ∧ ua142.length = 7 ∧ 7 ≤ 512 := by decide +kernel
  have h4 : ∀ c < 7, uaCheck (x2KeyMult 1 k20 0 * x2KeyMult 1 k20 1 * x2KeyMult 1 k20 2) 7 u142 (A1x036k0c.getD c 0) (ua142.getD c 0) = true := by decide +kernel
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h1
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, gjok20, h2, h3.1, h3.2.1, h3.2.2, h4⟩

noncomputable def ks : List (x2Key 1 × List (ℕ × ℕ × ℕ)) := [(k20, ibFS [(ua142, u142, 3)])]
theorem hks : ∀ k : x2Key 1, x2KeyTypes 1 k = ![0, 3, 6] ↔ k ∈ ks.map Prod.fst := by decide +kernel
theorem hnd : (ks.map Prod.fst).Nodup := by decide +kernel
theorem hlen : (ks.flatMap Prod.snd).length < 2 ^ 27 := by decide +kernel

theorem keys (N : X2Blocks 1) (hN20 : N k20 = x2CorrForm 1 k20 7 K1x036k0c A1x036k0c) :
    ∀ e ∈ ks, keyOK (x2Mult 1 0 * x2Mult 1 3 * x2Mult 1 6) 1 N e.1 e.2 := by
  intro e he
  simp only [ks, List.mem_singleton] at he
  subst he
  exact keyOK_of_corrChk 1 N k20 7 _ gj142 K1x036k0c u142 A1x036k0c ua142 (by decide) hN20 cchk20

end ThreeCopyQutritWerner.X2.InK1x036
