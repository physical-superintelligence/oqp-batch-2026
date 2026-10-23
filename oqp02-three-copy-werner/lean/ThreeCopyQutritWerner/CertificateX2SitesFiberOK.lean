module

public import ThreeCopyQutritWerner.CertificateX2SitesCore

@[expose] public section


/-! Shape predicates checked by the kernel in small chunks.
`fiberOK F`: `F < 2^(48·513)` and every 48-bit digit of `F` lies in `[2^47 - 2^9, 2^47 + 2^9]`
(so every entry `ent 48 47 F k` has absolute value at most `2^9`); `rowOK r`: a weight row of
length 513 with entries below `2^26`. Only natural-number operations. -/

open scoped BigOperators

namespace ThreeCopyQutritWerner.X2Sites

open X2

def fiberOK (F : ℕ) : Bool :=
  Nat.blt F (2 ^ (48 * 513)) && (List.range 513).all fun k =>
    Nat.ble 140737488354816 (ext F 48 k) && Nat.ble (ext F 48 k) 140737488355840

def rowOK (r : List ℕ) : Bool :=
  r.length == 513 && r.all fun x => Nat.blt x (2 ^ 26)

theorem fiberOK_lt (F : ℕ) (h : fiberOK F = true) : F < 2 ^ (48 * 513) := by
  unfold fiberOK at h
  simp only [Bool.and_eq_true] at h
  exact Nat.blt_eq.mp h.1

theorem fiberOK_ent (F : ℕ) (h : fiberOK F = true) (k : ℕ) (hk : k < 513) :
    |ent 48 (48 - 1) F k| ≤ 2 ^ 9 := by
  unfold fiberOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨h1, h2⟩ := h.2 k hk
  have hlo := Nat.le_of_ble_eq_true h1
  have hhi := Nat.le_of_ble_eq_true h2
  have hd : ext F 48 k = dig 48 F k := by rw [ext_eq, dig, ← pow_mul]
  rw [hd] at hlo hhi
  have hlo' : (140737488354816 : ℤ) ≤ (dig 48 F k : ℤ) := by exact_mod_cast hlo
  have hhi' : (dig 48 F k : ℤ) ≤ (140737488355840 : ℤ) := by exact_mod_cast hhi
  show |(dig 48 F k : ℤ) - 2 ^ 47| ≤ 2 ^ 9
  have e1 : (2 : ℤ) ^ 47 = 140737488355328 := by norm_num
  have e2 : (2 : ℤ) ^ 9 = 512 := by norm_num
  rw [e1, e2, abs_le]
  constructor <;> omega

end ThreeCopyQutritWerner.X2Sites
