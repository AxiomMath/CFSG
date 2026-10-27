module

public import Certificates.Kernel.LocalComp.Tits.ChainData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

public section

namespace CertificateChecks.KernelLC.Tits

theorem s1_00 : schC 1 0 = true := by quickRfl
theorem s1_01 : schC 1 1 = true := by quickRfl
theorem s1_02 : schC 1 2 = true := by quickRfl
theorem s1_03 : schC 1 3 = true := by quickRfl
theorem s1_04 : schC 1 4 = true := by quickRfl
theorem s1_05 : schC 1 5 = true := by quickRfl
theorem s1_06 : schC 1 6 = true := by quickRfl
theorem s1_07 : schC 1 7 = true := by quickRfl
theorem s1_08 : schC 1 8 = true := by quickRfl
theorem s1_09 : schC 1 9 = true := by quickRfl
theorem s1_10 : schC 1 10 = true := by quickRfl
theorem s1_11 : schC 1 11 = true := by quickRfl
theorem s1_12 : schC 1 12 = true := by quickRfl
theorem s1_13 : schC 1 13 = true := by quickRfl
theorem s1_14 : schC 1 14 = true := by quickRfl
theorem s1_15 : schC 1 15 = true := by quickRfl

theorem sRest : ∀ i < 4, ∀ c < 28, (i = 1 ∧ 16 ≤ c) ∨ 2 ≤ i → schC i c = true := by
  decide +kernel

theorem sch1a : ∀ c < 16, schC 1 c = true
  | 0, _ => s1_00
  | 1, _ => s1_01
  | 2, _ => s1_02
  | 3, _ => s1_03
  | 4, _ => s1_04
  | 5, _ => s1_05
  | 6, _ => s1_06
  | 7, _ => s1_07
  | 8, _ => s1_08
  | 9, _ => s1_09
  | 10, _ => s1_10
  | 11, _ => s1_11
  | 12, _ => s1_12
  | 13, _ => s1_13
  | 14, _ => s1_14
  | 15, _ => s1_15
  | _ + 16, h => absurd h (by omega)

theorem sch1 (c : Nat) (hc : c < 28) : schC 1 c = true := by
  rcases Nat.lt_or_ge c 16 with h | h
  · exact sch1a c h
  · exact sRest 1 (by omega) c hc (Or.inl ⟨rfl, h⟩)

end CertificateChecks.KernelLC.Tits
