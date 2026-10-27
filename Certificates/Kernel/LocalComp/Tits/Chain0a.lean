module

public import Certificates.Kernel.LocalComp.Tits.ChainData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

public section

namespace CertificateChecks.KernelLC.Tits

theorem s0_00 : schC 0 0 = true := by quickRfl
theorem s0_01 : schC 0 1 = true := by quickRfl
theorem s0_02 : schC 0 2 = true := by quickRfl
theorem s0_03 : schC 0 3 = true := by quickRfl
theorem s0_04 : schC 0 4 = true := by quickRfl
theorem s0_05 : schC 0 5 = true := by quickRfl
theorem s0_06 : schC 0 6 = true := by quickRfl
theorem s0_07 : schC 0 7 = true := by quickRfl
theorem s0_08 : schC 0 8 = true := by quickRfl
theorem s0_09 : schC 0 9 = true := by quickRfl
theorem s0_10 : schC 0 10 = true := by quickRfl
theorem s0_11 : schC 0 11 = true := by quickRfl
theorem s0_12 : schC 0 12 = true := by quickRfl
theorem s0_13 : schC 0 13 = true := by quickRfl

theorem sch0a : ∀ c < 14, schC 0 c = true
  | 0, _ => s0_00
  | 1, _ => s0_01
  | 2, _ => s0_02
  | 3, _ => s0_03
  | 4, _ => s0_04
  | 5, _ => s0_05
  | 6, _ => s0_06
  | 7, _ => s0_07
  | 8, _ => s0_08
  | 9, _ => s0_09
  | 10, _ => s0_10
  | 11, _ => s0_11
  | 12, _ => s0_12
  | 13, _ => s0_13
  | _ + 14, h => absurd h (by omega)

end CertificateChecks.KernelLC.Tits
