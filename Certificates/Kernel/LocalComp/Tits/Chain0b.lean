module

public import Certificates.Kernel.LocalComp.Tits.ChainData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

public section

namespace CertificateChecks.KernelLC.Tits

theorem s0_14 : schC 0 14 = true := by quickRfl
theorem s0_15 : schC 0 15 = true := by quickRfl
theorem s0_16 : schC 0 16 = true := by quickRfl
theorem s0_17 : schC 0 17 = true := by quickRfl
theorem s0_18 : schC 0 18 = true := by quickRfl
theorem s0_19 : schC 0 19 = true := by quickRfl
theorem s0_20 : schC 0 20 = true := by quickRfl
theorem s0_21 : schC 0 21 = true := by quickRfl
theorem s0_22 : schC 0 22 = true := by quickRfl
theorem s0_23 : schC 0 23 = true := by quickRfl
theorem s0_24 : schC 0 24 = true := by quickRfl
theorem s0_25 : schC 0 25 = true := by quickRfl
theorem s0_26 : schC 0 26 = true := by quickRfl
theorem s0_27 : schC 0 27 = true := by quickRfl

theorem sch0b : ∀ c < 14, schC 0 (c + 14) = true
  | 0, _ => s0_14
  | 1, _ => s0_15
  | 2, _ => s0_16
  | 3, _ => s0_17
  | 4, _ => s0_18
  | 5, _ => s0_19
  | 6, _ => s0_20
  | 7, _ => s0_21
  | 8, _ => s0_22
  | 9, _ => s0_23
  | 10, _ => s0_24
  | 11, _ => s0_25
  | 12, _ => s0_26
  | 13, _ => s0_27
  | _ + 14, h => absurd h (by omega)

end CertificateChecks.KernelLC.Tits
