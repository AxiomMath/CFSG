module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Data
public import Certificates.Data.Kernel.U6.Sec3Gens
public import Certificates.Data.Kernel.U6.F2K
public import Certificates.Data.Kernel.Spor.Prim

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 (gA)

@[expose] noncomputable def sec3G (k : ℕ) : ℕ := CFSG.KC.U6F2.getLD 0 sec3GL k

@[expose] noncomputable def gEnt (k : ℕ) : Bool :=
  (List.range 693).all fun i => Nat.beq (gA k)[i]! (pg 10 (mask 10) (sec3G k) i)

theorem gEnt_0 : gEnt 0 = true := by decide +kernel
theorem gEnt_1 : gEnt 1 = true := by decide +kernel
theorem gEnt_2 : gEnt 2 = true := by decide +kernel
theorem gEnt_3 : gEnt 3 = true := by decide +kernel
theorem gEnt_4 : gEnt 4 = true := by decide +kernel
theorem gEnt_5 : gEnt 5 = true := by decide +kernel
theorem gEnt_6 : gEnt 6 = true := by decide +kernel
theorem gEnt_7 : gEnt 7 = true := by decide +kernel
theorem gEnt_8 : gEnt 8 = true := by decide +kernel
theorem gEnt_9 : gEnt 9 = true := by decide +kernel
theorem gEnt_10 : gEnt 10 = true := by decide +kernel
theorem gEnt_11 : gEnt 11 = true := by decide +kernel
theorem gEnt_12 : gEnt 12 = true := by decide +kernel
theorem gEnt_13 : gEnt 13 = true := by decide +kernel
theorem gEnt_14 : gEnt 14 = true := by decide +kernel
theorem gEnt_15 : gEnt 15 = true := by decide +kernel
theorem gEnt_16 : gEnt 16 = true := by decide +kernel
theorem gEnt_17 : gEnt 17 = true := by decide +kernel

theorem hc : ∀ k < 18, canonK 693 10 (mask 10) (693 * 10) (sec3G k) = true := by decide +kernel

theorem hid : canonK 693 10 (mask 10) (693 * 10) (pidn 693 10) = true := by decide +kernel

end CertificateChecks.KernelU6.Sec3
