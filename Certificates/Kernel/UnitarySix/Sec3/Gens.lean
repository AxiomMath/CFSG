module

public import Certificates.Kernel.UnitarySix.Sec3.GensChk
public import CFSG.Certificates.Kernel.U6Sec3Sound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 (gA)

theorem hG : ∀ k < 18, gA k = unpack 693 10 (sec3G k) := by
  intro k hk
  have hs : (gA k).size = 693 := by interval_cases k <;> decide +kernel
  refine unpack_eq_of_all hs ?_
  interval_cases k
  exacts [gEnt_0, gEnt_1, gEnt_2, gEnt_3, gEnt_4, gEnt_5, gEnt_6, gEnt_7, gEnt_8, gEnt_9,
    gEnt_10, gEnt_11, gEnt_12, gEnt_13, gEnt_14, gEnt_15, gEnt_16, gEnt_17]

theorem hidA : CFSG.Monster.B.Co2.Native.idA 693 = unpack 693 10 (pidn 693 10) := by
  refine unpack_eq_of_all (by simp [CFSG.Monster.B.Co2.Native.idA]) ?_
  decide +kernel

end CertificateChecks.KernelU6.Sec3
