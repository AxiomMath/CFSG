module

public import Certificates.Kernel.SporSch.Ru.LData
public import Certificates.Kernel.SporSch.Ru.WitData
public import Certificates.Data.Kernel.SporSch.RuK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuMix

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch

@[expose] noncomputable def AK (i : Nat) : Nat := pcomp 4060 12 (mask 12) (RuW.LG 0) (RuLD.YT i)

@[expose] noncomputable def BK (i : Nat) : Nat := pcomp 4060 12 (mask 12) (AK i) (RuW.LGI 0)

@[expose] noncomputable def MK (i : Nat) : Nat := pcomp 4060 12 (mask 12) (RuLD.YT i) (BK i)

@[expose] noncomputable def prodK (i : Nat) : Bool :=
  bAnd(compEqK 4060 12 (mask 12) (4060 * 12) (RuW.LG 0) (RuLD.YT i) (AK i),
    bAnd(compEqK 4060 12 (mask 12) (4060 * 12) (AK i) (RuW.LGI 0) (BK i),
      compEqK 4060 12 (mask 12) (4060 * 12) (RuLD.YT i) (BK i) (MK i)))

theorem prod0 : prodK 0 = true := by quickRfl

theorem prod2 : prodK 2 = true := by quickRfl

theorem p13 : powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) (MK 2) 7 (pidn 4060 12) = true := by
  quickRfl

theorem n13 : neK 4060 12 (mask 12) (4060 * 12) (MK 2) (pidn 4060 12) = true := by quickRfl

theorem p5 : powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) (MK 0) 13 (pidn 4060 12) = true := by
  quickRfl

theorem n5 : neK 4060 12 (mask 12) (4060 * 12) (MK 0) (pidn 4060 12) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuMix

end
