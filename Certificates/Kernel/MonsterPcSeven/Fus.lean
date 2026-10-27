module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcSeven
public import Certificates.Kernel.MonsterPcSeven.Data

public section

namespace CFSG.KC.MonPcSevenD

open CFSG.KC.MonPcSeven

theorem m7phi : ∀ k < 7, phiOK (343 * k) 343 = true := by decide +kernel

theorem m7fus : fusOK rep 432 depth kind arg cls wit = true := by quickRfl

theorem m7len : ∀ k < 49, (chunks.getD k []).length = 2401 := by decide +kernel

end CFSG.KC.MonPcSevenD

end
