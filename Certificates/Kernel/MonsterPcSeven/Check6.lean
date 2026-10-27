module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcSeven
public import Certificates.Kernel.MonsterPcSeven.Data

public section

namespace CFSG.KC.MonPcSevenD

open CFSG.KC.MonPcSeven

theorem m7census6 :
    ∀ k < 7, chunkOK rep 432 (2401 * (42 + k)) (chunks.getD (42 + k) []) = true := by
  decide +kernel

end CFSG.KC.MonPcSevenD

end
