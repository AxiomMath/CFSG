module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcSeven
public import Certificates.Kernel.MonsterPcSeven.Data

public section

namespace CFSG.KC.MonPcSevenD

open CFSG.KC.MonPcSeven

theorem m7census2 :
    ∀ k < 7, chunkOK rep 432 (2401 * (14 + k)) (chunks.getD (14 + k) []) = true := by
  decide +kernel

end CFSG.KC.MonPcSevenD

end
