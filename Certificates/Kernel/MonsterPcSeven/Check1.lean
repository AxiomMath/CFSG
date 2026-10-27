module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcSeven
public import Certificates.Kernel.MonsterPcSeven.Data

public section

namespace CFSG.KC.MonPcSevenD

open CFSG.KC.MonPcSeven

theorem m7census1 :
    ∀ k < 7, chunkOK rep 432 (2401 * (7 + k)) (chunks.getD (7 + k) []) = true := by
  decide +kernel

end CFSG.KC.MonPcSevenD

end
