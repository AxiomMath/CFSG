module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcSeven
public import Certificates.Kernel.MonsterPcSeven.Data

public section

namespace CFSG.KC.MonPcSevenD

open CFSG.KC.MonPcSeven

theorem m7census0 :
    ∀ k < 7, chunkOK rep 432 (2401 * (0 + k)) (chunks.getD (0 + k) []) = true := by
  decide +kernel

end CFSG.KC.MonPcSevenD

end
