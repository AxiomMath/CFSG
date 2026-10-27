module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcSeven
public import Certificates.Kernel.MonsterPcSeven.Data

public section

namespace CFSG.KC.MonPcSevenD

open CFSG.KC.MonPcSeven

theorem m7census4 :
    ∀ k < 7, chunkOK rep 432 (2401 * (28 + k)) (chunks.getD (28 + k) []) = true := by
  decide +kernel

end CFSG.KC.MonPcSevenD

end
