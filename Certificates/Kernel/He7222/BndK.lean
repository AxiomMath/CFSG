module

public import Certificates.Kernel.He7222.FixK
public import Certificates.Kernel.He7222.CovK
public import Certificates.Data.Kernel.He7222.Cls
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow CFSG.KC.HeChain

theorem ch7222rt : (tupOK a0Ts (getLs a0RT 0) && tupOK a0Ts (getLs a0RT 1) &&
    tupOK a0Ts (getLs a0RT 2) && tupOK a0Ts (getLs a0RT 3) && tupOK a0Ts (getLs a0RT 4) &&
    tupOK t1Ts (getLs t1RT 0) && tupOK t1Ts (getLs t1RT 1) && tupOK t1Ts (getLs t1RT 2) &&
    tupOK t1Ts (getLs t1RT 3) && tupOK t1Ts (getLs t1RT 4) && tupOK t1Ts (getLs t1RT 5) &&
    tupOK t1Ts (getLs t1RT 6)) = true := by
  quickRfl

theorem ch7222cc : (allN 105 (fun i => Nat.blt (getS a0Cc i) 8330) &&
    allN 42 (fun i => Nat.blt (getS t1Cc i) 8330)) = true := by
  quickRfl

end CFSG.KD.He7222

end
