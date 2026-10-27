module

public import Certificates.Kernel.Misc.OmegaSix.Rec
public import Certificates.Data.Kernel.Misc.OmegaSixO
public import Certificates.Data.Foote82OmegaSixNorm
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Eval
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Misc.OmegaSix.TransGen

public section

set_option maxRecDepth 400000

#kc_eval CFSG.KD.OmegaSix.Trans TT CFSG.KD.OmegaSix.Trans.stepT

namespace CFSG.KD.OmegaSix.Trans

open CFSG.KD.OmegaSix CFSG.KD.BfsK CFSG.CGT.Foote82.OmegaSix
open CFSG.KLie.CT (notB)

@[expose] noncomputable def witK (p : List Nat) : Bool :=
  Nat.blt (p.getD 1 0) 25920 && Nat.beq (colK (recX RO 10 (p.getD 1 0)) 4) (p.getD 0 0)

theorem kTW : TT.TW.all witK = true := by quickRfl

theorem kNS : ((List.range 64).all fun n => !(q6 (cvec n) == 1) ||
    TT.TW.any fun p => p.getD 0 0 == n) = true := by decide +kernel

theorem negTW : notB (witK [(TT.TW.getD 0 []).getD 0 0, (TT.TW.getD 0 []).getD 1 0 + 1]) = true := by
  quickRfl

theorem negNS : notB (q6 (cvec 0) == 1) = true := by decide +kernel

end CFSG.KD.OmegaSix.Trans

end
