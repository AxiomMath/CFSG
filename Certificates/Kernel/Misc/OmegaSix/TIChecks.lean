module

public import Certificates.Data.Kernel.Misc.OmegaSixTI
public import Certificates.Kernel.Misc.OmegaSix.Rec
public import Certificates.Kernel.Misc.OmegaSix.RecO
public import Certificates.Kernel.Misc.OmegaSix.TIGen
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.YamakiRepF CFSG.KD.BfsK
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def ch919010 (q : Nat) : Bool := tiChunk RO ROO TIW 512 q

@[expose] noncomputable def tiFirst : Nat := TIF 0

theorem negTI1 : (Nat.blt 0 tiFirst && bIf(tiWitK RO (recX ROO 3 tiFirst) (TIW tiFirst + 1),
    false, true)) = true := by quickRfl

theorem negTI2 : bIf(tiWitK RO (recX ROO 3 tiFirst) 0, false, true) = true := by quickRfl

theorem negTI3 : bIf(tiWitK RO ONE (TIW tiFirst), false, true) = true := by quickRfl

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919010K CFSG.KD.OmegaSix.ch919010 102

end
