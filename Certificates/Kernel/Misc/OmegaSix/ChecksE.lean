module

public import Certificates.Data.Foote82OmegaSix
public import Certificates.Data.Kernel.Misc.OmegaSixE
public import Certificates.Kernel.Misc.OmegaSix.Rec

public section

namespace CFSG.KD.OmegaSix

open CFSG.CGT.Foote82.OmegaSix
open CFSG.KD.Sp62 (ONE)

theorem involCheck_ok : involCheck () = true := by decide +kernel

theorem isomCheck_ok : isomCheck () = true := by decide +kernel

theorem commCheck_ok : commCheck () = true := by decide +kernel

theorem oRelM : ∀ w ∈ relators, Nat.beq (wordF6 RO w) ONE = true := by decide +kernel

end CFSG.KD.OmegaSix

end
