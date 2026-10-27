module

public import Certificates.Data.Kernel.M23AutK
public import Certificates.Kernel.M23Aut.Data

public section

namespace CFSG.KD.M23Aut

open CFSG.KC.M23Aut

theorem ch7108_gidx : CFSG.KC.Enum.allN hN (fun i => Nat.blt (fl hG 4 i) 2) = true ∧
    CFSG.KC.Enum.allN iN (fun i => Nat.blt (fl iG 4 i) 2) = true ∧
    CFSG.KC.Enum.allN lN (fun i => Nat.blt (fl lG 4 i) 4) = true := by
  decide +kernel

end CFSG.KD.M23Aut

end
