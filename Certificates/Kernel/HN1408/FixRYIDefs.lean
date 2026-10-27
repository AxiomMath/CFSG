module

public import Certificates.Kernel.HN1408.Words

public section

namespace CFSG.KD.HN1408.FixR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] noncomputable def yInvF (Y YI : Nat → Nat) (nY : Nat) : Bool :=
  allN nY fun k => strictB (YI k) fun B =>
    bAnd(canonK 1408 11 (mask 11) (1408 * 11) B, Nat.beq (pc (Y k) B) idK)

end CFSG.KD.HN1408.FixR

end
