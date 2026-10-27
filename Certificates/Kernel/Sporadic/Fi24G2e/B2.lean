module

public import Certificates.Kernel.Sporadic.Fi24G2e.Data
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24G2e

@[expose] def lkC (k : Nat) : Bool :=
  Nat.beq (CFSG.KD.BrFi24.MUL (BX 0) (CFSG.KD.BrFi24.RB (k + 1))) (BX (k + 1))

@[expose] def skC (k : Nat) : Bool :=
  Nat.beq (CFSG.KD.BrFi24.MUL (BX (k + 1)) (BX (k + 1))) CFSG.KD.BrFi24.ONE

end CFSG.KD.Fi24G2e

#kss_each CFSG.KD.Fi24G2e.B2.L CFSG.KD.Fi24G2e.lkC 11

#kss_each CFSG.KD.Fi24G2e.B2.S CFSG.KD.Fi24G2e.skC 11

end
