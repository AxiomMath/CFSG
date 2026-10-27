module

public import Certificates.Kernel.Sporadic.Fi24G2e.RData
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24G2e

@[expose] def yC (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG (GWL i) CFSG.KD.BrFi24.ONE) (YY i)

@[expose] def zC (i : Nat) : Bool := Nat.beq (CFSG.KD.BrFi24.MUL (REP i) (YY i)) (ZZ i)

end CFSG.KD.Fi24G2e

#kss_each CFSG.KD.Fi24G2e.RY.Y CFSG.KD.Fi24G2e.yC 7

#kss_each CFSG.KD.Fi24G2e.RY.Z CFSG.KD.Fi24G2e.zC 7

end
