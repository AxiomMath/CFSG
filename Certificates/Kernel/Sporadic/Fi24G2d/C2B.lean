module

public import Certificates.Kernel.Sporadic.Fi24G2d.Data
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.Fi24G2d

@[expose] def ok2B (c : Nat) : Bool :=
  Nat.beq (CFSG.KC.Fi24FixK.cntFix CFSG.KC.Fi24G2d.idN CFSG.KD.Fi24Fix.TG WN W2B (4096 * c) 4096 64)
    (K2B.getD c 0)

theorem C2B.last : Nat.beq (CFSG.KC.Fi24FixK.cntFix CFSG.KC.Fi24G2d.idN CFSG.KD.Fi24Fix.TG WN W2B
    0x4a000 0xef8 64) 0x20 = true := by
  quickRfl

end CFSG.KD.Fi24G2d

#kss_each CFSG.KD.Fi24G2d.C2B CFSG.KD.Fi24G2d.ok2B 74

end
