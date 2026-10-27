module

public import Certificates.Kernel.Sporadic.Fi24G2e.LData
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24G2e

open CFSG.KC.Fi24G2e

@[expose] def l1C (j : Nat) : Bool :=
  permLOK FLC1 (brayWalk CFSG.KD.Fi24Fix.TG LWC1 (LWL1 j) (LEN1 j) (Nat.beq (LON1 j) 1)) (TB1 j) 696

@[expose] def o1C (t : Nat) : Bool :=
  Nat.beq (brayWalk CFSG.KD.Fi24Fix.TG LWC1 (LWL1 (t / 3)) (LEN1 (t / 3)) (Nat.beq (LON1 (t / 3)) 1)
    (OWN1.getD (t % 3) 0)) (OWV1.getD t 0)

@[expose] def i1C (k : Nat) : Bool := invLOK (TB1 k) (TI1 k) 696

@[expose] def n1C (t : Nat) : Bool :=
  cmLOK (TB1 (NODE.getD (2 * t) 0)) (TI1 (NODE.getD (2 * t) 0))
    (TB1 (NODE.getD (2 * t + 1) 0)) (TI1 (NODE.getD (2 * t + 1) 0)) (TB1 (t + 6)) 696

theorem LT1.cnt : Nat.beq (cntId (TB1 20) 696) 8 = true := by quickRfl

end CFSG.KD.Fi24G2e

#kss_each CFSG.KD.Fi24G2e.LT1.L CFSG.KD.Fi24G2e.l1C 6

#kss_each CFSG.KD.Fi24G2e.LT1.O CFSG.KD.Fi24G2e.o1C 18

#kss_each CFSG.KD.Fi24G2e.LT1.I CFSG.KD.Fi24G2e.i1C 21

#kss_each CFSG.KD.Fi24G2e.LT1.N CFSG.KD.Fi24G2e.n1C 15

end
