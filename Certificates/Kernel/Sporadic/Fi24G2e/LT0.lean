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

@[expose] def l0C (j : Nat) : Bool :=
  permLOK FLC0 (brayWalk CFSG.KD.Fi24Fix.TG LWC0 (LWL0 j) (LEN0 j) (Nat.beq (LON0 j) 1)) (TB0 j) 504

@[expose] def o0C (t : Nat) : Bool :=
  Nat.beq (brayWalk CFSG.KD.Fi24Fix.TG LWC0 (LWL0 (t / 4)) (LEN0 (t / 4)) (Nat.beq (LON0 (t / 4)) 1)
    (OWN0.getD (t % 4) 0)) (OWV0.getD t 0)

@[expose] def i0C (k : Nat) : Bool := invLOK (TB0 k) (TI0 k) 504

@[expose] def n0C (t : Nat) : Bool :=
  cmLOK (TB0 (NODE.getD (2 * t) 0)) (TI0 (NODE.getD (2 * t) 0))
    (TB0 (NODE.getD (2 * t + 1) 0)) (TI0 (NODE.getD (2 * t + 1) 0)) (TB0 (t + 6)) 504

theorem LT0.cnt : Nat.beq (cntId (TB0 20) 504) 4 = true := by quickRfl

end CFSG.KD.Fi24G2e

#kss_each CFSG.KD.Fi24G2e.LT0.L CFSG.KD.Fi24G2e.l0C 6

#kss_each CFSG.KD.Fi24G2e.LT0.O CFSG.KD.Fi24G2e.o0C 24

#kss_each CFSG.KD.Fi24G2e.LT0.I CFSG.KD.Fi24G2e.i0C 21

#kss_each CFSG.KD.Fi24G2e.LT0.N CFSG.KD.Fi24G2e.n0C 15

end
