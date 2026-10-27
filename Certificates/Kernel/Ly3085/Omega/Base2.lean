module

public import Certificates.Kernel.Ly3085.Omega.Data
public import Certificates.Kernel.Ly3085.Omega.O1Data
public import Certificates.Kernel.Ly3085.Omega.FibData
public import Certificates.Kernel.Ly3085.Omega.SwData
public import Certificates.Kernel.Ly3085.Omega.HData
public import Certificates.Data.Kernel.LyOmega.Base
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.LyOm

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop

@[expose] noncomputable def GP2 : Nat → Nat := pickL [P0, P1, PI0, PI1]

@[expose] noncomputable def GR2 : Nat → Nat := pickL [R0, R1, Q0, Q1]

@[expose] noncomputable def PW (w : List Nat) : Nat := fWord BC GP2 BC.ONEF (List.reverse w)

@[expose] noncomputable def hMaps (KS : List Nat) (m : Nat) (ws : List (List Nat)) : Bool :=
  bAnd(Nat.beq m (List.length ws),
    (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun w _ ih k => bAnd(kronOK SC.ONE (sWord SC GR2 SC.ONE w) (pickL KS k), ih (Nat.succ k))) ws) 0)

theorem o1pi : tabPI BC LyO1.PI LyO1.PJ LyO1.nc = true := by quickRfl
theorem o1gt0 : tabGT BC LyO1.PI LyO1.GT P0 P1 LyO1.nc 0 32 = true := by quickRfl
theorem o1gt1 : tabGT BC LyO1.PI LyO1.GT P0 P1 LyO1.nc 32 32 = true := by quickRfl
theorem o1gt2 : tabGT BC LyO1.PI LyO1.GT P0 P1 LyO1.nc 64 32 = true := by quickRfl
theorem o1gt3 : tabGT BC LyO1.PI LyO1.GT P0 P1 LyO1.nc 96 32 = true := by quickRfl
theorem o1wc : tabWC BC LyO1.PI LyO1.WC LyO1.nc = true := by quickRfl
theorem o1xa : tabX BC LyO1.PI LyO1.TA PTA LyO1.nc = true := by quickRfl
theorem o1xb : tabX BC LyO1.PI LyO1.TB PTB LyO1.nc = true := by quickRfl
theorem o1xt : tabX BC LyO1.PI LyO1.TT PTT LyO1.nc = true := by quickRfl
theorem o1xy : tabX BC LyO1.PI LyO1.YB PYB LyO1.nc = true := by quickRfl
theorem o1root : rootOK BC LyO1.KX LyO1.PT LyO1.PI (bMul BC UT1 T) = true := by quickRfl

theorem f3pi : tabPI BC LyF3.PI LyF3.PJ LyF3.nc = true := by quickRfl
theorem f3gt : tabGT BC LyF3.PI LyF3.GT (PW WF3_0) (PW WF3_1) LyF3.nc 0 128 = true := by quickRfl
theorem f3wc : tabWC BC LyF3.PI LyF3.WC LyF3.nc = true := by quickRfl
theorem f3root : rootOK BC LyF3.KX LyF3.PT LyF3.PI (bMul BC UT3 T) = true := by quickRfl
theorem f3fix0 : rootFix BC LyF3.KX LyF3.PT LyF3.PI LyF3.PJ GP2 WH3_0 = true := by quickRfl
theorem f3fix1 : rootFix BC LyF3.KX LyF3.PT LyF3.PI LyF3.PJ GP2 WH3_1 = true := by quickRfl
theorem f3fix2 : rootFix BC LyF3.KX LyF3.PT LyF3.PI LyF3.PJ GP2 WH3_2 = true := by quickRfl

theorem f4pi : tabPI BC LyF4.PI LyF4.PJ LyF4.nc = true := by quickRfl
theorem f4gt : tabGT BC LyF4.PI LyF4.GT (PW WF4_0) (PW WF4_1) LyF4.nc 0 128 = true := by quickRfl
theorem f4wc : tabWC BC LyF4.PI LyF4.WC LyF4.nc = true := by quickRfl
theorem f4root : rootOK BC LyF4.KX LyF4.PT LyF4.PI (bMul BC UT4 T) = true := by quickRfl
theorem f4fix0 : rootFix BC LyF4.KX LyF4.PT LyF4.PI LyF4.PJ GP2 WH4_0 = true := by quickRfl
theorem f4fix1 : rootFix BC LyF4.KX LyF4.PT LyF4.PI LyF4.PJ GP2 WH4_1 = true := by quickRfl
theorem f4fix2 : rootFix BC LyF4.KX LyF4.PT LyF4.PI LyF4.PJ GP2 WH4_2 = true := by quickRfl
theorem f4fix3 : rootFix BC LyF4.KX LyF4.PT LyF4.PI LyF4.PJ GP2 WH4_3 = true := by quickRfl

theorem s3 : bAnd(Nat.beq LyS3.m 2, bAnd(Nat.beq (pickL LyS3.KS 0) KQ0, bAnd(Nat.beq (pickL LyS3.KS 1) KQ1,
    Nat.beq (getRec LyS3.KX 539 0) BE3))) = true := by quickRfl
theorem s4 : bAnd(Nat.beq LyS4.m 2, bAnd(Nat.beq (pickL LyS4.KS 0) KQ0, bAnd(Nat.beq (pickL LyS4.KS 1) KQ1,
    Nat.beq (getRec LyS4.KX 539 0) BE4))) = true := by quickRfl

theorem h2 : bAnd(hMaps LyH2.KS LyH2.m [WH2_0, WH2_1],
    Nat.beq (getRec LyH2.KX 539 0) SC.ONE) = true := by quickRfl
theorem h3 : bAnd(hMaps LyH3.KS LyH3.m [WH3_0, WH3_1, WH3_2],
    Nat.beq (getRec LyH3.KX 539 0) SC.ONE) = true := by quickRfl
theorem h4 : bAnd(hMaps LyH4.KS LyH4.m [WH4_0, WH4_1, WH4_2, WH4_3],
    Nat.beq (getRec LyH4.KX 539 0) SC.ONE) = true := by quickRfl

end CFSG.KD.LyOm

end
