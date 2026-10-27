module

public import Certificates.Kernel.HS3850.Q25551
public import Certificates.Kernel.HS3850.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KD.LQT.C4126 CFSG.KD.LQT.HN
open CFSG.EvenSporadicStandard.TwoHS

@[expose] noncomputable def sW : Nat := wfoldR lc1 s6WWord

@[expose] noncomputable def sW2 : Nat := pc sW sW

@[expose] noncomputable def sW3 : Nat := pc sW2 sW

@[expose] noncomputable def sX : Nat := wfoldR lc1 s6XWord

@[expose] noncomputable def isWK (y : Nat) : Bool :=
  Nat.beq y idn || Nat.beq y sW || Nat.beq y sW2 || Nat.beq y sW3

@[expose] noncomputable def sF (z g0 g1 y : Nat) : Bool :=
  bAnd(bIf(bAnd(ptc y g0, ptc y g1), bIf(bAnd(cmK y g0, cmK y g1), isWK y, true), true),
    bIf(bAnd(ptc2 z y g0, ptc2 z y g1), strictB (pc z y) (fun zy =>
      bIf(bAnd(cmK zy g0, cmK zy g1), isWK zy, true)), true))

@[expose] noncomputable def ptS (i : Nat) : Bool := strictB (A.T i) (fun y => sF (FT.F 0) q1A q1B y)

@[expose] noncomputable def ckS (s : Nat) : Bool :=
  allN 32 (fun d => strictB (Nat.add (Nat.mul s (nat_lit 32)) d) (fun i =>
    bIf(Nat.blt i (nat_lit 7680), ptS i, true)))

theorem ok25950 : bAnd(Nat.beq sW2 (HC.F 5), bAnd(Nat.beq (pc sX sX) idn,
    bAnd(Nat.beq (pc sX sW) (pc sW3 sX),
    bAnd(Nat.beq (fx (HC.F 5)) 170, bAnd(Nat.beq (fx (HC.F 12)) 30,
    bAnd(Nat.beq (fx sX) 170, bAnd(Nat.beq (fx (pc sX (HC.F 5))) 170,
    bAnd(Nat.beq (fx (pc sX sW)) 30, bAnd(Nat.beq (fx cvX) 170,
      Nat.beq (fx (wfoldR ls8 (s6CWord.map Int.toNat))) 30))))))))) = true := by
  quickRfl

end CFSG.KD.HS3850

end
