module

public import Certificates.Kernel.HS3850.F25371
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.OddFixData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KD.LQT.C4126 CFSG.KD.LQT.HN
open CFSG.EvenSporadicStandard.TwoHS

@[expose] noncomputable def q1A : Nat := wfoldR lc1 hsOdd1WordA

@[expose] noncomputable def q1B : Nat := wfoldR lc1 hsOdd1WordB

@[expose] noncomputable def ptc (x g : Nat) : Bool := Nat.beq (img x (img g 0)) (img g (img x 0))

@[expose] noncomputable def ptc2 (w x g : Nat) : Bool :=
  Nat.beq (img w (img x (img g 0))) (img g (img w (img x 0)))

@[expose] noncomputable def qF (w g0 g1 x : Nat) : Bool :=
  bAnd(bIf(bAnd(ptc x g0, ptc x g1), bIf(bAnd(cmK x g0, cmK x g1), sqK (pc x x), true), true),
    bIf(bAnd(ptc2 w x g0, ptc2 w x g1), strictB (pc w x) (fun wx =>
      bIf(bAnd(cmK wx g0, cmK wx g1), sqK (pc wx wx), true)), true))

@[expose] noncomputable def ptQ25551 (i : Nat) : Bool := strictB (A.T i) (fun x => qF (FT.F 0) q1A q1B x)

@[expose] noncomputable def ckQ (s : Nat) : Bool :=
  allN 32 (fun d => strictB (Nat.add (Nat.mul s (nat_lit 32)) d) (fun i =>
    bIf(Nat.blt i (nat_lit 7680), ptQ25551 i, true)))

theorem ok25551 : strictB q1A (fun A => strictB q1B (fun B =>
    bAnd(Nat.beq (wfoldR (fun _ => A) (List.replicate 5 0)) idn,
    bAnd(Nat.beq (wfoldR (fun _ => B) (List.replicate 5 0)) idn,
      Nat.beq (wfoldR (fun _ => pc A B) (List.replicate 10 0)) (HC.F 5))))) = true := by
  quickRfl

end CFSG.KD.HS3850

end
