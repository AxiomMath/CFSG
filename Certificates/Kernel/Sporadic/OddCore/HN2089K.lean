module

public import Certificates.Kernel.Sporadic.OddCore.HN2089D
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Sporadic.Schreier.ONPermArr
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HN2089

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNOddCore.InvData
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Monster.B.Co2.Native CFSG.KC.BfsPin CertificateChecks.KernelSpor.HND

@[expose] noncomputable def listPK (w : Nat) (P : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => bAnd(Nat.beq x (pg w (mask w) P i), ih (Nat.succ i))) L

@[expose] noncomputable def siP (g : Nat) : Nat := pinvS 800 10 (mask 10) (HQS g)

theorem sb : allN 11 (fun g => bAnd(Nat.beq (HNT.S4.E.getD g []).length 800,
    listPK 10 (HQS g) (HNT.S4.E.getD g []) 0)) = true := by quickRfl
theorem qb : allN 8 (fun g => bAnd(Nat.beq (HNT.QP.E.getD g []).length 800,
    listPK 10 (HQQ g) (HNT.QP.E.getD g []) 0)) = true := by quickRfl

theorem cS : allN 11 (fun g => canonK 800 10 (mask 10) (800 * 10) (HQS g)) = true := by quickRfl
theorem cSI : allN 11 (fun g => canonK 800 10 (mask 10) (800 * 10) (siP g)) = true := by quickRfl
theorem cQ : allN 8 (fun i => canonK 800 10 (mask 10) (800 * 10) (HQQ i)) = true := by quickRfl
theorem cB : allN 256 (fun m => canonK 800 10 (mask 10) (800 * 10) (HQB m)) = true := by quickRfl
theorem cI : canonK 800 10 (mask 10) (800 * 10) (pidn 800 10) = true := by quickRfl
theorem idk : idK 800 10 (mask 10) = true := by quickRfl

theorem pS : allN 11 (fun g => permOK 800 10 (mask 10) (800 * 10) (HQS g) (siP g)) = true := by
  quickRfl
theorem pK : allN 11 (fun g => permOK 256 9 (mask 9) (256 * 9) (HQK g)
    (pinvS 256 9 (mask 9) (HQK g))) = true := by quickRfl

theorem bb : allN 256 (fun m => Nat.beq ((List.range 8).foldl (fun acc i =>
    if m.testBit i then CFSG.KC.Enum.pcomp 800 10 (mask 10) acc (HQQ i) else acc) (pidn 800 10))
    (HQB m)) = true := by quickRfl

theorem kb : allN 11 (fun g => allN 256 (fun m => Nat.beq ((List.range 8).foldl (fun acc i =>
    if m.testBit i then acc ^^^ (qColumns[g]!)[i]! else acc) 0) (pg 9 (mask 9) (HQK g) m))) =
    true := by quickRfl

theorem wq : allN 8 (fun i => wordEqK 800 10 (mask 10) (pidn 800 10) HQS siP 11 QData.qFlat[i]!
    (HQQ i)) = true := by quickRfl

theorem cm : allN 8 (fun i => allN 8 (fun j =>
    Nat.beq (CFSG.KC.Enum.pcomp 800 10 (mask 10) (HQQ i) (HQQ j))
      (CFSG.KC.Enum.pcomp 800 10 (mask 10) (HQQ j) (HQQ i)))) = true := by quickRfl

theorem sq : allN 8 (fun i =>
    Nat.beq (CFSG.KC.Enum.pcomp 800 10 (mask 10) (HQQ i) (HQQ i)) (pidn 800 10)) = true := by
  quickRfl

theorem qb2 : allN 8 (fun i => allN 256 (fun m =>
    bAnd(Nat.blt (Nat.xor m (Nat.shiftLeft 1 i)) 256,
      Nat.beq (CFSG.KC.Enum.pcomp 800 10 (mask 10) (HQQ i) (HQB m))
        (HQB (Nat.xor m (Nat.shiftLeft 1 i)))))) = true := by quickRfl

theorem kc : allN 11 (fun g => allN 256 (fun m =>
    bAnd(Nat.blt (pg 9 (mask 9) (HQK g) m) 256,
      Nat.beq (CFSG.KC.Enum.pcomp 800 10 (mask 10) (siP g)
          (CFSG.KC.Enum.pcomp 800 10 (mask 10) (HQB m) (HQS g)))
        (HQB (pg 9 (mask 9) (HQK g) m))))) = true := by quickRfl

theorem hcv : allN 10 (fun j => Nat.beq (HQS (if j < 9 then j else 10)) (HQCV.S j)) = true := by
  quickRfl
theorem hqc : allN 8 (fun j => Nat.beq (HQQ j) (HQQC.S j)) = true := by quickRfl
theorem hkc : allN 11 (fun j => Nat.beq (HQK j) (HQKC.S j)) = true := by quickRfl

theorem pCV : allN 18 (fun j => permOK 800 10 (mask 10) (800 * 10) (HQCV.S j) (HQCV.SI j)) =
    true := by
  quickRfl
theorem pQC : allN 13 (fun j => permOK 800 10 (mask 10) (800 * 10) (HQQC.S j) (HQQC.SI j)) =
    true := by
  quickRfl
theorem pKC : allN 19 (fun j => permOK 256 9 (mask 9) (256 * 9) (HQKC.S j) (HQKC.SI j)) = true := by
  quickRfl

theorem bCV : allN 5 (fun t => Nat.beq (pg 10 (mask 10) HQCV.BP t)
    ((QData.cvBase.map Fin.val).toArray[t]!)) = true := by quickRfl
theorem bQC : allN 5 (fun t => Nat.beq (pg 10 (mask 10) HQQC.BP t)
    ((QData.qBase.map Fin.val).toArray[t]!)) = true := by quickRfl
theorem bKC : allN 5 (fun t => Nat.beq (pg 9 (mask 9) HQKC.BP t)
    ((QData.conjBase.map Fin.val).toArray[t]!)) = true := by quickRfl

end CertificateChecks.KernelSpor.HN2089

end
