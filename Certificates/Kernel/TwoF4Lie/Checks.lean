module

public import Certificates.Kernel.TwoF4Lie.Data
public import Certificates.Data.Kernel.TwoF4LieK
public import Certificates.Kernel.SporSch.Tits.Action2262
public import Certificates.Kernel.SporSch.Tits.Common
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTwoF4Lie

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KD.TwoF4Lie CertificateChecks.KernelMisc
open CertificateChecks.KernelSporSch.TitsAction CertificateChecks.KernelSporSch

@[expose] noncomputable def F (h : Nat) : Nat := TitsText.F h

@[expose] noncomputable def nodes : List Nat :=
  nodeOf r0 :: nodeOf r1 :: fN.map nodeOf

theorem invG : allN 4 (fun h => permOK 1755 11 (mask 11) (1755 * 11) (F h) (TGI h)) = true := by
  quickRfl

theorem sGen : allL (fun j w => bAnd(Nat.beq (TS j) (wN F TGI w), stabS lpK (gp (TS j)))) sW 0 =
    true := by quickRfl

theorem tc : bAnd(Nat.beq (TTC 0) (wN F TGI tW), Nat.beq (TTC 1) (wN F TGI cW)) = true := by
  quickRfl

theorem treeA : treeK TA TS aR = true := by quickRfl

theorem ugB : ugK TA TS TU uG = true := by quickRfl

theorem treeB : treeK TB TU bR = true := by quickRfl

theorem fixB : allN 64 (fun j => fixAll (TB j) (base.take 4)) = true := by quickRfl

theorem distA : distK (fun i => keyK (TA i) (base.take 4)) 64 = true := by quickRfl

theorem distB : distK (fun j => keyK (TB j) (base.drop 4)) 64 = true := by quickRfl

theorem cov0 : covK TA TB nodes (aC.take 32) 0 = true := by quickRfl

theorem cov1 : covK TA TB nodes (aC.drop 32) 32 = true := by quickRfl

theorem roots : bAnd(Nat.beq (mul (TA (r0.headD 0)) (TB (r0.tail.headD 0))) TitsZ,
    Nat.beq (mul (TA (r1.headD 0)) (TB (r1.tail.headD 0))) (TTC 0)) = true := by quickRfl

theorem for0 : forK F TGI TA TB lpK base (fN.take 71) [nodeOf r1, nodeOf r0] = true := by
  quickRfl

theorem for1 : forK F TGI TA TB lpK base (fN.drop 71)
    (((fN.take 71).map nodeOf).reverse ++ [nodeOf r1, nodeOf r0]) = true := by quickRfl

theorem tFacts : bAnd(Nat.beq (mul (TTC 0) (TTC 0)) idP, bAnd(bIf(Nat.beq (TTC 0) idP, false, true),
    bAnd(Nat.beq (fixCnt (TTC 0)) 27, Nat.beq (fixCnt TitsZ) 91))) = true := by quickRfl

theorem cFacts : bAnd(Nat.beq (mul (TTC 1) (mul (TTC 1) (TTC 1))) idP,
    bAnd(bIf(Nat.beq (TTC 1) idP, false, true),
      Nat.beq (mul (TTC 1) (TTC 0)) (mul (TTC 0) (TTC 1)))) = true := by quickRfl

theorem pfl : pflK lpK (TTC 0) pflL = true := by quickRfl

end CertificateChecks.KernelTwoF4Lie

end
