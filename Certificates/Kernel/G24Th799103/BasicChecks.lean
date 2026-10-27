module

public import Certificates.Kernel.G24Th799103.BasicData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24Th

open CFSG.KC.PCent CFSG.KC.Enum CFSG.KC.Misc.ArrEnum

theorem ch799103_bw : (allN 4 (fun k => permB 1365 11 (wT k) && inDK (wT k) &&
    commPt (wT k) (TG.F 2)) && Nat.beq (commP 1365 11 (wT 0) (wT 1)) (TG.F 0) &&
    Nat.beq (commP 1365 11 (wT 2) (wT 3)) (TG.F 1)) = true := by quickRfl

theorem ch799103_bc : (cubePt (TG.F 0) && cubePt (TG.F 1) && commPt (TG.F 0) (TG.F 1) &&
    !Nat.beq (TG.F 0) (pidn 1365 11) && !Nat.beq (TG.F 1) (pidn 1365 11) &&
    !Nat.beq (TG.F 1) (TG.F 0) && !Nat.beq (TG.F 1) (mulG (TG.F 0) (TG.F 0))) = true := by
  quickRfl

theorem ch799103_bsign : CFSG.KC.Pack.signK 1365 11 (CFSG.KS.mask 11) (TG.F 2) TT 651 = true := by
  quickRfl

theorem ch799103_be9 : allN 3 (fun a => allN 3 (fun b =>
    Nat.beq (e9 (Nat.add (Nat.mul 3 a) b)) (mulG (powG (TG.F 0) a) (powG (TG.F 1) b)))) = true := by
  quickRfl

theorem ch799103_bpd : (allN 2 (fun k => permB 1365 11 (pG k) && inDK (pG k)) &&
    allN 4 (fun k => permB 1365 11 (dK k) && inDK (dK k))) = true := by quickRfl

theorem ch799103_bpl : (mulRecK 1365 11 pG 2 PL && Nat.beq PL.length 27) = true := by quickRfl

theorem ch799103_bcl : allN 27 (fun i => allN 2 (fun k =>
    Nat.blt (CL.getD (Nat.add (Nat.mul 2 i) k) 0) 27 &&
    Nat.beq (mulG (pG k) (pL i)) (pL (CL.getD (Nat.add (Nat.mul 2 i) k) 0)))) = true := by
  quickRfl

theorem ch799103_bsq : allN 27 (fun i => Nat.blt (SQ.getD i 0) 27 &&
    Nat.beq (mulG (pL i) (pL i)) (pL (SQ.getD i 0)) &&
    Nat.beq (mulG (pL i) (pL (SQ.getD i 0))) (pidn 1365 11)) = true := by quickRfl

theorem ch799103_bcj : (Nat.blt PO 1365 && Nat.beq CJ.length 108 && allN 108 (fun t =>
    Nat.ble 9 (CJ.getD t 9) || (Nat.blt (CJ.getD t 9) 9 &&
      Nat.beq (conjP 1365 11 (dK (Nat.div t 27)) (pL (Nat.mod t 27))) (e9 (CJ.getD t 9))))) =
    true := by quickRfl

theorem ch799103_bpairs : pairsK CJ = true := by quickRfl

end CertificateChecks.KernelG24Th

end
