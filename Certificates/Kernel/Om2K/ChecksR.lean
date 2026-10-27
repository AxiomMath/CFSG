module

public import Certificates.Kernel.Om2K.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Holder1711.Om2Check
public import Certificates.Data.Kernel.BfsPin
public import Certificates.Data.Kernel.SetOrb

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check (wCc)
open CertificateChecks.KernelLC.E8 (FT)

theorem kEL : allN 7 (fun k => Nat.beq (EL.G k) (wYK (elW.getD k []))) = true := by quickRfl

theorem kCC : allN 5 (fun k => Nat.beq (CC.G k) (wYK (wCc.getD k []))) = true := by quickRfl

theorem kCRg : allN 2 (fun k => Nat.beq (CRG.G k) (wYK (wCR.getD k []))) = true := by quickRfl

theorem kOkE : allN 7 (fun k => okK (EL.G k)) = true := by quickRfl

theorem kOkC : allN 5 (fun k => okK (CC.G k)) = true := by quickRfl

theorem kOkR : allN 2 (fun k => okK (CRG.G k)) = true := by quickRfl

theorem kCA : allN 3 (fun k => okK (cAK k)) = true := by quickRfl

theorem kHF : CFSG.KLC.E8.homF FT = true := by quickRfl

theorem kNEG : canonK 240 8 (mask 8) (240 * 8) CertificateChecks.KernelLC.E8.NEG = true := by
  quickRfl

theorem kR1 : allN 240 (fun i => Nat.beq (pg 9 511 (EL.G 0) i) (pg 8 255 (FT 15) i)) = true := by
  quickRfl

theorem kR2 : Nat.beq (pc (EL.G 0) (EL.G 0)) pid = true := by quickRfl

theorem kR3a : Nat.beq (pc (EL.G 1) (EL.G 1)) (EL.G 0) = true := by quickRfl

theorem kR3b : Nat.beq (pc (EL.G 2) (EL.G 2)) (EL.G 0) = true := by quickRfl

theorem kR3c : Nat.beq (cj (EL.G 2) (EL.G 1)) (pinv (EL.G 1)) = true := by quickRfl

theorem kR4 : allN 3 (fun k => Nat.beq (cj (FU.G k) (EL.G 0)) (pc (EL.G 0) (cAK k))) = true := by
  quickRfl

theorem kR5a : allN 8 (fun k => Nat.beq (pc (TG.G k) (EL.G 0)) (pc (EL.G 0) (TG.G k))) = true := by
  quickRfl

theorem kR5b : allN 8 (fun k => (q8K (EL.G 1) (EL.G 2)).any (Nat.beq (cj (TG.G k) (EL.G 1)))) =
    true := by quickRfl

theorem kR5c : allN 8 (fun k => (q8K (EL.G 1) (EL.G 2)).any (Nat.beq (cj (TG.G k) (EL.G 2)))) =
    true := by quickRfl

theorem kR6 : allN 240 (fun i => Nat.beq (pg 9 511 (EL.G 3) i) (pg 8 255 (FT 23) i)) = true := by
  quickRfl

theorem kR7 : Nat.beq (pc (EL.G 3) (EL.G 3)) pid = true := by quickRfl

theorem kR8 : Nat.beq (cj (EL.G 4) (EL.G 3)) (pc (EL.G 3) (cAK 1)) = true := by quickRfl

theorem kR9 : allN 5 (fun k => Nat.beq (pc (CC.G k) (EL.G 3)) (pc (EL.G 3) (CC.G k))) = true := by
  quickRfl

theorem kR10a : allN 240 (fun i => Nat.beq (pg 9 511 (EL.G 5) i) (pg 8 255 (FT 3) i)) = true := by
  quickRfl

theorem kR10b : allN 240 (fun i => Nat.beq (pg 9 511 (EL.G 6) i) (pg 8 255 (FT 252) i)) = true := by
  quickRfl

theorem kR11 : allN 2 (fun k => bAnd(!(Nat.beq (pc (EL.G (Nat.add 5 k)) (EL.G (Nat.add 5 k))) pid),
    !(Nat.beq (pc (pc (EL.G (Nat.add 5 k)) (cAK 1)) (pc (EL.G (Nat.add 5 k)) (cAK 1))) pid))) =
    true := by quickRfl

theorem kR12 : allN 2 (fun k => bAnd(Nat.beq (pc (CRG.G k) (EL.G 1)) (pc (EL.G 1) (CRG.G k)),
    Nat.beq (pc (CRG.G k) (EL.G 2)) (pc (EL.G 2) (CRG.G k)))) = true := by quickRfl

theorem kQ8a : (q8K (EL.G 1) (EL.G 2)).all okK = true := by quickRfl

theorem kQ8b : (q8K (EL.G 1) (EL.G 2)).all (fun a => (q8K (EL.G 1) (EL.G 2)).all fun b =>
    (q8K (EL.G 1) (EL.G 2)).any (Nat.beq (pc a b))) = true := by quickRfl

theorem kQ8c : (q8K (EL.G 1) (EL.G 2)).all (fun a =>
    (q8K (EL.G 1) (EL.G 2)).any (Nat.beq (pinv a))) = true := by quickRfl

end CertificateChecks.KernelOm2

end
