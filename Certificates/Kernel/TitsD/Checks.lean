module

public import Certificates.Kernel.TitsD.Data
public import Certificates.Kernel.TitsOct.Data
public import Certificates.Kernel.Misc.Tits.Text
public import Certificates.Data.Kernel.TitsDK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsD

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KC.TitsDK CFSG.KD.TitsD
  CFSG.KD.TitsOct CertificateChecks.KernelMisc

@[expose] noncomputable def lpT (i : Nat) : Nat := fw 11 LP i

@[expose] noncomputable def FH (j : Nat) : Nat := TitsText.F (Nat.add 43 j)

@[expose] noncomputable def FN (j : Nat) : Nat := TitsText.F (Nat.add 61 j)

@[expose] noncomputable def labF (i : Nat) : Nat := [1755, 1756, 1757, 1763, 1759].getD i 0

theorem invH : allN 9 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (FH j) (HI j)) = true := by
  quickRfl

theorem invN : allN 10 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (FN j) (NI j)) = true := by
  quickRfl

theorem bindP : bindK FH HI EP wPt = true := by quickRfl

theorem bind1 : bindK FN NI E1 w1Ln = true := by quickRfl

theorem bind2 : bindK FN NI E2 w2Ln = true := by quickRfl

theorem recP : recR lpT FH 9 (fun x => Nat.beq x 87) 8 1024 LAY0 ORDP PRP LBP PSP = true := by
  quickRfl

theorem recS : recR lpT FN 10 (fun x => Nat.beq x 45) 7 1536 LAY1 ORDS PRS LBS PSS = true := by
  quickRfl

theorem recE : recR lpT FN 10 (fun x => bIf(Nat.beq x 1862, true, Nat.beq x 1896)) 8 2048 LAY1
    ORDE PRE LBE PSE = true := by
  quickRfl

theorem stabP : stabK lpT PL EP 10 0 87 = true := by quickRfl

theorem stab1 : stabK lpT PL E1 6 1755 1862 = true := by quickRfl

theorem stab2 : stabK lpT PL E2 6 1755 1896 = true := by quickRfl

theorem transP : transK lpT PL EP 10 0 1755 = true := by quickRfl

theorem exactP : exactK lpT PL (EP 2) 1755 87 K0 = true := by quickRfl

theorem labP : labK lpT PL 0 labF = true := by quickRfl

theorem affP : affK lpT FH 9 labF AF = true := by quickRfl

theorem layP : bAnd(Nat.beq (layAt LAY0 87) 8, bAnd(Nat.beq (layAt LAY1 45) 7,
    bAnd(Nat.beq (layAt LAY1 1862) 8, Nat.beq (layAt LAY1 1896) 8))) = true := by
  quickRfl

end CertificateChecks.KernelTitsD

end
