module

public import Certificates.Kernel.TitsOct.Data
public import Certificates.Data.Kernel.TitsOctK
public import Certificates.Kernel.SporSch.Tits.Action2262
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOct

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KD.TitsOct
open CertificateChecks.KernelSporSch.TitsAction CertificateChecks.KernelMisc

@[expose] noncomputable def F (h : Nat) : Nat := TitsText.F h

@[expose] noncomputable def lpD (i : Nat) : Nat := fw 11 LP i

theorem lpEq : bAnd(Nat.beq (Nat.shiftRight LP (8775 * 11)) 0,
    allN 8775 (fun i => Nat.beq (lpD i) (lpK i))) = true := by quickRfl

theorem invG : allN 4 (fun h => permOK 1755 11 (mask 11) (1755 * 11) (F h) (GI h)) = true := by
  quickRfl

theorem bindP : bindK F GI FP fwPt = true := by quickRfl

theorem bindL : bindK F GI FL fwLn = true := by quickRfl

theorem inc : incK lpD PL = true := by quickRfl

theorem lay0 : layK lpD PL 0 1024 LAY0 PAR0 = true := by quickRfl

theorem lay1 : layK lpD PL 1755 2048 LAY1 PAR1 = true := by quickRfl

theorem cyc : cycK lpD CYC = true := by quickRfl

theorem fix0 : allN 5 (fun j => fixV lpD PL (gp (FP j)) 0) = true := by quickRfl

theorem fix1 : allN 3 (fun j => fixV lpD PL (gp (FL j)) 1755) = true := by quickRfl

theorem rec0 : recK lpD FP 5 87 1024 LAY0 ORD0 PR0 LB0 PS0 = true := by quickRfl

theorem rec1 : recK lpD FL 3 1862 2048 LAY1 ORD1 PR1 LB1 PS1 = true := by quickRfl

theorem loc0 : locK lpD F GI PL 0 87 5 lwPt prPt = true := by quickRfl

theorem loc1 : locK lpD F GI PL 1755 1862 3 lwLn prLn = true := by quickRfl

theorem small : smallK lpD FP PL (F 3) (F 1) (F 2) = true := by quickRfl

theorem far : farK LAY0 = true := by quickRfl

theorem witLen : Nat.beq WIT.length 1024 = true := by quickRfl

theorem wit0 : witK FP LAY0 ORD0 PR0 LB0 PS0 (F 3) (F 2) 0 (WIT.take 512) = true := by quickRfl

theorem wit1 : witK FP LAY0 ORD0 PR0 LB0 PS0 (F 3) (F 2) 512 (WIT.drop 512) = true := by quickRfl

end CertificateChecks.KernelTitsOct

end
