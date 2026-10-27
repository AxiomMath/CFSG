module

public import Certificates.Kernel.SporSch.Mathieu.M12WData
public import Certificates.Data.Kernel.SporSch.CF67GenK
public import Certificates.Data.Kernel.SporSch.OddWit
public import Certificates.Data.Kernel.SporSch.MathieuBT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11 CFSG.KS.SporSch.MOC CFSG.KS.SporSch.MBT
open CFSG.KS.SporSch.OddWit CFSG.KS.SporSch.CF67K CFSG.Sporadic.Schreier
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M12OC

theorem bP : allN 27 (fun i => bAnd(abOK (Certificates.CF67.M12.pw.getD i []),
    Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) (M12Q.S 0) (M12Q.SI 0) (M12Q.S 1) (M12Q.SI 1)
      (Certificates.CF67.M12.pw.getD i [])) (PL.getD i 0))) = true := by quickRfl

theorem bE1 : allN 4 (fun e => bAnd(abOK (Certificates.CF67.M12.ew.getD e ([], [])).1,
    Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) (M12Q.S 0) (M12Q.SI 0) (M12Q.S 1) (M12Q.SI 1)
      (Certificates.CF67.M12.ew.getD e ([], [])).1) (E1L.getD e 0))) = true := by quickRfl

theorem bE2 : allN 4 (fun e => bAnd(abOK (Certificates.CF67.M12.ew.getD e ([], [])).2,
    Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) (M12Q.S 0) (M12Q.SI 0) (M12Q.S 1) (M12Q.SI 1)
      (Certificates.CF67.M12.ew.getD e ([], [])).2) (E2L.getD e 0))) = true := by quickRfl

theorem shr : allN 27 (fun i => Nat.beq (Nat.shiftRight (PL.getD i 0) (12 * 4)) 0) = true ∧
    allN 4 (fun e => bAnd(Nat.beq (Nat.shiftRight (E1L.getD e 0) (12 * 4)) 0,
      Nat.beq (Nat.shiftRight (E2L.getD e 0) (12 * 4)) 0)) = true := ⟨by quickRfl, by quickRfl⟩

theorem bH0 : allN 4 (fun j => bAnd(abOK (CFSG.KS.SporSch.MathieuC3.m12Words0.getD j []),
    Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) (M12Q.S 0) (M12Q.SI 0) (M12Q.S 1) (M12Q.SI 1)
      (CFSG.KS.SporSch.MathieuC3.m12Words0.getD j [])) (M12CH0.S j))) = true := by quickRfl

theorem bH1 : allN 4 (fun j => bAnd(abOK (CFSG.KS.SporSch.MathieuC3.m12Words1.getD j []),
    Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) (M12Q.S 0) (M12Q.SI 0) (M12Q.S 1) (M12Q.SI 1)
      (CFSG.KS.SporSch.MathieuC3.m12Words1.getD j [])) (M12CH1.S j))) = true := by quickRfl

theorem syl : sylK 12 4 3 27 4 (fun i => PL.getD i 0) (fun e => E1L.getD e 0)
    (fun e => E2L.getD e 0) = true := by quickRfl

theorem hComm0 : allN 4 (fun j => Nat.beq (pcomp 12 4 (mask 4) (M12CH0.S j) (E1L.getD 0 0))
    (pcomp 12 4 (mask 4) (E1L.getD 0 0) (M12CH0.S j))) = true := by quickRfl

theorem hComm1 : allN 4 (fun j => Nat.beq (pcomp 12 4 (mask 4) (M12CH1.S j) (E1L.getD 1 0))
    (pcomp 12 4 (mask 4) (E1L.getD 1 0) (M12CH1.S j))) = true := by quickRfl

theorem hOrd : Nat.beq (ordK M12CH0.LR 2) 54 = true ∧ Nat.beq (ordK M12CH1.LR 2) 54 = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem cent0 : Nat.beq (btK 12 4 (mask 4) (12 * 4) M12Q.BP 5 M12Q.LR M12Q.TR M12Q.TRI
    (E1L.getD 0 0) (E1L.getD 0 0)) 54 = true := by quickRfl

theorem cent1 : Nat.beq (btK 12 4 (mask 4) (12 * 4) M12Q.BP 5 M12Q.LR M12Q.TR M12Q.TRI
    (E1L.getD 1 0) (E1L.getD 1 0)) 54 = true := by quickRfl

theorem elems0 : allN 54 (fun j => powCommK 12 4 (E2L.getD 0 0) 27
    (elemK 12 4 (mask 4) (12 * 4) (pidn 12 4) M12CH0.LR M12CH0.TR 2 j)) = true := by quickRfl

theorem elems1 : allN 54 (fun j => powCommK 12 4 (E2L.getD 1 0) 27
    (elemK 12 4 (mask 4) (12 * 4) (pidn 12 4) M12CH1.LR M12CH1.TR 2 j)) = true := by quickRfl

theorem elems2 : allN 54 (fun j => powCommK 12 4 (E2L.getD 2 0) 27
    (elemK 12 4 (mask 4) (12 * 4) (pidn 12 4) M12CH1.LR M12CH1.TR 2 j)) = true := by quickRfl

theorem elems3 : allN 54 (fun j => powCommK 12 4 (E2L.getD 3 0) 27
    (elemK 12 4 (mask 4) (12 * 4) (pidn 12 4) M12CH1.LR M12CH1.TR 2 j)) = true := by quickRfl

end CertificateChecks.KernelSporSch.M12W

end
