module

public import Certificates.Kernel.MaxD2.HSU35E.HeisData
public import Certificates.Kernel.MaxD2.HSP.Enum
public import Certificates.Kernel.MaxD2.HSP.Data
public import Certificates.Kernel.MaxD2.HSOver.Enum
public import Certificates.Kernel.MaxD2.HSOver.Data
public import Certificates.Kernel.MaxD2.HSU.Enum
public import Certificates.Kernel.MaxD2.HSU.Data
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Data.Kernel.MaxD2.Heis
public import Certificates.Data.HSFiveLocalR
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.HSU35E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Heis

theorem ch19831_rg0 : wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsFiveDataP.uW
    (HSU.RE.G 0) = true := by quickRfl
theorem ch19831_rg1 : wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsFiveDataP.vW
    (HSU.RE.G 1) = true := by quickRfl
theorem ch19831_norm : allN 4 (fun j => allN 2 (fun i =>
    bAnd(conjInK 100 7 HSU.RE.cnt HSU.RE.T (HSP.NE.G j) (HSP.NGI j) (HSU.RE.G i)
      (r32 NHP (Nat.add (Nat.mul 4 j) (Nat.mul 2 i))),
    conjInK 100 7 HSU.RE.cnt HSU.RE.T (HSP.NGI j) (HSP.NE.G j) (HSU.RE.G i)
      (r32 NHP (Nat.add (Nat.add (Nat.mul 4 j) (Nat.mul 2 i)) 1))))) = true := by quickRfl
theorem ch19831_tw : wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsFiveDataP.tW
    (HSP.NE.G 2) = true := by quickRfl
theorem ch19831_tp : permOK 100 7 (mask 7) (100 * 7) (HSP.NE.G 2) (HSP.NGI 2) = true := by
  quickRfl
theorem ch19831_th1 : Nat.blt (r32 MS 0) HSP.NE.cnt = true := by quickRfl
theorem ch19831_th2 : Nat.beq (HSP.NE.T (r32 MS 0)) (HSP.NE.G 2) = true := by quickRfl
theorem ch19831_tk : torusHK 100 7 hsFiveDataP.p HSU.RE.cnt 5 hsFiveDataP.tm hsFiveDataP.tlam
    hsFiveDataP.te HSU.RE.T (r32 HSU.ZP) (HSU.RE.G 0) (HSU.RE.G 1) (HSP.NE.G 2) (HSP.NGI 2) =
    true := by quickRfl
theorem ch19831_cent : allN HSP.NE.cnt (fun k => centK 100 7 HSU.RE.cnt HSP.NE.T HSU.RE.T
    (HSU.RE.G 0) (HSU.RE.G 1) (r32 CHP k) k) = true := by quickRfl

theorem ch19832_rg0 : wordEqK 100 7 (mask 7) (pidn 100 7) HSOver.GP HSOver.GPI 3 hsFiveDataR.uW
    (HSU.RE.G 0) = true := by quickRfl
theorem ch19832_rg1 : wordEqK 100 7 (mask 7) (pidn 100 7) HSOver.GP HSOver.GPI 3 hsFiveDataR.vW
    (HSU.RE.G 1) = true := by quickRfl
theorem ch19832_norm : allN 5 (fun j => allN 2 (fun i =>
    bAnd(conjInK 100 7 HSU.RE.cnt HSU.RE.T (HSOver.NE.G j) (HSOver.NGI j) (HSU.RE.G i)
      (r32 NHR (Nat.add (Nat.mul 4 j) (Nat.mul 2 i))),
    conjInK 100 7 HSU.RE.cnt HSU.RE.T (HSOver.NGI j) (HSOver.NE.G j) (HSU.RE.G i)
      (r32 NHR (Nat.add (Nat.add (Nat.mul 4 j) (Nat.mul 2 i)) 1))))) = true := by quickRfl
theorem ch19832_tw : wordEqK 100 7 (mask 7) (pidn 100 7) HSOver.GP HSOver.GPI 3 hsFiveDataR.tW
    (HSOver.NE.G 2) = true := by quickRfl
theorem ch19832_tp : permOK 100 7 (mask 7) (100 * 7) (HSOver.NE.G 2) (HSOver.NGI 2) = true := by
  quickRfl
theorem ch19832_th1 : Nat.blt (r32 MS 1) HSOver.NE.cnt = true := by quickRfl
theorem ch19832_th2 : Nat.beq (HSOver.NE.T (r32 MS 1)) (HSOver.NE.G 2) = true := by quickRfl
theorem ch19832_tk : torusHK 100 7 hsFiveDataR.p HSU.RE.cnt 5 hsFiveDataR.tm hsFiveDataR.tlam
    hsFiveDataR.te HSU.RE.T (r32 HSU.ZP) (HSU.RE.G 0) (HSU.RE.G 1) (HSOver.NE.G 2)
    (HSOver.NGI 2) = true := by quickRfl
theorem ch19832_cent : allN HSOver.NE.cnt (fun k => centK 100 7 HSU.RE.cnt HSOver.NE.T HSU.RE.T
    (HSU.RE.G 0) (HSU.RE.G 1) (r32 CHR k) k) = true := by quickRfl

end CertificateChecks.KernelMaxD2.HSU35E

end
