module

public import Certificates.Kernel.SporSch.Mathieu.M22OData
public import CFSG.Certificates.Kernel.SporSch.ChainKCosetClassEq
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M22OC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT

@[expose] noncomputable def XO : List Nat :=
  [210807013258508634695602337318944, 539009560421025950312372031785985,
    671392086201514384129908610993153, 331534703744324155674095882733600,
    427772902558002597503243231759392, 301006616355128741795844057074720,
    712676444204616306429661336964097, 538955353662767225066839735274561,
    379323923574366073684465869261888, 757304110698254614741846542388288]

@[expose] noncomputable def CO : List Nat := [1344, 320, 48, 32, 6, 8, 5, 6, 7, 7]

theorem oRep : allN 10 (fun i => cosetRepK 22 5 (mask 5) (22 * 5) M22Q.BP 5 M22Q.LR M22Q.TR
    M22Q.TRI M22D (XO.getD i 0) (CO.getD i 0)) = true := by quickRfl

theorem oDist : allN 10 (fun i => allN i (fun j => distK 22 5 (mask 5) (22 * 5) M22Q.BP 5
    M22Q.LR M22Q.TR M22Q.TRI (XO.getD j 0) (XO.getD i 0))) = true := by quickRfl

theorem oSum : Nat.beq (sumAllK (ordK M22Q.LR 5) CO 10) (ordK M22Q.LR 5) = true := by quickRfl

theorem oLt : allN 10 (fun i => Nat.blt (CO.getD i 0) (ordK M22Q.LR 5)) = true := by quickRfl

theorem oTot2 : Nat.beq (sumOrdK 22 5 (mask 5) (ordK M22Q.LR 5) XO CO 2 10) 1716 = true := by
  quickRfl

end CertificateChecks.KernelSporSch.M22OC

end
