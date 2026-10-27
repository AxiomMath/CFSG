module

public import Certificates.Data.Kernel.SmithEKCd
public import Certificates.Kernel.SmithEK.CdData
public import Certificates.Kernel.SmithEK.MData
public import Certificates.Kernel.SmithEK.OData
public import Certificates.Kernel.SmithEK.Pts
public import Certificates.Kernel.SmithEK.WData
public import Certificates.Kernel.Misc.XiD.TP
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21276map_
  (fun i => CFSG.SmithE.K.cdMapK (bif Nat.beq i 0 then CFSG.SmithE.K.cdFrob else CFSG.SmithE.K.cdDlt)
    CertificateChecks.KernelSmithEK.pts.L
    (bif Nat.beq i 0 then CertificateChecks.KernelSmithEK.pd.FT
     else CertificateChecks.KernelSmithEK.pd.DT)) 0 2

#kc_each CertificateChecks.KernelSmithEK c21276inv_
  (fun i => bif Nat.beq i 0 then
      CFSG.SmithE.K.cdInvK [CertificateChecks.KernelSmithEK.pd.DT] CertificateChecks.KernelSmithEK.pd.DI
    else CFSG.SmithE.K.cdInvK [CertificateChecks.KernelSmithEK.pd.DT,
      CertificateChecks.KernelSmithEK.pd.DT] CertificateChecks.KernelSmithEK.pd.EI) 0 2

#kc_each CertificateChecks.KernelSmithEK c21276lt_
  (fun j => CFSG.SmithE.K.cdCompK (CertificateChecks.KernelSmithEK.pd.LT.getD j 0)
    ([[], [CFSG.KD.Misc.Xi.TP (Nat.mod (CertificateChecks.KernelSmithEK.po.SW.getD 0 0) 1024),
        CFSG.KD.Misc.Xi.TP (Nat.div (CertificateChecks.KernelSmithEK.po.SW.getD 0 0) 1024)],
      [CertificateChecks.KernelSmithEK.pd.FT],
      [CertificateChecks.KernelSmithEK.pd.DT, CertificateChecks.KernelSmithEK.pd.FT,
        CertificateChecks.KernelSmithEK.pd.DI],
      [CertificateChecks.KernelSmithEK.pd.DT, CertificateChecks.KernelSmithEK.pd.DT,
        CertificateChecks.KernelSmithEK.pd.FT, CertificateChecks.KernelSmithEK.pd.EI]].getD j []))
  0 5

#kc_each CertificateChecks.KernelSmithEK c21276sa_
  (fun j => CFSG.SmithE.K.cdSaK (CertificateChecks.KernelSmithEK.po.PL.getD 0 [])
    (CertificateChecks.KernelSmithEK.pd.LT.getD j 0) (CertificateChecks.KernelSmithEK.pd.SA.getD j []))
  0 5

#kc_each CertificateChecks.KernelSmithEK c21276red_
  (fun j => Nat.beq (CFSG.SmithE.K.lenK (CertificateChecks.KernelSmithEK.pd.RD.getD j [])) 512 &&
    CFSG.SmithE.K.cdRedAll CFSG.KD.Misc.Xi.TP (CertificateChecks.KernelSmithEK.po.PL.getD 0 [])
      (CertificateChecks.KernelSmithEK.pd.LT.getD (Nat.succ j) 0) CertificateChecks.KernelSmithEK.po.CO
      (CertificateChecks.KernelSmithEK.pd.SA.getD (Nat.succ j) [])
      (CertificateChecks.KernelSmithEK.pd.RP.getD (Nat.succ j) [])
      (CertificateChecks.KernelSmithEK.pd.RD.getD j []) 0) 0 4

#kc_each CertificateChecks.KernelSmithEK c21276rep_
  (fun k => CFSG.SmithE.K.cdRepK CFSG.KD.Misc.Xi.TP (CertificateChecks.KernelSmithEK.po.PL.getD 0 [])
    CertificateChecks.KernelSmithEK.pd.LT CertificateChecks.KernelSmithEK.po.PL
    CertificateChecks.KernelSmithEK.pb.P CertificateChecks.KernelSmithEK.wd.W
    (CertificateChecks.KernelSmithEK.pd.RR.getD k [])) 0 29
