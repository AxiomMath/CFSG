module

public import Certificates.Data.Kernel.SmithEKFp
public import Certificates.Kernel.SmithEK.CdData
public import Certificates.Kernel.SmithEK.FpData
public import Certificates.Kernel.SmithEK.MData
public import Certificates.Kernel.SmithEK.OData
public import Certificates.Kernel.SmithEK.Pts
public import Certificates.Kernel.SmithEK.WData
public import Certificates.Kernel.Misc.XiD.TP
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21276fp_
  (fun r => CFSG.SmithE.K.fpRepK CFSG.KD.Misc.Xi.TP (CertificateChecks.KernelSmithEK.po.PL.getD 0 [])
    (CertificateChecks.KernelSmithEK.pd.LT.getD (Nat.add r 2) 0) 19
    CertificateChecks.KernelSmithEK.po.PL CertificateChecks.KernelSmithEK.pb.P
    CertificateChecks.KernelSmithEK.wd.W CertificateChecks.KernelSmithEK.pts.L
    (CertificateChecks.KernelSmithEK.pf.PI.getD r []) (CertificateChecks.KernelSmithEK.pf.PJ.getD r [])
    (CertificateChecks.KernelSmithEK.pf.UM.getD r []) (CertificateChecks.KernelSmithEK.pf.BS.getD r [])
    (CertificateChecks.KernelSmithEK.pf.BM.getD r []) (CertificateChecks.KernelSmithEK.pf.FX.getD r [])
    (CertificateChecks.KernelSmithEK.pf.FC.getD r []) (CertificateChecks.KernelSmithEK.pf.FE.getD r [])
    (CertificateChecks.KernelSmithEK.pf.FL.getD r []) (CertificateChecks.KernelSmithEK.pf.SP.getD r []))
  0 3
