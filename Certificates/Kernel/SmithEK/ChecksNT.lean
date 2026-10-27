module

public import Certificates.Data.Kernel.SmithEKNT
public import Certificates.Data.Kernel.SmithEKO
public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Kernel.SmithEK.NTData
public import Certificates.Kernel.SmithEK.NData
public import Certificates.Kernel.SmithEK.OData
public import Certificates.Kernel.Misc.XiD.TP
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21275fp_
  (fun _ => CFSG.SmithE.K.ivFP CertificateChecks.KernelSmithEK.pt.FP 675
    ((List.range 21).flatMap fun y0 => CertificateChecks.KernelSmithEK.pn.R.getD y0 [])) 0 1

#kc_each CertificateChecks.KernelSmithEK c21275lt_
  (fun _ => CFSG.SmithE.K.ivLt CertificateChecks.KernelSmithEK.pt.FP 675) 0 1

#kc_each CertificateChecks.KernelSmithEK c21275swr_
  (fun _ => CFSG.KC.Misc.eqLN CertificateChecks.KernelSmithEK.pt.SWR
    (CertificateChecks.KernelSmithEK.po.SW.map fun c => Nat.add (Nat.div c 1024)
      (Nat.mul 1024 (Nat.mod c 1024)))) 0 1

#kc_each CertificateChecks.KernelSmithEK c21275sr_
  (fun _ => CFSG.SmithE.K.sgK CFSG.KD.Misc.Xi.TP (CertificateChecks.KernelSmithEK.po.PL.getD 0 [])
    CertificateChecks.KernelSmithEK.pt.SWR CertificateChecks.KernelSmithEK.pt.SR) 0 1

#kc_each CertificateChecks.KernelSmithEK c21275tree_
  (fun _ => CFSG.SmithL6.K.treeK 675 34
    (CFSG.SmithE.K.ivRootK CertificateChecks.KernelSmithEK.pt.RT CertificateChecks.KernelSmithEK.pt.FP)
    (CFSG.SmithE.K.ivEdgeK CertificateChecks.KernelSmithEK.pt.FP CertificateChecks.KernelSmithEK.po.SG
      CertificateChecks.KernelSmithEK.pt.SR)
    CertificateChecks.KernelSmithEK.pt.RI
    (CertificateChecks.KernelSmithEK.pt.TR.map CFSG.SmithE.K.decR)) 0 1
