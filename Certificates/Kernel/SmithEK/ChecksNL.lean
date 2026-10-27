module

public import Certificates.Data.Kernel.SmithEKNL
public import Certificates.Kernel.SmithEK.NTData
public import Certificates.Kernel.SmithEK.OData
public import Certificates.Kernel.Misc.Unitary
public import CFSG.LargeExtraspecial.S14SMKTransCheck
public import CFSG.Certificates.Kernel.Common.EachTrue
public import Std.Data.HashMap

#kc_each CertificateChecks.KernelSmithEK c21275lift_
  (fun _ => CFSG.SmithE.K.liftK CFSG.KD.Misc.Unitary.UL CFSG.F4.Native.normC CFSG.SmithE.dltC
    CFSG.SmithE.frobC (CertificateChecks.KernelSmithEK.po.PL.getD 0 [])
    (CertificateChecks.KernelSmithEK.po.SG.getD 0 []) CertificateChecks.KernelSmithEK.pt.RT) 0 1
