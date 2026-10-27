module

public import Certificates.Data.Kernel.SmithEKN
public import Certificates.Kernel.SmithEK.NData
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21275cp_
  (fun _ => Nat.beq CertificateChecks.KernelSmithEK.pn.CP
    (CertificateChecks.KernelSmithEK.pn.CL.foldr (fun x acc => Nat.add x (Nat.mul 512 acc)) 0))
  0 1

#kc_each CertificateChecks.KernelSmithEK c21275lm_
  (fun _ => CFSG.SmithE.K.ivLm CertificateChecks.KernelSmithEK.pn.CP
    (CFSG.SmithE.K.s2K CertificateChecks.KernelSmithEK.pn.CL) CertificateChecks.KernelSmithEK.pn.LI
    CertificateChecks.KernelSmithEK.pn.LM) 0 1

#kc_each CertificateChecks.KernelSmithEK c21275mp_
  (fun _ => CFSG.SmithE.K.ivMp CertificateChecks.KernelSmithEK.pn.LM
    CertificateChecks.KernelSmithEK.pn.MP) 0 1

#kc_each CertificateChecks.KernelSmithEK c21275grp_
  (fun y0 => CFSG.KC.Misc.eqLN
    (CFSG.SmithE.K.ivGrp CertificateChecks.KernelSmithEK.pn.CP CertificateChecks.KernelSmithEK.pn.LI
      CertificateChecks.KernelSmithEK.pn.LM CertificateChecks.KernelSmithEK.pn.MP y0 [])
    (CertificateChecks.KernelSmithEK.pn.R.getD y0 [])) 0 21
