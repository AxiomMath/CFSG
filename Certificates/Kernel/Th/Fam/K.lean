module

public import CFSG.Certificates.Kernel.Th.Expr
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.M3_const

public section

namespace CertificateChecks.KernelTh.Fam

@[expose] noncomputable def thK : CFSG.KC.Th.Expr.K :=
  ⟨CFSG.KD.ThM3.RB, CFSG.KD.ThS.c, CFSG.KD.ThS.rm, CFSG.KD.ThS.ONE, CFSG.KD.ThSeed.SA,
    CFSG.KD.ThSeed.SB⟩

end CertificateChecks.KernelTh.Fam

end
