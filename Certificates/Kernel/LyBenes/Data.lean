module

public import Certificates.Data.Kernel.LyBenes.Check
public import Certificates.Kernel.LyGlue.Hex
public import CFSG.Certificates.Kernel.Common.Benes

public section

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.LyBenes CFSG.Sporadic.Recognition.LyonsSims.LyFinal
  CertificateChecks.KernelLy

#kc_benes CertificateChecks.KernelLyB N 0 6 17 fun T j =>
  nIf(Nat.beq j 0, tabPlanes CS, nIf(Nat.beq j 1, tabPlanes DS,
    nIf(Nat.beq j 2, netsApply 17 131072 (repU 131072 17) [T 1, T 1] (idP 17),
      netsApply 17 131072 (repU 131072 17) (genNets T (genZ (Fin.ofNat 6 (j - 1)))) (idP 17))))
#kc_select CertificateChecks.KernelLyB NS N 6

end
