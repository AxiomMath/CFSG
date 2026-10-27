module

public import Certificates.Kernel.LyBenes.Data
public import CFSG.Sporadic.Recognition.LyonsModelInputs

public section

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.LyBenes CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.McLMultiplier CertificateChecks.KernelLyB

#kc_benes CertificateChecks.KernelLyModel M 0 8 17 fun T j =>
  nIf(Nat.beq j 0, netsApply 17 131072 (repU 131072 17) (genNets NS Ly0.wordA) (idP 17),
    nIf(Nat.beq j 1, netsApply 17 131072 (repU 131072 17) (genNets NS Ly0.wordB) (idP 17),
      nIf(Nat.beq j 2, netsApply 17 131072 (repU 131072 17) (genNets NS (invW Ly0.wordB)) (idP 17),
        netsApply 17 131072 (repU 131072 17) (genNets T (mclGenWord (j - 3))) (idP 17))))
#kc_select CertificateChecks.KernelLyModel MS M 8

end
