module

public import Certificates.Kernel.LyBenes.Data
public import CFSG.Sporadic.Recognition.LyonsModelInputs

public section

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.LyBenes CFSG.Sporadic.Recognition.LyonsSims
  CertificateChecks.KernelLyB

#kc_benes CertificateChecks.KernelLyModel NY 0 1 17 fun _ _ =>
  netsApply 17 131072 (repU 131072 17) (genNets NS Ly0.wordY) (idP 17)

end
