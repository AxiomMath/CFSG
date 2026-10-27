module

public import Certificates.Kernel.SchreierFam.C188001H
public import Certificates.Kernel.SchreierFam.C188001C2
public import Certificates.Kernel.SchreierFam.C188001E2
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Data.Kernel.B3S3K

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.U38B

open CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.KC.Enum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K

@[expose] noncomputable def tailSl2 (s : Nat) : Bool :=
  allBlk (Nat.mul 27 s) (ptailBranchK 513 10 U38C2.LR U38C2.TR U38C2.BP (U38A.F 27)
    (pw 513 10 (U38A.F 27)) rels2 U38E2.N U38E2.T 5) 27

end CertificateChecks.KernelSchreierFam.U38B

end

#kss_each CertificateChecks.KernelSchreierFam.U38T2
  CertificateChecks.KernelSchreierFam.U38B.tailSl2 19
