
module

public import Certificates.Kernel.SporSch.PairHe.Check2225
public import Certificates.Kernel.SporSch.PairHe.CntScA
public import Certificates.Kernel.SporSch.PairHe.CntScA3

public section

#kss_b2all CertificateChecks.KernelSporSch.PHeCn CertificateChecks.KernelSporSch.PHeCn.scA 7 8
#kss_b2all CertificateChecks.KernelSporSch.PHeCn CertificateChecks.KernelSporSch.PHeCn.scA3 7 8

namespace CertificateChecks.KernelSporSch.PHePart

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB

theorem facts :
    countPair PairHe.bs 7 PairHe.wA PairHe.conds heBlocks ≤ 322560 ∧
      (List.range 8330).countP (fun i => (heGen 0)[i]! == i) = 346 ∧
      (List.range 8330).countP (fun i => PairHe.t1Arr[i]! == i) = 42 :=
  ⟨partners_of PHeCn.scA_all PHeCn.scA3_all, fix_facts⟩

end CertificateChecks.KernelSporSch.PHePart

end
