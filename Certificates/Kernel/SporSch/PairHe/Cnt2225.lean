
module

public import Certificates.Kernel.SporSch.PairHe.Check2225O
public import Certificates.Kernel.SporSch.PairHe.CntOrb

public section

#kss_b2all CertificateChecks.KernelSporSch.PHeCn CertificateChecks.KernelSporSch.PHeCn.orbB 3 8
#kss_b2all CertificateChecks.KernelSporSch.PHeCn CertificateChecks.KernelSporSch.PHeCn.permB 7 7

namespace CertificateChecks.KernelSporSch.PHePart

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB

theorem facts :
    countPair PairHe.bs 7 PairHe.wA PairHe.conds heBlocks ≤ 322560 ∧
      (List.range 8330).countP (fun i => (heGen 0)[i]! == i) = 346 ∧
      (List.range 8330).countP (fun i => PairHe.t1Arr[i]! == i) = 42 :=
  ⟨partners_orb PHeCn.orbB_all PHeCn.permB_all PHeCn.rep_ok PHeCn.op_ok PHeCn.op2_ok, fix_facts⟩

end CertificateChecks.KernelSporSch.PHePart

end
