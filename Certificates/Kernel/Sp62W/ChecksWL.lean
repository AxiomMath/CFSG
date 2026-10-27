module

public import Certificates.Data.Kernel.Sp62W.Defs
public import Certificates.Kernel.Sp62W.DataWL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CertificateChecks.KernelSp62W

open CFSG.KD.Sp62W CFSG.KD.BfsK CFSG.KGroups.Sp6 CFSG.AGLEmbedding.KFactProofs.Sp62Local

theorem ch9441wl_g : gensK WL gensWL = true := by decide +kernel

theorem ch9441wl_m : memsK WL 7 14 51840 gensWD = true := by decide +kernel

theorem ch9441wl_h : (Nat.beq (recX WL 14 0) (numC oneC) && Nat.beq (recC WL 14 7 0) 1 &&
    Nat.beq (recC WL 14 7 (51840 * 7)) 51840) = true := by decide +kernel

#kc_each CertificateChecks.KernelSp62W ch9441wlB (fun j => buildSl WL 14 51840 7 j) 0 13

#kc_forall_chunks ch9441wl_b (fun j => buildSl WL 14 51840 7 j = true) 13
  CertificateChecks.KernelSp62W.ch9441wlB 1

#kc_each CertificateChecks.KernelSp62W ch9441wlT (fun j => sortSl WL 14 51840 j) 0 13

#kc_forall_chunks ch9441wl_t (fun j => sortSl WL 14 51840 j = true) 13
  CertificateChecks.KernelSp62W.ch9441wlT 1

#kc_each CertificateChecks.KernelSp62W ch9441wlS (fun j => stepSl WL 14 51840 7 j) 0 45

theorem ch9441wl_n1 : gensK WL gensWD = false := by decide +kernel

theorem ch9441wl_n2 : memsK WL 7 14 51840 gensWL = false := by decide +kernel

end CertificateChecks.KernelSp62W

end
