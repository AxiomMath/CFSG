module

public import Certificates.Data.Kernel.Sp62W.Defs
public import Certificates.Kernel.Sp62W.DataV
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CertificateChecks.KernelSp62W

open CFSG.KD.Sp62W CFSG.KD.BfsK CFSG.KGroups.Sp6 CFSG.AGLEmbedding.KFactProofs.Sp62Local

theorem ch9441v_g : gensK VR gensV = true := by decide +kernel

theorem ch9441v_m : memsK VR 2 20 25920
    (gensT ++ gensWD.flatMap fun g => gensV.map (conjC g)) = true := by decide +kernel

theorem ch9441v_h : (Nat.beq (recX VR 20 0) (numC oneC) && Nat.beq (recC VR 20 2 0) 1 &&
    Nat.beq (recC VR 20 2 (25920 * 2)) 25920) = true := by decide +kernel

#kc_each CertificateChecks.KernelSp62W ch9441vB (fun j => buildSl VR 20 25920 2 j) 0 7

#kc_forall_chunks ch9441v_b (fun j => buildSl VR 20 25920 2 j = true) 7
  CertificateChecks.KernelSp62W.ch9441vB 1

#kc_each CertificateChecks.KernelSp62W ch9441vT (fun j => sortSl VR 20 25920 j) 0 7

#kc_forall_chunks ch9441v_t (fun j => sortSl VR 20 25920 j = true) 7
  CertificateChecks.KernelSp62W.ch9441vT 1

#kc_each CertificateChecks.KernelSp62W ch9441vS (fun j => stepSl VR 20 25920 2 j) 0 13

#kc_forall_chunks ch9441v_s (fun j => stepSl VR 20 25920 2 j = true) 13
  CertificateChecks.KernelSp62W.ch9441vS 1

theorem ch9441v_n1 : gensK VR [cB, cA] = false := by decide +kernel

theorem ch9441v_n2 : memsK VR 2 20 25920 [cGD] = false := by decide +kernel

end CertificateChecks.KernelSp62W

end
