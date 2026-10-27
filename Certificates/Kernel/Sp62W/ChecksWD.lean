module

public import Certificates.Data.Kernel.Sp62W.Defs
public import Certificates.Kernel.Sp62W.DataWD
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CertificateChecks.KernelSp62W

open CFSG.KD.Sp62W CFSG.KD.BfsK CFSG.KGroups.Sp6 CFSG.AGLEmbedding.KFactProofs.Sp62Local

theorem ch9441wd_g : gensK WD gensWD = true := by decide +kernel

theorem ch9441wd_m : memsK WD 7 16 51840 (gensV ++ gensWL) = true := by decide +kernel

theorem ch9441wd_h : (Nat.beq (recX WD 16 0) (numC oneC) && Nat.beq (recC WD 16 7 0) 1 &&
    Nat.beq (recC WD 16 7 (51840 * 7)) 51840) = true := by decide +kernel

#kc_each CertificateChecks.KernelSp62W ch9441wdB (fun j => buildSl WD 16 51840 7 j) 0 13

#kc_forall_chunks ch9441wd_b (fun j => buildSl WD 16 51840 7 j = true) 13
  CertificateChecks.KernelSp62W.ch9441wdB 1

#kc_each CertificateChecks.KernelSp62W ch9441wdT (fun j => sortSl WD 16 51840 j) 0 13

#kc_forall_chunks ch9441wd_t (fun j => sortSl WD 16 51840 j = true) 13
  CertificateChecks.KernelSp62W.ch9441wdT 1

#kc_each CertificateChecks.KernelSp62W ch9441wdC (fun j => cenSl WD 16 51840 (gensV.map numC)
  ([oneC].map numC) (gensT.map numC) ([oneC, cZ, cZ2].map numC) j) 0 13

#kc_forall_chunks ch9441wd_c (fun j => cenSl WD 16 51840 (gensV.map numC) ([oneC].map numC)
  (gensT.map numC) ([oneC, cZ, cZ2].map numC) j = true) 13 CertificateChecks.KernelSp62W.ch9441wdC 1

#kc_each CertificateChecks.KernelSp62W ch9441wdS (fun j => stepSl WD 16 51840 7 j) 0 45

theorem ch9441wd_n1 : gensK WD gensWL = false := by decide +kernel

theorem ch9441wd_n2 : memsK WD 7 16 51840 (gensWL ++ gensV) = false := by decide +kernel

theorem ch9441wd_n3 : stepSl WD 16 51840 6 3 = false := by decide +kernel

theorem ch9441wd_n4 : cenSl WD 16 51840 (gensV.map numC) [] (gensT.map numC)
    ([oneC, cZ, cZ2].map numC) 0 = false := by decide +kernel

end CertificateChecks.KernelSp62W

end
