module

public import Certificates.Data.Kernel.Sp62F.Defs
public import Certificates.Kernel.Sp62F.DataN
public import Certificates.Kernel.Sp62L.Data

public section

namespace CertificateChecks.KernelSp62F

open CFSG.KD.Sp62W CFSG.KD.Sp62F CFSG.KD.BfsK CFSG.KGroups.Sp6
  CFSG.AGLEmbedding.KFactProofs.Sp62Local CertificateChecks.KernelSp62L

theorem ch9452n_g : gensK NR gensN = true := by decide +kernel

theorem ch9452n_m : memsK NR 6 15 1296 (gensN ++ [cIo1, cIo2, cTau12]) = true := by decide +kernel

theorem ch9452n_h : (Nat.beq (recX NR 15 0) (numC oneC) && Nat.beq (recC NR 15 6 0) 1 &&
    Nat.beq (recC NR 15 6 (1296 * 6)) 1296) = true := by decide +kernel

theorem ch9452n_b : buildSl NR 15 1296 6 0 = true := by decide +kernel

theorem ch9452n_s0 : stepSl NR 15 1296 6 0 = true := by decide +kernel

theorem ch9452n_s1 : stepSl NR 15 1296 6 1 = true := by decide +kernel

theorem ch9452n_t : sortSl NR 15 1296 0 = true := by decide +kernel

theorem ch9452s_g : gensK SR gensS0 = true := by decide +kernel

theorem ch9452s_h : (Nat.beq (recX SR 7 0) (numC oneC) && Nat.beq (recC SR 7 7 0) 1 &&
    Nat.beq (recC SR 7 7 (432 * 7)) 432) = true := by decide +kernel

theorem ch9452s_b : buildSl SR 7 432 7 0 = true := by decide +kernel

theorem ch9452s_s : stepSl SR 7 432 7 0 = true := by decide +kernel

theorem ch9452s_t : sortSl SR 7 432 0 = true := by decide +kernel

end CertificateChecks.KernelSp62F

end
