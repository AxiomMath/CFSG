module

public import Certificates.Kernel.LyModel.Nets

public section

namespace CertificateChecks.KernelLyModel

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.LyBenes CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.McLMultiplier CertificateChecks.KernelLyB

theorem ly6110_validM : ∀ j < 8, netValid 17 (MS j) = true := by decide +kernel

theorem ly6110_netA : planesEq 17 (genNets NS Ly0.wordA) (MS 0) = true := by decide +kernel

theorem ly6110_netB : planesEq 17 (genNets NS Ly0.wordB) (MS 1) = true := by decide +kernel

theorem ly6110_netBi : planesEq 17 (genNets NS (invW Ly0.wordB)) (MS 2) = true := by decide +kernel

theorem ly6110_netAA : planesId 17 [MS 0, MS 0] = true := by decide +kernel

theorem ly6110_netY0 : planesEq 17 (genNets MS (mclGenWord 0)) (MS 3) = true := by decide +kernel

theorem ly6110_netY1 : planesEq 17 (genNets MS (mclGenWord 1)) (MS 4) = true := by decide +kernel

theorem ly6110_netY2 : planesEq 17 (genNets MS (mclGenWord 2)) (MS 5) = true := by decide +kernel

theorem ly6110_netY3 : planesEq 17 (genNets MS (mclGenWord 3)) (MS 6) = true := by decide +kernel

theorem ly6110_netY4 : planesEq 17 (genNets MS (mclGenWord 4)) (MS 7) = true := by decide +kernel

theorem ly6110_netYY : ∀ k < 5, planesId 17 [MS (k + 3), MS (k + 3)] = true := by decide +kernel

end CertificateChecks.KernelLyModel

end
