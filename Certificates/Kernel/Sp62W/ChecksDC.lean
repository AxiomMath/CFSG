module

public import Certificates.Data.Kernel.Sp62W.Cosets

public section

namespace CertificateChecks.KernelSp62W

open CFSG.KD.Sp62W CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.KGroups.Sp6

theorem ch9443dc : dcCosetsCheck = true := by decide +kernel

end CertificateChecks.KernelSp62W
