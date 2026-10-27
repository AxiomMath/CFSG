module

public import Certificates.Kernel.U42Syl.Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData

public section

namespace CertificateChecks.KernelU42Syl

open CFSG.KD.U42Syl CFSG.KD.Sp62W CFSG.AGLEmbedding.KFactProofs.Sp62Local

theorem ch465001_tab : tabK (gensT.map numC) TW TWI TT TI = true := by decide +kernel

theorem ch465001_rep :
    repK (gensT.map numC) (gensV.map numC) (numC cA) (numC cB) RW RT AW BW = true := by
  decide +kernel

theorem ch465001_rec0 : recB TT TI RT REC0 0 K0 = true := by decide +kernel

theorem ch465001_rec1 : recB TT TI RT REC1 K0 K1 = true := by decide +kernel

theorem ch465001_rec2 : recB TT TI RT REC2 K1 K2 = true := by decide +kernel

theorem ch465001_rec3 : recB TT TI RT REC3 K2 K3 = true := by decide +kernel

theorem ch465001_len : REC0.length + REC1.length + REC2.length + REC3.length = 1296 := by
  decide +kernel

end CertificateChecks.KernelU42Syl
