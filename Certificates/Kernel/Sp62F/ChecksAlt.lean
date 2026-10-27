module

public import Certificates.Data.Kernel.Sp62W.Defs
public import Certificates.Kernel.Sp62F.DataAlt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62EscapeData

public section

namespace CertificateChecks.KernelSp62F

open CFSG.KD.Sp62W CFSG.KD.BfsK CFSG.KGroups.Sp6 CFSG.AGLEmbedding.KFactProofs.Sp62Local

theorem ch9540_g : gensK AR gensAlt = true := by decide +kernel

theorem ch9540_h : (Nat.beq (recX AR 4 0) (numC oneC) && Nat.beq (recC AR 4 4 0) 1 &&
    Nat.beq (recC AR 4 4 (360 * 4)) 360) = true := by decide +kernel

theorem ch9540_b : buildSl AR 4 360 4 0 = true := by decide +kernel

theorem ch9540_s : stepSl AR 4 360 4 0 = true := by decide +kernel

theorem ch9540_t : sortSl AR 4 360 0 = true := by decide +kernel

theorem ch9540_gen : gensAlt.all genB = true := by decide +kernel

theorem ch9540_rel : relAlt = true := by decide +kernel

theorem ch9540_comm : commAlt = true := by decide +kernel

theorem ch9540_q : (qbits cAlt0 != qbits oneC) = true := by decide +kernel

end CertificateChecks.KernelSp62F

end
