module

public import Certificates.Kernel.LyY.ChainData
public import Certificates.Data.Kernel.LyY.Pair
public import CFSG.Sporadic.Recognition.LyonsAmalgamYData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.LyY CFSG.Sporadic.Recognition.LyonsSims

@[expose] noncomputable def pFix (wd : List Int) : Bool :=
  wordFix 1080 11 (YC.S 0) (YC.SI 0) (YC.S 1) (YC.SI 1) wd

theorem k_pair : bAnd(pFix [1, 1], bAnd(pFix (List.replicate 12 2),
    bAnd(bIf(pFix (List.replicate 6 2), false, true), bAnd(bIf(pFix (List.replicate 4 2), false, true),
    bAnd(Ly1080.autRelators.all pFix, Ly1080.autWitnesses.all fun wd => !pFix wd))))) = true := by
  quickRfl

theorem k_negP : bAnd(bIf(pFix [2, 2], false, true), bIf(pFix [1], false, true)) = true := by
  quickRfl

end CertificateChecks.KernelLyY

end
