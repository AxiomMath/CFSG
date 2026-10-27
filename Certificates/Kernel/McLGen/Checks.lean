module

public import Certificates.Kernel.McLGen.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLGen

theorem gen_ok : genOK = true := by quickRfl
theorem words_ok : wordsOK = true := by quickRfl
theorem inv_ok : invOK' = true := by quickRfl
theorem pair_ok : pairOK = true := by quickRfl
theorem fix_ok : fixOK = true := by quickRfl
theorem tree_ok : CFSG.KC.Enum.allN 5 tree = true := by quickRfl
theorem cnt_ok : (CNTJ 0 == 275 && CNTJ 1 == 162 && CNTJ 2 == 105 && CNTJ 3 == 64 &&
    CNTJ 4 == 3) = true := by quickRfl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.SC

end CertificateChecks.KernelMcLGen

end
