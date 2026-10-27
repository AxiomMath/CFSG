module

public import Certificates.Kernel.Sporadic.McLK.Defs
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
import Certificates.Kernel.Sporadic.StrList

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLK

open CFSG.Sporadic.McL.Native

theorem orbHd_ok : orbHd = true := by quickRfl
theorem orbPt_ok : orbPt = true := by quickRfl
theorem orbSort_ok : orbSort = true := by quickRfl
theorem invAB_ok : invAB = true := by quickRfl
theorem words_all : (chainWords ()).toList.map (fun w => w.map codeZ) =
    [W0, W1, W2, W3, W4, W5, W6, W7, W8] := by
  simp only [chainWords, wordOf, String.toList_append, strToList]
  decide +kernel
theorem invL_ok : invL = true := by quickRfl
theorem tree_ok : CFSG.KC.Enum.allN 6 tree = true := by quickRfl
theorem schR_ok : CFSG.KC.Enum.allN 5 (fun i => schR (Nat.succ i)) = true := by quickRfl
theorem term_ok : term = true := by quickRfl
theorem t2_ok : t2 = true := by quickRfl
theorem cover_ok : cover = true := by quickRfl

end CertificateChecks.KernelSpor.McLK

#kon_slices CertificateChecks.KernelSpor.McLK.sch0 0 5
#kon_slices CertificateChecks.KernelSpor.McLK.wordsSl 0 99

end
