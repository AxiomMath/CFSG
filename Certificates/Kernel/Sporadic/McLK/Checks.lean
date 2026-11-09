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
    [WL 0, WL 1, WL 2, WL 3, WL 4, WL 5, WL 6, WL 7, WL 8] := by
  simp only [chainWords, wordOf, String.toList_append, List.append_assoc, strToList]
  decide +kernel
theorem mclLettersW_ok : mclLettersW = true := by quickRfl
theorem invL_ok : invL = true := by quickRfl
theorem tree_ok : CFSG.KC.Enum.allN 6 tree = true := by quickRfl
theorem schR_ok : CFSG.KC.Enum.allN 5 (fun i => schR (Nat.succ i)) = true := by quickRfl
theorem term_ok : term = true := by quickRfl
theorem t2_ok : t2 = true := by quickRfl
theorem cover_ok : cover = true := by quickRfl

end CertificateChecks.KernelSpor.McLK

#kon_slices CertificateChecks.KernelSpor.McLK.sch0 0 5
#kon_slices CertificateChecks.KernelSpor.McLK.mclGramSl 0 18

end
