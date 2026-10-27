module

public import Certificates.Data.Kernel.PermCent.Gs03C
public import Certificates.Data.Kernel.PermCent.SmallK
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03A6Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.Certificates.Kernel.PkCV.Gs03.K1037401
  "Certificates/Kernel/PermCent/data/kg1037401.json.gz" 8767 6072821468486099162
  (wit : List (Nat × Nat))

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.Gs03.K1037401

open CFSG.GH74.KGroups.A6 CFSG.LocalAnalysis.WeakClosure81.Gs03A6

theorem kCov : covWC (elemsC QA) ((a6Classes.map fun c => c.1).map cOf) wit = true := by
  decide +kernel

theorem kCls : clsesC QP ([pa, pb].map cOf) 5 (a6Classes.map cOfCls) = true := by
  decide +kernel

theorem kNeg : covWC (elemsC QA) ((a6Classes.map fun c => c.1).map cOf)
      (wit.map fun w => (w.1, w.2 + 1)) = false ∧
    covWC (elemsC QA) ((a6Classes.map fun c => c.1).map cOf) (wit.map fun w => (3, w.2)) = false ∧
    covWC (elemsC QA) ((a6Classes.map fun c => c.1).map cOf) wit.tail = false ∧
    clsesC QP ([pa, pb].map cOf) 4 (a6Classes.map cOfCls) = false ∧
    clsesC QP ([pb, pb].map cOf) 5 (a6Classes.map cOfCls) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.Certificates.Kernel.PkCV.Gs03.K1037401

end
