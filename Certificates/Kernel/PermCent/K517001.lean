module

public import Certificates.Data.Kernel.PermCent.S7M12C
public import Certificates.Data.S7Q8

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.K517001

open Certificates.S5Rows Certificates.S7Q8 CFSG.Certificates.Kernel.PkCV.S7M12C

theorem k517001_basic : (q8RelB (eC 27) (eC 48) && q8RelB (eC 4) (eC 38) &&
    decide (eC 27 * eC 27 = eC 22) && decide (eC 4 * eC 4 = eC 22) &&
    (q8Span (eC 4) (eC 38)).all fun x => fpC x != fpC (eC 27)) = true := by
  decide +kernel

theorem k517001_class1 : classCheck (eC 27) (eC 48) SLc CLc = true := by
  decide +kernel

theorem k517001_class2 : classCheck (eC 4) (eC 38) SLc CLc = true := by
  decide +kernel

theorem k517001_norm1 : normAllB (eC 27) (eC 48) CZc = true := by
  decide +kernel

theorem k517001_norm2 : normAllB (eC 4) (eC 38) CZc = true := by
  decide +kernel

theorem k517001_q8S : q8InCheck (SLc.filter ord4B) (eC 27) (eC 48) (eC 4) (eC 38) = true := by
  decide +kernel

theorem k517001_q8CZ : q8InCheck (CZc.filter ord4B) (eC 27) (eC 48) (eC 4) (eC 38) = true := by
  decide +kernel

theorem k517001_edge : (edgeB (eC 27) (eC 48) (eC 4) (eC 38) Ec &&
    factB (eC 27) (eC 48) (eC 4) (eC 38) [Ec] Ac FAc &&
    factB (eC 27) (eC 48) (eC 4) (eC 38) [Ec] Bc FBc) = true := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.K517001

end
