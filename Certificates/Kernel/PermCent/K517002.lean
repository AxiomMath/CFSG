module

public import Certificates.Data.Kernel.PermCent.S7U33C

public section

set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.K517002

open Certificates.S5Rows Certificates.S7Q8 CFSG.Certificates.Kernel.PkCV.S7U33C CFSG.GH74.KGroups

theorem k517002_basic : (q8RelB I1 J1 && q8RelB I2 J2 && decide (I2 * I2 = I1 * I1) &&
    siftC U33.QP I1 0 && siftC U33.QP J1 0 && !(siftC U33.QP I2 0 && siftC U33.QP J2 0)) = true := by
  decide +kernel

theorem k517002_class1 : classCheck I1 J1 SC AC = true := by
  decide +kernel

theorem k517002_class2 : classCheck I2 J2 SC AC = true := by
  decide +kernel

theorem k517002_norm1 : normAllB I1 J1 CZC = true := by
  decide +kernel

theorem k517002_norm2 : normAllB I2 J2 CZC = true := by
  decide +kernel

theorem k517002_normS : (normAllB I1 J1 SC && normAllB I2 J2 SC) = true := by
  decide +kernel

theorem k517002_q8S : q8InCheck (SC.filter ord4B) I1 J1 I2 J2 = true := by
  decide +kernel

theorem k517002_q8CZ : q8InCheck (CZC.filter ord4B) I1 J1 I2 J2 = true := by
  decide +kernel

theorem k517002_edge : (edgeB I1 J1 I2 J2 SG && factB I1 J1 I2 J2 [SG] PA FPa &&
    factB I1 J1 I2 J2 [SG] PB FPb && factB I1 J1 I2 J2 [SG] SG [SG]) = true := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.K517002

end
