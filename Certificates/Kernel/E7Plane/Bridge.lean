module

public import Certificates.Kernel.E7Plane.Data
public import CFSG.Blueprint.ChevalleyRootsInputs

public section

namespace CFSG.KD.E7Plane

open CFSG.Blueprint.Chevalley

theorem RV_eq_e7Certificate_roots : RV = e7Certificate.roots := by decide +kernel

theorem TB_eq_e7Certificate_table : TB = e7Certificate.table := by decide +kernel

end CFSG.KD.E7Plane

end
