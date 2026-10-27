module

public import Certificates.Kernel.E8Plane.Data
public import Certificates.Data.E8KilledPlanes

public section

namespace CFSG.KD.E8Plane

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane

theorem RC_eq_e8Certificate_roots : RC = e8Certificate.roots := by decide +kernel

theorem TB_eq_e8Certificate_table : TB = e8Certificate.table := by decide +kernel

theorem QW_eq_e8PlaneWord : QW = (List.range 243).map e8PlaneWord := by decide +kernel

theorem RW_eq_e8PlaneWord : RW = [1, 4, 13, 40].map e8PlaneWord := by decide +kernel

end CFSG.KD.E8Plane

end
