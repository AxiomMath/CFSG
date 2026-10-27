module

public import Certificates.Kernel.Fi23K.ChkDefs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kon_slices CFSG.KD.Fi23K.miscSl 0 8

namespace CFSG.KD.Fi23K

set_option Elab.async false

theorem dep_ok : depK = true := by quickRfl
theorem bfs_ok : bfsK = true := by quickRfl
theorem cover_ok : coverK = true := by quickRfl
theorem sift_ok : siftChk = true := by quickRfl
theorem move_ok : moveK = true := by quickRfl

end CFSG.KD.Fi23K

end
