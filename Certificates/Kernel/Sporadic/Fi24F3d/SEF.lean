module

public import Certificates.Kernel.Sporadic.Fi24F3d.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange
import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.Fi24F3d

@[expose] def okEF (c : Nat) : Bool :=
  Nat.beq (CFSG.KC.Fi24FixK.cntFix CFSG.KC.Fi24G2d.idN CFSG.KD.Fi24Fix.TG [] WEF (Nat.mul 4096 c) 4096
    64) (CFSG.KC.Fi24Kn.nthN J.KEF c)

theorem SEF.last : Nat.beq (CFSG.KC.Fi24FixK.cntFix CFSG.KC.Fi24G2d.idN CFSG.KD.Fi24Fix.TG [] WEF
    303104 3832 64) (CFSG.KC.Fi24Kn.nthN J.KEF 74) = true := by quickRfl

end CFSG.KD.Fi24F3d

#kc_slice_range CFSG.KD.Fi24F3d.okEF CFSG.KD.Fi24F3d.SEF.c 0 74

namespace CFSG.KD.Fi24F3d

#kc_forall_tree SEF.all (fun c => okEF c = true) 74 CFSG.KD.Fi24F3d.SEF.c

end CFSG.KD.Fi24F3d

end
