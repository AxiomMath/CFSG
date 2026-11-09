module

public import Certificates.Kernel.J2Dc.Pts
public import Certificates.Kernel.J2Dc.Mems
public import Certificates.Kernel.J2Dc.Tabs
public import Certificates.Kernel.J2Dc.Chunk
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.J2Dc

open CFSG.KC.SLDc

@[expose] def orbc (j : Nat) : Bool := orbOKL C D J.P j

end CFSG.KD.J2Dc

#kss_each CFSG.KD.J2Dc.OrbK CFSG.KD.J2Dc.orbc 845

namespace CFSG.KD.J2Dc

open CFSG.KC.SLDc

theorem glob : globalOK C D = true := by
  quickRfl

theorem pts : (List.range D.npc).all (ptChunk C D) = true := by
  have hn : D.npc = 97 := rfl
  rw [hn, List.all_eq_true]
  intro i hi
  exact PtK.all i (List.mem_range.1 hi)

theorem orbs : (List.range D.obase.length).all (orbOKL C D J.P) = true := by
  have hn : D.obase.length = 845 := rfl
  rw [hn, List.all_eq_true]
  intro j hj
  exact OrbK.all j (List.mem_range.1 hj)

theorem osz : oszOK C D = true := by
  quickRfl

theorem mems : (List.range 5).all memOK = true :=
  List.all_eq_true.2 fun j hj => MemK.all j (List.mem_range.1 hj)

end CFSG.KD.J2Dc

end
