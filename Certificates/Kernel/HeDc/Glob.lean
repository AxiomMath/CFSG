module

public import Certificates.Kernel.HeDc.Defs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.HeDc

open CFSG.KC.SLDc

theorem glob : globalOK C D = true := by
  quickRfl

theorem pts : (List.range D.npc).all (ptChunk C D) = true := by
  quickRfl

theorem orbs : (List.range D.obase.length).all (orbOK C D) = true := by
  quickRfl

theorem mems : (List.range 11).all memOK = true := by
  quickRfl

theorem incl : inclOK = true := by
  quickRfl

theorem invs : (List.range 4).all (fun i => (List.range 8330).all fun p =>
    L (Nat.add 6 i) (L (Nat.add 2 i) p) == p) = true := by
  quickRfl

end CFSG.KD.HeDc

end
