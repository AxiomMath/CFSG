module

public import Certificates.Kernel.M12Dc.Defs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.M12Dc

open CFSG.KC.SLDc

theorem glob : globalOK C D = true := by
  quickRfl

theorem pts : (List.range D.npc).all (ptChunk C D) = true := by
  quickRfl

theorem orbs : (List.range D.obase.length).all (orbOK C D) = true := by
  quickRfl

theorem chunks : (List.range D.Rc.length).all (chunkOK C D) = true := by
  quickRfl

theorem mems : (List.range 3).all memOK = true := by
  quickRfl

theorem tabsOK : (J.tabs.length == 8 && J.tabs.all fun t => t.length == 12 && t.all (· < 12)) =
    true := by
  quickRfl

theorem invs : (List.range 3).all (fun i => (List.range 12).all fun p =>
    L0 (Nat.add 5 i) (L0 (Nat.add 2 i) p) == p) = true := by
  quickRfl

end CFSG.KD.M12Dc

end
