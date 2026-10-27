module

public import Certificates.Kernel.M11Dc.Defs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.M11Dc

open CFSG.KC.SLDc

theorem glob : globalOK C D = true := by
  quickRfl

theorem pts : (List.range D.npc).all (ptChunk C D) = true := by
  quickRfl

theorem orbs : (List.range D.obase.length).all (orbOK C D) = true := by
  quickRfl

theorem chunks : (List.range D.Rc.length).all (chunkOK C D) = true := by
  quickRfl

theorem mems : (List.range 4).all memOK = true := by
  quickRfl

theorem ots : (List.range 4).all otOK = true := by
  quickRfl

theorem tabsOK : (J.tabs.length == 6 && J.tabs.all fun t => t.length == 11 && t.all (· < 11)) =
    true := by
  quickRfl

theorem invs : (List.range 2).all (fun i => (List.range 11).all fun p =>
    L0 (Nat.add 4 i) (L0 (Nat.add 2 i) p) == p) = true := by
  quickRfl

end CFSG.KD.M11Dc

end
