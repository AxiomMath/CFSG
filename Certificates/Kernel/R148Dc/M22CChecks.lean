module

public import Certificates.Kernel.R148Dc.M22CDefs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.R148Dc.M22C

open CFSG.KC.SLDc

theorem glob : globalOK C D = true := by
  quickRfl

theorem pts : (List.range D.npc).all (ptChunk C D) = true := by
  quickRfl

theorem orbs : (List.range D.obase.length).all (orbOKS C D 36) = true := by
  quickRfl

theorem chunks : (List.range D.Rc.length).all (chunkOK C D) = true := by
  quickRfl

theorem mems : (List.range 8).all memOK = true := by
  quickRfl

theorem tabsOK : (J.tabs.length == 10 && J.tabs.all fun t => t.length == 22 && t.all (· < 22)) =
    true := by
  quickRfl

theorem invs : (List.range 4).all (fun i => (List.range 22).all fun p =>
    L0 (Nat.add 6 i) (L0 (Nat.add 2 i) p) == p) = true := by
  quickRfl

end CFSG.KD.R148Dc.M22C

end
