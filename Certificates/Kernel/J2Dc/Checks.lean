module

public import Certificates.Kernel.J2Dc.Defs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.J2Dc

open CFSG.KC.SLDc

theorem glob : globalOK C D = true := by
  quickRfl

theorem pts : (List.range D.npc).all (ptChunk C D) = true := by
  quickRfl

theorem orbs : (List.range D.obase.length).all (orbOKL C D J.P) = true := by
  quickRfl

theorem osz : oszOK C D = true := by
  quickRfl

theorem chunks : (List.range D.Rc.length).all (chunkOK C D) = true := by
  quickRfl

theorem mems : (List.range 5).all memOK = true := by
  quickRfl

theorem tabsC : ((List.range 8).all fun l => J.tabs.getD l [] == (List.range 315).map (L0 l)) =
    true := by
  quickRfl

theorem invs : (List.range 3).all (fun i => (List.range 315).all fun p =>
    L0 (Nat.add 5 i) (L0 (Nat.add 2 i) p) == p) = true := by
  quickRfl

end CFSG.KD.J2Dc

end
