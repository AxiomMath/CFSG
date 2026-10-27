module

public import Certificates.Kernel.R148Dc.J2BDefs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.R148Dc.J2B

open CFSG.KC.SLDc

theorem glob : globalOK C D = true := by
  quickRfl

theorem pts : (List.range D.npc).all (ptChunk C D) = true := by
  quickRfl

theorem orbs : (List.range D.obase.length).all (orbOKS C D 36) = true := by
  quickRfl

theorem chunks : (List.range D.Rc.length).all (chunkOK C D) = true := by
  quickRfl

theorem mems : (List.range 12).all memOK = true := by
  quickRfl

theorem tabsC : ((List.range 10).all fun l => J.tabs.getD l [] == (List.range 315).map (L l)) =
    true := by
  quickRfl

theorem invs : (List.range 4).all (fun i => (List.range 315).all fun p =>
    L (Nat.add 6 i) (L (Nat.add 2 i) p) == p) = true := by
  quickRfl

end CFSG.KD.R148Dc.J2B

end
