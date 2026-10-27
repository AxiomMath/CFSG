module

public import Certificates.Data.Kernel.RuDc.Defs
public import Certificates.Kernel.LocalQT.Base.C4143D
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.RuDc

open CFSG.KC.SLDc

theorem glob : globalOK C D = true := by
  quickRfl

theorem pts : (List.range D.npc).all (ptChunk C D) = true := by
  quickRfl

theorem orbs : (List.range D.obase.length).all (orbOK C D) = true := by
  quickRfl

theorem mems : (List.range 5).all memOK = true := by
  quickRfl

theorem incl : inclOK = true := by
  quickRfl

theorem invs : invOK = true := by
  quickRfl

theorem codes : (List.range 8).all (fun l =>
    J.lc.getD l 0 == CFSG.KD.LQT.C4143.TF (nodes.getD l 0)) = true := by
  quickRfl

end CFSG.KD.RuDc

end
