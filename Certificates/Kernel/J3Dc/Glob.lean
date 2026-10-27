module

public import Certificates.Data.Kernel.J3Dc.Defs
public import Certificates.Kernel.Census.J3.Text
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.J3Dc

open CFSG.KC.SLDc

theorem glob : globalOK C D = true := by
  quickRfl

theorem pts : (List.range D.npc).all (ptChunk C D) = true := by
  quickRfl

theorem orbs : (List.range D.obase.length).all (orbOK C D) = true := by
  quickRfl

theorem mems : (List.range 5).all memOK = true := by
  quickRfl

theorem sb : sbOK = true := by
  quickRfl

theorem sgw : sgwOK = true := by
  quickRfl

theorem sg0 : sgOK 0 = true := by
  quickRfl

theorem sg1 : sgOK 1 = true := by
  quickRfl

theorem sg2 : sgOK 2 = true := by
  quickRfl

theorem invs : invOK = true := by
  quickRfl

theorem ab : abOK = true := by
  quickRfl

theorem codes : (Nat.beq (J.lc.getD 0 0) (CertificateChecks.KernelCensus.J3S.F 0) &&
    Nat.beq (J.lc.getD 1 0) (CertificateChecks.KernelCensus.J3S.F 1)) = true := by
  quickRfl

end CFSG.KD.J3Dc

end
