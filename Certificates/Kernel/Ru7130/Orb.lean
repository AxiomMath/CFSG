module

public import Certificates.Data.Kernel.PcReach
public import Certificates.Data.Kernel.Ru7130.Data
public import Certificates.Kernel.Ru7130.Codes
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.HSA312.Defs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Ru7130

open CFSG.KC.Enum CFSG.KC.LQT.PcW CFSG.KC.PcReach

@[expose] noncomputable def Kc (i : Nat) : Nat := J.K.getD i 0

theorem kOrb : (reachC 12 4095 J.K 1 J.O0 && J.O0.length == 511) = true := by quickRfl

theorem hW : (J.hW.length == J.H.length && (List.range J.hW.length).all fun i =>
    (J.hW.getD i []).all (fun l => Nat.blt l J.K.length) &&
      Nat.beq (wordPB 4060 12 4095 Kc (J.hW.getD i []) I) (J.H.getD i 0)) = true := by
  quickRfl

theorem hFix : (J.H.all fun h => pg 12 4095 h 0 == 0) = true := by quickRfl

theorem hOrb : (reachC 12 4095 J.H 4 J.O1 && J.O1.length == 3) = true := by quickRfl

end CFSG.KD.Ru7130

end
