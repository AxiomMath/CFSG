module

public import Certificates.Kernel.HN27600.Data
public import Certificates.Kernel.HN25550.Data
public import Certificates.Kernel.HN25550.Enum
public import Certificates.Data.Kernel.Spor.PNode4
public import Certificates.Data.Kernel.HNMultK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN27600

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PNode CFSG.KS.PNode4 CFSG.KC.HNMult

theorem nodesA_ok : bAnd(Nat.beq (CFSG.KC.Ord.lenL NWA) 512,
    nodes4K 1100 11 (mask 11) 1024 CFSG.KD.HN25550.EP.T CFSG.KD.HN25550.EP.PL CFSG.KD.HN25550.PP
      SQ4 NWA 0) = true := by
  quickRfl

theorem nodesB_ok : bAnd(Nat.beq (CFSG.KC.Ord.lenL NWB) 512,
    nodes4K 1100 11 (mask 11) 1024 CFSG.KD.HN25550.EP.T CFSG.KD.HN25550.EP.PL CFSG.KD.HN25550.PP
      SQ4 NWB 512) = true := by
  quickRfl

theorem sq_ok : sqPathsK CFSG.KD.HN25550.EP.PL CFSG.KD.HN25550.PR SQ4 REL4 = true := by
  quickRfl

theorem rel_ok : REL4.all (relW CFSG.KD.HN25550.RB CFSG.KD.HN25550.mul 46 CFSG.KD.OrdHN.ONE) =
    true := by
  quickRfl

end CFSG.KD.HN27600

end
