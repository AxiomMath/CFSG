module

public import Certificates.Kernel.Sporadic.Fi24Net.Data
public import Certificates.Data.Kernel.Spor.Fi24NetPt
public import Certificates.Data.Kernel.Spor.Fi24Base
public import Certificates.Data.Kernel.Spor.Fi24FixP
public import Certificates.Data.Fi24ThreeFix
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi24Base

open CFSG.KC.Fi24Base CFSG.KC.Fi24NetPt CFSG.KC.Fi24FixP Timmesfeld.Fi24Cl

set_option Elab.async false

theorem cfg_ok : cfgG (eqB (letN CFSG.KD.Fi24Net.NW)) = true := by quickRfl

theorem inv_ok : invG (eqB (letN CFSG.KD.Fi24Net.NW)) = true := by quickRfl

theorem fix_ok : repFixData.all (fun d => fixOK (planeL CFSG.KD.Fi24Net.NW) d.1 d.2) = true := by
  quickRfl

end CFSG.KD.Fi24Base

end
