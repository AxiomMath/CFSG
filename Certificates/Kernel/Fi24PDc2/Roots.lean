module

public import Certificates.Data.Kernel.Fi24PDc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi24PDc2

open CFSG.KC.SLD2

theorem roots_ok : (List.range D.roots.length).all (rootsOK C D) = true := by
  quickRfl

end CFSG.KD.Fi24PDc2

end
