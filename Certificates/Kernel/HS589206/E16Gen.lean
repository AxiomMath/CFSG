module

public import Certificates.Kernel.HS589206.E16M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BfsRecK
public import Certificates.Data.Kernel.HS589206E16
public import Certificates.Kernel.HS589207.M

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HS589206.E16Gen

open CFSG.KC.DcHSOutK CFSG.KC.Enum CFSG.KD.HS589207 CFSG.KD.HS589206.E16
  CFSG.Quasithin.H13.LocDbl.HSLoc

theorem gens : allN 3 (fun t => eqF (GS t) (CFSG.KC.E64F.wordF A (sWords.getD t [])) &&
    eqF (GS5 t) (CFSG.KC.E64F.wordF A (s5Words.getD t []))) = true := by
  quickRfl

end CFSG.KD.HS589206.E16Gen

end
