module

public import Certificates.Data.Kernel.Sp62Cen
public import Certificates.Kernel.Sp62.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp62

theorem cen899102_ok : cenK (REC 27) (REC 28) (REC 29) (recX REC 38) 2160 34 = true := by
  quickRfl

end CFSG.KD.Sp62

end
