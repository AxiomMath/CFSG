module

public import Certificates.Kernel.HS589207.M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BfsRecK

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HS589207.Rec

open CFSG.KC.DcHSOutK CFSG.KC.BfsRecK CFSG.KC.Enum

theorem frec : recOK 4 3850 FP FL FPOS (keyF FR.TF) Fsig Fsinv (stF A FR.TF) = true := by
  quickRfl

theorem fent : (allN 3850 (fun i => (setT FR.TF i).all fun x => Nat.blt x 100) &&
    setT FR.TF 0 == [0, 1, 5, 21, 39, 50, 53, 61]) = true := by
  quickRfl

theorem crec : recOK 4 1100 CP CL CPOS (keyC CR.TF) Csig Csinv (stC A CR.TF) = true := by
  quickRfl

theorem cent : (allN 1100 (fun i => ltF (fl (CR.TF i))) && eqF (fl (CR.TF 0)) r0F) = true := by
  quickRfl

end CFSG.KD.HS589207.Rec

end
