module

public import Certificates.Kernel.OmegaEight.C3006D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelO8.C3006

open CFSG.EvenSmallLie.OmegaEight.Cover CFSG.KC.CycTabW

theorem covR : onesOKW 240 8 D.TR (coverWs.map (List.map codeW)) = true := by
  quickRfl

theorem uR : onesOKW 240 8 D.TR [(uWord ++ uWord).map codeW] = true := by
  quickRfl

theorem tuR : (!eqOKW 240 8 D.TR ((tuWord ++ tuWord).map codeW) fun x => x) = true := by
  quickRfl

end CertificateChecks.KernelO8.C3006

end
