module

public import Certificates.Kernel.ONKLat.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.ON5.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONKL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.ONSchreier
open CertificateChecks.KernelSpor

theorem ch812105_y5 : yOK 5 y5 (List.getD yPos 0 0) = true := by quickRfl

theorem ch812105_y7 : yOK 7 y7 (List.getD yPos 1 0) = true := by quickRfl

theorem ch812105_c5len : c5.length = 5 := by decide +kernel

theorem ch812105_c7len : c7.length = 7 := by decide +kernel

theorem ch812105_t : tOK = true := by quickRfl

theorem ch812105_bind : bindOK = true := by quickRfl

theorem ch812105_neg_sel : (!(cS y7 (2 :: c7) 0)) = true := by quickRfl

theorem ch812105_neg_y : (!(yOK 7 y5 (List.getD yPos 0 0))) = true := by quickRfl

theorem ch812105_neg_inv : (!(allN 512 (invK dP.dropLast))) = true := by quickRfl

theorem ch812105_neg_e : (!(allN 512 (eK (T32E.G 0) zP))) = true := by quickRfl

end CertificateChecks.KernelSpor.ONKL

#kon_slices CertificateChecks.KernelSpor.ONKL.c5S 0 20
#kon_slices CertificateChecks.KernelSpor.ONKL.c7S 0 20
#kon_join CertificateChecks.KernelSpor.ONKL.c5All CertificateChecks.KernelSpor.ONKL.c5S 20
#kon_join CertificateChecks.KernelSpor.ONKL.c7All CertificateChecks.KernelSpor.ONKL.c7S 20

end
