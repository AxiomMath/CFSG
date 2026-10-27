module

public import Certificates.Kernel.HS799102.M12Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

open CFSG.KC.PCent CFSG.KC.Enum CFSG.KC.Misc.ArrEnum

theorem ch799102_m12perm : (allN 2 (fun k => permB 100 7 (mG12 k)) &&
    allN 4 (fun k => permB 100 7 (aW12 k))) = true := by quickRfl

theorem ch799102_m12mem : (allN 2 (fun k => memK (mG12 k) (TH.F 2) && memK (mG12 k) (TH.F 3)) &&
    allN 4 (fun k => memK (aW12 k) (TH.F 2) && memK (aW12 k) (TH.F 3))) = true := by quickRfl

theorem ch799102_m12y : (Nat.blt Y12 4 && !Nat.beq (pcomp 100 7 (CFSG.KS.mask 7) (mG3 Y12) (TH.F 2))
    (pcomp 100 7 (CFSG.KS.mask 7) (TH.F 2) (mG3 Y12))) = true := by quickRfl

theorem ch799102_m12n : (stabLowK 100 7 mG12 2 N12 && baseInK N12 (maskK O12) &&
    Nat.beq ((N12.map fun lv => lv.2.2.2.length).prod) 1440) = true := by quickRfl

theorem ch799102_m12o : oddOrbK 100 7 dG12 2 X12 (maskK O12) O12 = true := by quickRfl

theorem ch799102_m12w : normK 100 7 mG12 2 dG12 2 W12 = true := by quickRfl

end CertificateChecks.KernelHS799102

end
