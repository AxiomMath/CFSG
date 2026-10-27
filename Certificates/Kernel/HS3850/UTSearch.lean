module

public import Certificates.Kernel.HS3850.UTDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.ConjOrb
public import Certificates.Data.Kernel.PkPow

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHS3850.UT

open CFSG.KC.InvTabK

theorem rank6 : forallGreedyF 191 cK pK (fun _ => false) 6 [] = true := by quickRfl

theorem rank4 : forallGreedyF 191 cK pK pred4K 4 [] = true := by quickRfl

theorem rank5 : forallGreedyF 191 cK pK pred5K 5 [] = true := by quickRfl

end CertificateChecks.KernelHS3850.UT

end
