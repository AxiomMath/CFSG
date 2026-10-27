module

public import Certificates.Kernel.LocalComp.Tits.Bind
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.Tits

open CFSG.KC.LocalComp.Tits CFSG.SectionRank.Native.Tits

theorem kCubic : cubicK 1755 11 TG CP titsSylow3 = true := by quickRfl

theorem kSquare : squareK 1755 11 TG CP titsSylow5 = true := by quickRfl

theorem sylow3 : cubicOK titsSylow3 = true := cubicOK_of_K gens_eq check_eq kCubic

theorem sylow5 : squareOK titsSylow5 = true := squareOK_of_K gens_eq check_eq kSquare

end CertificateChecks.KernelLC.Tits
