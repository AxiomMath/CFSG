module

public import Certificates.Kernel.LocalComp.Tits.Bind
public import CFSG.Certificates.Kernel.LocalCompTits.Elem
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.Tits

open CFSG.KC.LocalComp.Tits CFSG.KC.LocalComp.TitsSound CFSG.SectionRank.Native.Tits

theorem kElem : elemK 1755 11 TG CP [0] [2, 26] [5, 6, 5] [16, 2, 5] [24, 2, 18] = true := by
  quickRfl

theorem kElemNegDup : (!elemK 1755 11 TG CP [0] [2, 26] [5, 6, 5] [16, 2, 5] [0]) = true := by
  quickRfl

theorem kElemNegInv : (!elemK 1755 11 TG CP [0] [2, 26] [5, 6, 5] [16, 2, 5] [4]) = true := by
  quickRfl

theorem elem : elemOK [0] [2, 26] [5, 6, 5] [16, 2, 5] [24, 2, 18] = true :=
  elemOK_of_K gens_eq check_eq kElem

end CertificateChecks.KernelLC.Tits
