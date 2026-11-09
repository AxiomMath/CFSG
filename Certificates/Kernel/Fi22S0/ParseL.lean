module

public import Certificates.Kernel.Fi22S0.ParseChk
public import Certificates.Data.Kernel.LyS0.ParseW
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22S0

open CFSG.KD.LyS0

theorem ch131101pLW : parseW LRec 59049 LS.chars (nat_lit 0) (nat_lit 0) false = true := by
  quickRfl

theorem ch131101pL : parseOK LRec LS.chars 59049 = true := parseOK_of_parseW ch131101pLW

end CertificateChecks.KernelFi22S0

end
