module

public import CFSG.GH74.GLS.LU.Local.FiveStdInputs
public import Certificates.Data.Kernel.FiveStdKPl
public import Batteries.Data.List.Basic

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd

set_option maxRecDepth 200000 in
theorem cs_chain : (Cs.map fun x => keyC (codeE x)).IsChain (· < ·) := by decide +kernel

end CertificateChecks.FiveStd

end
