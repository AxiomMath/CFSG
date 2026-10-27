module

public import Certificates.Data.Kernel.EvenSporCocode.Defs
public meta import Certificates.Kernel.EvenSporCocode.Gen
public import CFSG.Certificates.Kernel.Common.Eval

public section

#kc_eval CertificateChecks.KernelCocode D CertificateChecks.KernelCocode.stepCocode

namespace CertificateChecks.KernelCocode

open CFSG.KC.EvenSporCocode

@[expose] noncomputable def rowsF (b : ℕ) : Bool := rowsBlk D.EP D.RB D.LT D.KT b

@[expose] noncomputable def dfsF (k : ℕ) : Bool := dfsSubK D.RB D.LT D.IV ((D.IV.drop (16 * k)).take 16)

end CertificateChecks.KernelCocode

end
