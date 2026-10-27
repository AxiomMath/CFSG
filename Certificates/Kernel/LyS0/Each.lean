module

public import Certificates.Kernel.LyS0.Data
public import Certificates.Data.Kernel.LyS0.Check

public section

namespace CertificateChecks.KernelLyS0

open CFSG.KD.LyS0

@[expose] noncomputable def leftC (q : Nat) : Bool := leftK GI T (Nat.mul 81 q) 81

@[expose] noncomputable def sortC (q : Nat) : Bool := sortK GI T (Nat.mul 81 q) 81

end CertificateChecks.KernelLyS0

end
