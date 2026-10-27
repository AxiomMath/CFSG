module

public import CFSG.Sporadic.Recognition.HSMultiplierInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG

public section

namespace CertificateChecks.KernelHSMult

open CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.HSMultiplier

@[expose] noncomputable def rels6 : List (List (Nat × Bool)) := hsRels.map encW

@[expose] noncomputable def cover6 : List (List (Nat × Bool)) := hsCover.map encW

end CertificateChecks.KernelHSMult

end
