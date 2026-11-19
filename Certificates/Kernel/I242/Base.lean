module

public import CFSG.HardMathSupport.Solomon.Coordinator.I24_2Inputs

@[expose] public section

namespace CertificateChecks.KernelI242

def i242BaseA : Array Nat :=
  (CFSG.HardMathSupport.Solomon.Coordinator.i242Base.map Fin.val).toArray

end CertificateChecks.KernelI242

end
