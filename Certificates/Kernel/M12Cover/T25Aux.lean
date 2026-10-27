module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsTransversalCheckInputs

public section

namespace CertificateChecks.KernelM12T

open CFSG.ComponentClassification.M12Cover.InternalSylow

def sigInv : Array Nat := Id.run do
  let mut a := Array.replicate 1485 0
  for i in [0:1485] do
    a := a.set! sigArr[i]! i
  return a

end CertificateChecks.KernelM12T

end
