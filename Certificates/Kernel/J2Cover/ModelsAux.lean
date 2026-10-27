module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsCosets

public section

namespace CertificateChecks.KernelJ2Cover

open CFSG.ComponentClassification.J2Cover.Models

@[expose] def cosetDepth : Array Nat := Id.run do
  let mut d : Array Nat := Array.replicate 4725 0
  for i in [1:4725] do
    d := d.set! i (d[cosetPar[i]!]! + 1)
  return d

end CertificateChecks.KernelJ2Cover

end
