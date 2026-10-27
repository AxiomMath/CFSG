module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative

public section

namespace CertificateChecks.KernelJ2Cover

open CFSG.ComponentClassification.J2Cover.Models

@[expose] def lamSrc : Array (Array Nat) :=
  #[Array.ofFn (n := 16384) (fun m =>
      (mulTab[m.val / 128]!)[betaTab[m.val % 128]!]! +
        128 * (if (lamBit (m.val % 128) ^^ fRows[m.val / 128]!.testBit betaTab[m.val % 128]!) then 1
          else 0)),
    Array.ofFn (n := 4725) (fun i =>
      invTab[aCoefT[i.val]!]! + 128 * (if fRows[invTab[aCoefT[i.val]!]!]!.testBit aCoefT[i.val]! then 1
        else 0)),
    Array.ofFn (n := 128) (fun a => betaTab[a.val]!),
    Array.ofFn (n := 128) (fun a => invTab[a.val]!)]

end CertificateChecks.KernelJ2Cover

end
