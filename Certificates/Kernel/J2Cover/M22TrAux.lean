module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative

public section

namespace CertificateChecks.KernelJ2Cover

open CFSG.ComponentClassification.J2Cover.Models

@[expose] def r7Src : Array (Array Nat) :=
  #[Array.ofFn (n := 16384) fun m =>
    (List.range 7).foldl (fun acc j =>
      acc ||| (if (if j < 6 then (hRowsT j)[m.val / 128]! else fRows[m.val / 128]!).testBit
        (m.val % 128) then 2 ^ j else 0)) 0]

end CertificateChecks.KernelJ2Cover

end
