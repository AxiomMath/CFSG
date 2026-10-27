module

public import Certificates.Kernel.SporSch.PairBT.McLData

public section

namespace CertificateChecks.KernelSporSch.McLBT

open CFSG.KS.SporSch.MBT

@[expose] def wConds : List (List Bool × Nat) :=
  [([false, true], 11), ([false, true, false, true, true, true, true], 5),
    ([false, true, true], 12),
    ([false, true, false, true, false, true, false, true, true, false, true, false, true, true,
      false, true, true], 7)]

@[expose] def ws3 : List (List Nat × Nat) := condWords wConds

end CertificateChecks.KernelSporSch.McLBT

end
