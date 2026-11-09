module

public import Certificates.Kernel.LyGlue.Data
public import Certificates.Kernel.LyGlue.Hex
public import CFSG.Sporadic.Recognition.LyonsAmalgamGlueInputs
public import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LyGlue.Defs

public section

namespace CertificateChecks.KernelLy

open CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Recognition CFSG.KC.LyGlue CFSG.KC.Enum
  CFSG.KS

@[expose] def cdIdx (l : Int) : List Nat :=
  if l = 1 ∨ l = -1 then [1] else if l = 2 then [2] else [2, 2]

@[expose] def conjList : List (Nat × Nat × Nat × Nat) :=
  [(8, 3, 3, 8),
   (11, 3, 10, 11), (11, 8, 3, 11),
   (12, 3, 7, 12), (12, 8, 10, 12),
   (13, 3, 7, 13), (13, 8, 10, 13),
   (14, 3, 10, 14), (14, 8, 7, 14)]

end CertificateChecks.KernelLy

end
