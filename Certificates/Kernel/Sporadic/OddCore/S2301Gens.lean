module

public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Sporadic.SuzOddCore.InvGraphCheckInputs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CertificateChecks.KernelSpor.S2301

open CFSG.Sporadic.SuzOddCore

meta def gensM : Array (Array Nat) :=
  #[b0Arr, b1Arr, vArr, tArr 0, tArr 1, tArr 2, tArr 3]

end CertificateChecks.KernelSpor.S2301

#kmisc_packarrs CertificateChecks.KernelSpor.S2301.GP CertificateChecks.KernelSpor.S2301.gensM 12

end
