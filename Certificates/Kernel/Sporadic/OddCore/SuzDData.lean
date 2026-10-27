module

public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Sporadic.SuzOddCore.CTICheckInputs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CertificateChecks.KernelSpor.SuzDGen

meta def kM : Array (Array Nat) := CFSG.Sporadic.SuzOddCore.kGens 0

meta def kiM : Array (Array Nat) := CFSG.Sporadic.SuzOddCore.kInvs 0

end CertificateChecks.KernelSpor.SuzDGen

#kmisc_packarrs CertificateChecks.KernelSpor.SuzDK.K CertificateChecks.KernelSpor.SuzDGen.kM 6
#kmisc_packarrs CertificateChecks.KernelSpor.SuzDK.KI CertificateChecks.KernelSpor.SuzDGen.kiM 6

end
