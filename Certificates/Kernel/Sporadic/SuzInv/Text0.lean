module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Sporadic.SuzOddCore.InvArrays
meta import CFSG.Sporadic.SuzOddCore.InvArrays
import all CFSG.Sporadic.SuzOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Sporadic.SuzOddCore.Arrays
meta import CFSG.Sporadic.SuzOddCore.Arrays

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzInvT0 CFSG.Sporadic.SuzOddCore.invCase0Text

#kmisc_hexflat CertificateChecks.KernelSpor.SuzInvT0 CFSG.Sporadic.SuzOddCore.invCase0Text
  3 1782 11 82

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.Sporadic.SuzOddCore CFSG.KS.Raw

theorem run_eq0 {k : Nat} (hk : k < 82) : invRun 0 k = unpack 1782 11 (SuzInvT0.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzInvT0.all k hk
  rw [← SuzInvT0.eq] at h
  exact h

end CertificateChecks.KernelSpor.SuzInv

end
