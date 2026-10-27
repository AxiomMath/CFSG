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

#ks_chars CertificateChecks.KernelSpor.SuzInvT2 CFSG.Sporadic.SuzOddCore.invCase2Text

#kmisc_hexflat CertificateChecks.KernelSpor.SuzInvT2 CFSG.Sporadic.SuzOddCore.invCase2Text
  3 1782 11 20

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.Sporadic.SuzOddCore CFSG.KS.Raw

theorem run_eq2 {k : Nat} (hk : k < 20) : invRun 2 k = unpack 1782 11 (SuzInvT2.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzInvT2.all k hk
  rw [← SuzInvT2.eq] at h
  exact h

end CertificateChecks.KernelSpor.SuzInv

end
