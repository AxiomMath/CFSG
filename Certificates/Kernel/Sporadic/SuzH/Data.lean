module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Sporadic.SuzI301Cover.Inputs
meta import CFSG.Sporadic.SuzI301Cover.Inputs
import CFSG.Sporadic.SuzI301.Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzHN CFSG.Sporadic.SuzI301Cover.Native.nHex

#kmisc_hexflat CertificateChecks.KernelSpor.SuzHN CFSG.Sporadic.SuzI301Cover.Native.nHex
  3 1782 11 2

#ks_chars CertificateChecks.KernelSpor.SuzHS CFSG.Sporadic.SuzI301.suzHex

#kmisc_hexflat CertificateChecks.KernelSpor.SuzHS CFSG.Sporadic.SuzI301.suzHex 3 1782 11 5

namespace CertificateChecks.KernelSpor.SuzH

open CFSG.KS.Raw

theorem nArr_eq {k : Nat} (hk : k < 2) :
    CFSG.Sporadic.SuzI301Cover.Native.nArr k = unpack 1782 11 (SuzHN.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzHN.all k hk
  rw [← SuzHN.eq] at h
  exact h

theorem suzArr_eq {k : Nat} (hk : k < 5) :
    CFSG.Sporadic.SuzI301.suzArr k = unpack 1782 11 (SuzHS.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzHS.all k hk
  rw [← SuzHS.eq] at h
  exact h

end CertificateChecks.KernelSpor.SuzH

end
