
module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
meta import CFSG.Monster.B.Fischer.PinnedChainData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22ChT CFSG.Monster.B.Fischer.fi22ChainStrongHex

#kmisc_hexflat CertificateChecks.KernelSpor.Fi22ChT CFSG.Monster.B.Fischer.fi22ChainStrongHex 3 3510 12 19

namespace CertificateChecks.KernelSpor.Fi22X

open CFSG.Monster.B.Fischer CFSG.KS.Raw

@[expose] def nilD : List (List Int) := []

theorem strong_eq {j : Nat} (hj : j < 19) : fi22StrongArrs[j]! = unpack 3510 12 (Fi22ChT.F j) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound Fi22ChT.all j hj
  rw [← Fi22ChT.eq] at h
  rw [fi22StrongArrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact h

end CertificateChecks.KernelSpor.Fi22X

end
