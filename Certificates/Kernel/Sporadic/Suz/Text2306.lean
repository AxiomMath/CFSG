module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.MtxKSound
public import CFSG.Sporadic.SuzOddCore.Arrays
meta import CFSG.Sporadic.SuzOddCore.Arrays
import all CFSG.Sporadic.SuzOddCore.Arrays
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzSmallT CFSG.Sporadic.SuzOddCore.smallChainText

#kmisc_hexflat CertificateChecks.KernelSpor.SuzSmallT CFSG.Sporadic.SuzOddCore.smallChainText
  3 1782 11 14

#ks_chars CertificateChecks.KernelSpor.SuzVT CFSG.Sporadic.SuzOddCore.suzd2P1782M1Text

#ks_chars CertificateChecks.KernelSpor.SuzB0T CFSG.Sporadic.SuzOddCore.suzP1782M1Text

#ks_chars CertificateChecks.KernelSpor.SuzB1T CFSG.Sporadic.SuzOddCore.suzP1782M2Text

namespace CertificateChecks.KernelSpor.Suz2306

meta def vM : Array Nat := CFSG.Sporadic.SuzOddCore.vArr

meta def b0M : Array Nat := CFSG.Sporadic.SuzOddCore.b0Arr

meta def b1M : Array Nat := CFSG.Sporadic.SuzOddCore.b1Arr

end CertificateChecks.KernelSpor.Suz2306

#ks_perm CertificateChecks.KernelSpor.Suz2306.V 11 CertificateChecks.KernelSpor.Suz2306.vM

#ks_perm CertificateChecks.KernelSpor.Suz2306.B0 11 CertificateChecks.KernelSpor.Suz2306.b0M

#ks_perm CertificateChecks.KernelSpor.Suz2306.B1 11 CertificateChecks.KernelSpor.Suz2306.b1M

namespace CertificateChecks.KernelSpor.Suz2306

open CFSG.Sporadic.SuzOddCore CFSG.KS.Raw

theorem smallArr_eq {k : Nat} (hk : k < 14) : smallArr k = unpack 1782 11 (SuzSmallT.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzSmallT.all k hk
  rw [← SuzSmallT.eq] at h
  exact h

theorem vArr_eq : vArr = unpack 1782 11 V := by
  change mtxArr suzd2P1782M1Text = _
  rw [SuzVT.eq]
  exact CFSG.KC.Mtx.mtxK_sound (by quickRfl)

theorem b0Arr_eq : b0Arr = unpack 1782 11 B0 := by
  change mtxArr suzP1782M1Text = _
  rw [SuzB0T.eq]
  exact CFSG.KC.Mtx.mtxK_sound (by quickRfl)

theorem b1Arr_eq : b1Arr = unpack 1782 11 B1 := by
  change mtxArr suzP1782M2Text = _
  rw [SuzB1T.eq]
  exact CFSG.KC.Mtx.mtxK_sound (by quickRfl)

end CertificateChecks.KernelSpor.Suz2306

end
