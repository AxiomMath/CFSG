module

public import Certificates.Kernel.Sporadic.Suz.Text2306
public import CFSG.Certificates.Kernel.Spor.PresCardK
public import Certificates.Kernel.Bounds.Suz.Binding
public meta import Certificates.Data.CFSGNative.Bridge.SuzGPL
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.SuzOddCore.Arrays
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Spor.PresCard
public import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Suz2306

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Bridge.SuzGPL.Native

meta def gensM : Array (Array Nat) := smallGenArrs
meta def gensIM : Array (Array Nat) := gensM.map (invCand 1782)
meta def imgM (k : Nat) : Array Nat := wordA 1782 gensM gensIM (imgWords[k]!)
meta def i0 : Array Nat := imgM 0
meta def i1 : Array Nat := imgM 1
meta def i2 : Array Nat := imgM 2
meta def i3 : Array Nat := imgM 3
meta def i4 : Array Nat := imgM 4
meta def i5 : Array Nat := imgM 5
meta def i6 : Array Nat := imgM 6
meta def j0 : Array Nat := invCand 1782 i0
meta def j1 : Array Nat := invCand 1782 i1
meta def j2 : Array Nat := invCand 1782 i2
meta def j3 : Array Nat := invCand 1782 i3
meta def j4 : Array Nat := invCand 1782 i4
meta def j5 : Array Nat := invCand 1782 i5
meta def j6 : Array Nat := invCand 1782 i6

end CertificateChecks.KernelSpor.Suz2306

#ks_perm CertificateChecks.KernelSpor.Suz2306.I0 11 CertificateChecks.KernelSpor.Suz2306.i0
#ks_perm CertificateChecks.KernelSpor.Suz2306.I1 11 CertificateChecks.KernelSpor.Suz2306.i1
#ks_perm CertificateChecks.KernelSpor.Suz2306.I2 11 CertificateChecks.KernelSpor.Suz2306.i2
#ks_perm CertificateChecks.KernelSpor.Suz2306.I3 11 CertificateChecks.KernelSpor.Suz2306.i3
#ks_perm CertificateChecks.KernelSpor.Suz2306.I4 11 CertificateChecks.KernelSpor.Suz2306.i4
#ks_perm CertificateChecks.KernelSpor.Suz2306.I5 11 CertificateChecks.KernelSpor.Suz2306.i5
#ks_perm CertificateChecks.KernelSpor.Suz2306.I6 11 CertificateChecks.KernelSpor.Suz2306.i6
#ks_perm CertificateChecks.KernelSpor.Suz2306.J0 11 CertificateChecks.KernelSpor.Suz2306.j0
#ks_perm CertificateChecks.KernelSpor.Suz2306.J1 11 CertificateChecks.KernelSpor.Suz2306.j1
#ks_perm CertificateChecks.KernelSpor.Suz2306.J2 11 CertificateChecks.KernelSpor.Suz2306.j2
#ks_perm CertificateChecks.KernelSpor.Suz2306.J3 11 CertificateChecks.KernelSpor.Suz2306.j3
#ks_perm CertificateChecks.KernelSpor.Suz2306.J4 11 CertificateChecks.KernelSpor.Suz2306.j4
#ks_perm CertificateChecks.KernelSpor.Suz2306.J5 11 CertificateChecks.KernelSpor.Suz2306.j5
#ks_perm CertificateChecks.KernelSpor.Suz2306.J6 11 CertificateChecks.KernelSpor.Suz2306.j6

namespace CertificateChecks.KernelSpor.Suz2306

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Pres

@[expose] noncomputable def Gs (i : Nat) : Nat :=
  nIf(Nat.beq i 0, I0, nIf(Nat.beq i 1, I1, nIf(Nat.beq i 2, I2, nIf(Nat.beq i 3, I3,
    nIf(Nat.beq i 4, I4, nIf(Nat.beq i 5, I5, I6))))))

@[expose] noncomputable def GIs (i : Nat) : Nat :=
  nIf(Nat.beq i 0, J0, nIf(Nat.beq i 1, J1, nIf(Nat.beq i 2, J2, nIf(Nat.beq i 3, J3,
    nIf(Nat.beq i 4, J4, nIf(Nat.beq i 5, J5, J6))))))

theorem imgsOK : allN 7 (fun i => bAnd(permOK 1782 11 (mask 11) (1782 * 11) (Gs i) (GIs i),
    bAnd(canonK 1782 11 (mask 11) (1782 * 11) (Gs i), canonK 1782 11 (mask 11) (1782 * 11) (GIs i))))
    = true := by
  quickRfl

@[expose] def surj0 : List (Nat × Bool) := [(6, false), (3, false), (1, false), (0, false),
  (2, false), (3, false), (1, false), (2, false), (0, false), (1, false), (0, false), (1, false),
  (3, false), (2, false), (3, false), (5, false), (1, false), (6, false), (1, false), (2, false),
  (3, false), (4, false), (3, false), (2, false), (3, false), (1, false), (2, false), (3, false),
  (4, false), (3, false), (2, false), (1, false), (0, false), (1, false), (3, false), (6, false),
  (5, false), (1, false), (0, false), (2, false)]

@[expose] def surj1 : List (Nat × Bool) := [(0, false), (6, false), (1, false), (5, false),
  (6, false), (3, false), (1, false), (0, false), (2, false), (3, false), (1, false), (2, false),
  (0, false), (1, false), (0, false), (1, false), (3, false), (2, false), (1, false), (6, false),
  (1, false), (0, false), (2, false), (3, false), (4, false), (3, false), (2, false), (3, false),
  (1, false), (2, false), (3, false), (4, false), (3, false), (2, false), (5, false), (1, false),
  (2, false), (3, false), (2, false), (1, false), (3, false), (4, false), (6, false)]

theorem surjOK0 : Nat.beq (wordPK 1782 11 Gs GIs surj0) (SuzSmallT.F 0) = true := by
  quickRfl

theorem surjOK1 : Nat.beq (wordPK 1782 11 Gs GIs surj1) (SuzSmallT.F 1) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Suz2306

end
