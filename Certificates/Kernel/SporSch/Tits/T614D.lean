module

public import Certificates.Kernel.SporSch.Tits.Abel2261
public import Certificates.Kernel.Sporadic.Tits.LocH
public import Certificates.Kernel.Sporadic.Tits.LocJ
public import Certificates.Kernel.Sporadic.Tits.LocK
public import Certificates.Kernel.Sporadic.Tits.LocN
public import Certificates.Kernel.SporSch.Tits.GenList
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TInputs
public meta import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.T614

meta def eGenM : List (Array Nat) := (List.range 5).map CFSG.Quasithin.H13.Tits614.eGenArr

meta def g1M : Array Nat := CFSG.Sporadic.Schreier.Tits.titsGenArrs[1]!

meta def pInvM : Array Nat :=
  CFSG.Monster.B.Co2.Native.invCand 1755 CFSG.Quasithin.H13.Tits614.pArr

end CertificateChecks.KernelSporSch.T614

#ks_perm CertificateChecks.KernelSporSch.T614P 11 CFSG.Quasithin.H13.Tits614.pArr
#ks_perm CertificateChecks.KernelSporSch.T614PI 11 CertificateChecks.KernelSporSch.T614.pInvM
#ks_perm CertificateChecks.KernelSporSch.T614G1 11 CertificateChecks.KernelSporSch.T614.g1M
#kst_plist CertificateChecks.KernelSporSch.T614EG 11 CertificateChecks.KernelSporSch.T614.eGenM
#kst_plist CertificateChecks.KernelSporSch.T614EL 11 CFSG.Quasithin.H13.Tits614.eArrs

namespace CertificateChecks.KernelSporSch.T614

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSpor

@[expose] noncomputable def sfJ (X : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsJ.LR TitsJ.TRI TitsJ.BP 4 0 X

@[expose] noncomputable def sfK (X : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsK.LR TitsK.TRI TitsK.BP 5 0 X

end CertificateChecks.KernelSporSch.T614

end
