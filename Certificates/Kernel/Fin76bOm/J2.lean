module

public import Certificates.Kernel.Sporadic.OddCore.J2Cent
public import CFSG.Certificates.Kernel.Local.Core
meta import CFSG.Sporadic.SmallOddCore.J2DataInputs
public meta import Certificates.Kernel.Fin76bOm.Meta
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Fin76bOm.Meta

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelC24608

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

meta def j2OmIdx (k : Nat) : Nat := if k < 4 then 32 + k else 31

meta def j2OmM : Array Nat :=
  orbitM ((List.range 4).toArray.map fun k => natArr (j2CentTbl (32 + k))) 10

meta def j2OmPM : Array (Array Nat) := #[j2OmM]

meta def j2OmTM : Array (Array Nat) :=
  (List.range 5).toArray.map fun k => restrM j2OmM (natArr (j2CentTbl (j2OmIdx k)))

end CertificateChecks.KernelC24608

#kmisc_packarrs CertificateChecks.KernelC24608.J2OmP CertificateChecks.KernelC24608.j2OmPM 9

#kmisc_packarrs CertificateChecks.KernelC24608.J2OmT CertificateChecks.KernelC24608.j2OmTM 6

namespace CertificateChecks.KernelC24608

open CFSG.KC.Enum CFSG.KC.Local CFSG.KS CertificateChecks.KernelSpor

@[expose] noncomputable def j2OmG (k : Nat) : Nat :=
  J2CentT.F (nIf(Nat.blt k (nat_lit 4), Nat.add (nat_lit 32) k, nat_lit 31))

@[expose] noncomputable def j2OmR (k : Nat) : Bool :=
  restrOK (nat_lit 9) (mask 9) (j2OmG k) (J2OmP 0) (nat_lit 9) (mask 9) (nat_lit 32) (J2OmT k)
    (nat_lit 6) (mask 6)

theorem j2Om_pts : ptsOK (nat_lit 315) (J2OmP 0) (nat_lit 9) (mask 9) (nat_lit 32) = true := by
  quickRfl

theorem j2Om_restr : allN 5 j2OmR = true := by
  quickRfl

end CertificateChecks.KernelC24608

end
