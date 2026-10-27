module

public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import CFSG.Certificates.Kernel.Local.Core
meta import CFSG.Sporadic.SmallOddCore.J3DataInputs
public meta import Certificates.Kernel.Fin76bOm.Meta
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Fin76bOm.Meta

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelC24608

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

meta def j3OmIdx (k : Nat) : Nat := if k < 5 then 10 + k else 9

meta def j3OmM : Array Nat :=
  orbitM ((List.range 5).toArray.map fun k => natArr (j3CentTbl (10 + k))) 18

meta def j3OmPM : Array (Array Nat) := #[j3OmM]

meta def j3OmTM : Array (Array Nat) :=
  (List.range 6).toArray.map fun k => restrM j3OmM (natArr (j3CentTbl (j3OmIdx k)))

end CertificateChecks.KernelC24608

#kmisc_packarrs CertificateChecks.KernelC24608.J3OmP CertificateChecks.KernelC24608.j3OmPM 13

#kmisc_packarrs CertificateChecks.KernelC24608.J3OmT CertificateChecks.KernelC24608.j3OmTM 7

namespace CertificateChecks.KernelC24608

open CFSG.KC.Enum CFSG.KC.Local CFSG.KS CertificateChecks.KernelSpor

@[expose] noncomputable def j3OmG (k : Nat) : Nat :=
  J3CentP (nIf(Nat.blt k (nat_lit 5), Nat.add (nat_lit 10) k, nat_lit 9))

@[expose] noncomputable def j3OmR (k : Nat) : Bool :=
  restrOK (nat_lit 13) (mask 13) (j3OmG k) (J3OmP 0) (nat_lit 13) (mask 13) (nat_lit 80) (J3OmT k)
    (nat_lit 7) (mask 7)

theorem j3Om_pts : ptsOK (nat_lit 6156) (J3OmP 0) (nat_lit 13) (mask 13) (nat_lit 80) = true := by
  quickRfl

theorem j3Om_restr : allN 6 j3OmR = true := by
  quickRfl

end CertificateChecks.KernelC24608

end
