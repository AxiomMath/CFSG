module

public import Certificates.Kernel.Sporadic.Fi22.N3153Data
public import Certificates.Data.Kernel.Fi22Nbr3153
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.Fi22.N3153Dil
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public meta import CFSG.Monster.B.Fischer.Fi22OuterArrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.N3153

meta def gensM : Array (Array Nat) :=
  #[CFSG.Monster.B.Fischer.fi22OrigArrs[0]!, CFSG.Monster.B.Fischer.fi22OrigArrs[1]!,
    (CFSG.Monster.B.Fischer.fi22OuterStrong3510 1)[0]!, Array.range 3510]

end CertificateChecks.KernelSpor.N3153

#kmisc_packarrs CertificateChecks.KernelSpor.N3153.GP CertificateChecks.KernelSpor.N3153.gensM 12

namespace CertificateChecks.KernelSpor.N3153

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.N3153

@[expose] noncomputable def rowB (s : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 64) s) (fun x => bIf(Nat.blt x (nat_lit 3510),
    rowOKW (nat_lit 3510) (nat_lit 693) R M S dilK x, true)) (nat_lit 64)

@[expose] noncomputable def imgB (k s : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 64) s) (fun x => bIf(Nat.blt x (nat_lit 3510),
    imgOK (nat_lit 3510) (nat_lit 693) (GP k) R M x, true)) (nat_lit 64)

@[expose] noncomputable def img0B (s : Nat) : Bool := imgB (nat_lit 0) s

@[expose] noncomputable def img1B (s : Nat) : Bool := imgB (nat_lit 1) s

@[expose] noncomputable def cellB (s : Nat) : Bool :=
  strictB (GP (nat_lit 3)) fun T => cellK (nat_lit 3510) S T [0, 1, 2, 3, 6, 4] (nat_lit 4) s
    ([3510, 2816, 567, 720, 16, 2].getD s (nat_lit 0))

end CertificateChecks.KernelSpor.N3153

end
