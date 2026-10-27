module

public import Certificates.Kernel.Sporadic.Fi22.N3153Data
public import Certificates.Data.Kernel.Fi22Nbr3153
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveData
import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

#kc_repo #kc_ktree CFSG.KD.N9551 O "Certificates/Kernel/Sporadic/Fi22/data/ord9551.bin" 7020 4 7020 17777888114129074559

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.B9551

meta def xsM : Array (Array Nat) := #[CFSG.AGLEmbedding.KFactProofs.Fi22Five.xA]

end CertificateChecks.KernelSpor.B9551

#kmisc_packarrs CertificateChecks.KernelSpor.B9551.UX CertificateChecks.KernelSpor.B9551.xsM 12

namespace CertificateChecks.KernelSpor.B9551

open CFSG.KC.N3153 CFSG.KD.N3153

@[expose] def pts : List Nat := [48, 752, 788, 1425, 847, 221]

@[expose] def bnds : List Nat := [10, 3, 2, 2, 5, 2]

@[expose] noncomputable def cellB (s : Nat) : Bool :=
  cellK (nat_lit 3510) S (UX (nat_lit 0)) pts (nat_lit 4) s (bnds.getD s (nat_lit 0))

@[expose] noncomputable def injB (_ : Nat) : Bool :=
  injK (nat_lit 3510) S (UX (nat_lit 0)) pts (nat_lit 4) (CFSG.KD.N9551.O (nat_lit 0))

end CertificateChecks.KernelSpor.B9551

#kc_slices CertificateChecks.KernelSpor.B9551.Cell CertificateChecks.KernelSpor.B9551.cellB 6
#kc_slices CertificateChecks.KernelSpor.B9551.Inj CertificateChecks.KernelSpor.B9551.injB 1

end
