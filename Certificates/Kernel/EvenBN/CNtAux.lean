
module

public import Certificates.Kernel.EvenBN.CNt
public import CFSG.Quasithin.Recognition.RuRank3TitsClsInputs
public meta import CFSG.Quasithin.Recognition.RuRank3TitsClsInputs
public meta import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelEvenBN.TAux CFSG.Quasithin.RuRank3.titsAuxText
#kmisc_hexflat CertificateChecks.KernelEvenBN.TAux CFSG.Quasithin.RuRank3.titsAuxText 3 1755 11 1

public section

namespace CertificateChecks.KernelEvenBN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsInv
open CertificateChecks.KernelSpor.Tits2268 CFSG.KC.BfsPin

@[expose] noncomputable def PN (k : Nat) : Nat := prodCode 1755 11 (mask 11) (1755 * 11) TitsN.LR TitsN.TR k

theorem cAux : C (TAux.F 0) := by quickRfl

end CertificateChecks.KernelEvenBN

end
