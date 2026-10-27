module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Misc.Perm.HexCmd
import Certificates.Kernel.SporSch.HN.GenHNX
meta import CFSG.Quasithin.Recognition.RuRank3T1CertInputs
import CFSG.Assembly.LowTwoRankDefs

namespace CertificateChecks.KernelRuT1

open CFSG.Quasithin.RuRank3

meta def npM : Array (Array Nat) := #[t1NT[194]!, t1NT[217]!, t1NT[260]!, t1NT[303]!]
meta def txM : Array (Array Nat) := t1GenReps.toArray.map fun x => t1T.getD x #[]
meta def uxM : Array (Array Nat) := t1GenReps.toArray.map fun x => t1U.getD x #[]
meta def dM : Array (Array Nat) := #[t1Ta, t1Tb]

end CertificateChecks.KernelRuT1

set_option maxRecDepth 400000

public section

#kmisc_packarrs CertificateChecks.KernelRuT1.NP CertificateChecks.KernelRuT1.npM 11
#kmisc_packarrs CertificateChecks.KernelRuT1.TX CertificateChecks.KernelRuT1.txM 11
#kmisc_packarrs CertificateChecks.KernelRuT1.UX CertificateChecks.KernelRuT1.uxM 11
#kmisc_packarrs CertificateChecks.KernelRuT1.D CertificateChecks.KernelRuT1.dM 11
#kss_strlits CertificateChecks.KernelRuT1.W CFSG.Quasithin.RuRank3.t1GenWords
#kss_strlits CertificateChecks.KernelRuT1.B CFSG.Quasithin.RuRank3.t1Bits

end
