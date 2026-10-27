module

public import Certificates.Data.Kernel.SporSch.LyFiveRel
public import Certificates.Kernel.SporSch.Ly.FiveLanesData
public import Certificates.Kernel.SporSch.Ly.FiveTbData
public import CFSG.Certificates.Kernel.Y333.Dispatch
import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.SporSch.Ly.FiveRelGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kc_eval CertificateChecks.KernelSporSch.LyFR L CertificateChecks.KernelSporSch.LyFiveRelGen.relStep

#kc_natDispatch CertificateChecks.KernelSporSch.LyFR.TT CertificateChecks.KernelSporSch.LyFR.L.t 2880 4
#kc_natDispatch CertificateChecks.KernelSporSch.LyFR.VP CertificateChecks.KernelSporSch.LyFR.L.vp 20 4
#kc_natDispatch CertificateChecks.KernelSporSch.LyFR.XP CertificateChecks.KernelSporSch.LyFR.L.xp 5 4
#kc_natDispatch CertificateChecks.KernelSporSch.LyFR.PA CertificateChecks.KernelSporSch.LyFR.L.pa 25 4
#kc_natDispatch CertificateChecks.KernelSporSch.LyFR.PB CertificateChecks.KernelSporSch.LyFR.L.pb 125 4
#kc_natDispatch CertificateChecks.KernelSporSch.LyFR.PC CertificateChecks.KernelSporSch.LyFR.L.pc 625 4

#ks_chars CertificateChecks.KernelSporSch.LyFRN CFSG.RankThree.Native.lyFiveNextHex
#kmisc_hexflat CertificateChecks.KernelSporSch.LyFRN CFSG.RankThree.Native.lyFiveNextHex 3 5760 12 1

#ks_chars CertificateChecks.KernelSporSch.LyFRQ CFSG.RankThree.Native.lyFiveQHex
#kmisc_hexflat CertificateChecks.KernelSporSch.LyFRQ CFSG.RankThree.Native.lyFiveQHex 3 5760 12 1

namespace CertificateChecks.KernelSporSch.LyFR

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyFiveRel CertificateChecks.KernelSporSch.LyBS

@[expose] noncomputable def NF (q : Nat) : Nat := mul (PC (Nat.div q (nat_lit 5))) (XP (Nat.mod q (nat_lit 5)))

end CertificateChecks.KernelSporSch.LyFR

end
