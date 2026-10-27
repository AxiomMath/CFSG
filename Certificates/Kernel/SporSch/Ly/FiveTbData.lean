module

public import Certificates.Data.Kernel.SporSch.LyFiveTb
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.RankThree.Native.LyFiveArrays
import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.SporSch.Ly.FiveTbGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.LinearAlgebra.SelfAdjointRankFactorization
public import CFSG.RankThree.Native.LyFaithful
public import CFSG.RankThree.Native.LyFiveData
public import CFSG.RankThree.Native.LyFiveDataBase
public import CFSG.RankThree.Native.LySeedCheckBase
public import CFSG.RankThree.Native.LySeedOperatorBase
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import Certificates.Certificate3085Base

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.LyFTP CFSG.RankThree.Native.lyFiveParHex
#kmisc_hexflat CertificateChecks.KernelSporSch.LyFTP CFSG.RankThree.Native.lyFiveParHex 3 2880 12 1

#ks_chars CertificateChecks.KernelSporSch.LyFTG CFSG.RankThree.Native.lyFiveGenHex
#kmisc_hexflat CertificateChecks.KernelSporSch.LyFTG CFSG.RankThree.Native.lyFiveGenHex 3 2880 12 1

#kc_eval CertificateChecks.KernelSporSch.LyFT D CertificateChecks.KernelSporSch.LyFiveTbGen.tbStep

namespace CertificateChecks.KernelSporSch.LyFT

open CFSG.KC.LyFiveTb

theorem tb : tbOK D.G0 D.G1 (LyFTP.F 0) (LyFTG.F 0) D.KS = true := by quickRfl

theorem srt : sortOK D.SK D.RHO D.KS = true := by quickRfl

end CertificateChecks.KernelSporSch.LyFT

end
