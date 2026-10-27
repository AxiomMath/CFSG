module

public import CFSG.Sporadic.Recognition.LyonsAmalgamYData
public import CFSG.Sporadic.Recognition.LyonsAmalgamTrData
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Bounds.Core3
public meta import CFSG.Sporadic.Recognition.LyonsAmalgamYData
public meta import CFSG.Sporadic.Recognition.LyonsAmalgamTrData
import CFSG.Certificates.Kernel.Bounds.Load
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_blocked_root CertificateChecks.KernelLy.FY
  "Certificates/Kernel/LyGlue/data/FY.bin" 6 4 65535 133650 15602524896381769794
#kc_repo #kc_blocked_root CertificateChecks.KernelLy.FT
  "Certificates/Kernel/LyGlue/data/FT.bin" 6 4 65535 133650 5257218317091467996
#kc_repo #kc_blocked_root CertificateChecks.KernelLy.SY
  "Certificates/Kernel/LyGlue/data/SY.bin" 6 5 4294967295 4320 12467015261748865761
#kc_repo #kc_blocked_root CertificateChecks.KernelLy.ST
  "Certificates/Kernel/LyGlue/data/ST.bin" 6 5 4294967295 972 6668357711228452468

#ks_chars CertificateChecks.KernelLy.UH CFSG.Sporadic.Recognition.LyonsSims.Ly1080.uHex
#kmisc_hexflat CertificateChecks.KernelLy.UH CFSG.Sporadic.Recognition.LyonsSims.Ly1080.uHex
  3 1080 11 4

#ks_chars CertificateChecks.KernelLy.GH CFSG.Sporadic.Recognition.LyonsSims.Ly243.genHex
#kmisc_hexflat CertificateChecks.KernelLy.GH CFSG.Sporadic.Recognition.LyonsSims.Ly243.genHex
  2 243 8 5

#ks_chars CertificateChecks.KernelLy.LH CFSG.Sporadic.Recognition.LyonsSims.Ly243.lineHex
#kmisc_hexflat CertificateChecks.KernelLy.LH CFSG.Sporadic.Recognition.LyonsSims.Ly243.lineHex
  2 243 8 3

namespace CertificateChecks.KernelLy

@[expose] def yU : List Int := [1, 2, 3, 2, 1, 3, 4, 1, 4, 2]

@[expose] def xU : List Int := [3, 2, 3, 2, 3, 2, 3, 2, 3, 2]

end CertificateChecks.KernelLy

end
