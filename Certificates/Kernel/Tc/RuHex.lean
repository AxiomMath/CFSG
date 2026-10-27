module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.RuTcData
public import Certificates.Data.Kernel.Misc.HexFlat
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.GenPerms
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.RuTcData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc.Ru

open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.AGLEmbeddingD2.Wilson.ThetaSpor
  CFSG.AGLEmbeddingD2.Wilson.Census219

meta def invs3M : Array (Array Nat) := (Array.range 31).map fun k => invCand 4060 (ruArr3 k)

meta def invsTM : Array (Array Nat) := (Array.range 13).map fun k => invCand 4060 (ruTcArr k)

end CertificateChecks.KernelTc.Ru

#ks_chars CertificateChecks.KernelTc.Ru.R3 CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.ruThreeHex
#kmisc_hexflat CertificateChecks.KernelTc.Ru.R3 CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.ruThreeHex
  3 4060 12 31
#ks_chars CertificateChecks.KernelTc.Ru.RT CFSG.AGLEmbeddingD2.Wilson.Census219.ruTcHex
#kmisc_hexflat CertificateChecks.KernelTc.Ru.RT CFSG.AGLEmbeddingD2.Wilson.Census219.ruTcHex
  3 4060 12 13
#kss_perms CertificateChecks.KernelTc.Ru.I3 12 CertificateChecks.KernelTc.Ru.invs3M
#kss_perms CertificateChecks.KernelTc.Ru.IT 12 CertificateChecks.KernelTc.Ru.invsTM

end
