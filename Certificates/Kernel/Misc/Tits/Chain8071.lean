module

public import Certificates.Data.Kernel.Misc.TitsChain
public import CFSG.Certificates.Kernel.YModel.TextGenS
public import Certificates.Kernel.Sporadic.RawGenOrb
public import CFSG.Quasithin.Recognition.CertDataTits
meta import CFSG.Quasithin.Recognition.CertDataTits
meta import CFSG.Sporadic.Schreier.TitsArrays
meta import Certificates.Data.CFSGNative.YGroups.ExactCheck

set_option maxRecDepth 400000

#ym_texts CertificateChecks.KernelMisc.TitsCT CFSG.Quasithin.titsChainText 32 1

public section

namespace CertificateChecks.KernelMisc.TitsCT

open CFSG.KC.YModel CFSG.KC.TitsChain

@[expose] noncomputable def words : List (List Int) := linesWK (lget El) 32 F lines

end CertificateChecks.KernelMisc.TitsCT

end

namespace CertificateChecks.KernelMisc.TitsCT

meta def strongM : Array (Array Nat) :=
  (CFSG.YGroups.ModelNative.strongOf 1755
    #[CFSG.Sporadic.Schreier.Tits.titsDerivedArrs[0]!, CFSG.Sporadic.Schreier.Tits.titsDerivedArrs[1]!]
    (CFSG.YGroups.ModelNative.chainWords CFSG.Quasithin.titsChainText)).1

meta def baseM : Array Nat := #[0, 1, 3, 6, 5, 24, 12]

end CertificateChecks.KernelMisc.TitsCT

#ks_raworb CertificateChecks.KernelMisc.TitsCh 1755 11 64 CertificateChecks.KernelMisc.TitsCT.strongM
  CertificateChecks.KernelMisc.TitsCT.baseM 2 CertificateChecks.KernelMisc.TitsCT.words
