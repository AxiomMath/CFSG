module

public import Certificates.Data.K426McL
public import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Data.K426McL

public section

namespace CertificateChecks.KernelK426

@[expose] def dA : List (List Int) := CFSG.RankThree.PartTwo.KFacts.K426.mcl3ChainAWords.toList.drop 2

@[expose] def dB : List (List Int) := CFSG.RankThree.PartTwo.KFacts.K426.mcl3ChainBWords.toList.drop 2

end CertificateChecks.KernelK426

end

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelK426.MA 275 9 55
  CFSG.RankThree.PartTwo.KFacts.K426.mcl3ChainAArrs
  CFSG.RankThree.PartTwo.KFacts.K426.mcl3ChainABaseArr 2 CertificateChecks.KernelK426.dA

#ks_rawchain CertificateChecks.KernelK426.MB 275 9 55
  CFSG.RankThree.PartTwo.KFacts.K426.mcl3ChainBArrs
  CFSG.RankThree.PartTwo.KFacts.K426.mcl3ChainBBaseArr 2 CertificateChecks.KernelK426.dB
