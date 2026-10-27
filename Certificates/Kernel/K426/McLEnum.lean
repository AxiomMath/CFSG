module

public import Certificates.Data.K426McL
public import Certificates.Kernel.B3S3.Gen
public import CFSG.Sporadic.Schreier.PairMcLCheckInputs
public meta import Certificates.Data.K426McL
public meta import CFSG.Sporadic.Schreier.PairMcLCheckInputs
public meta import Certificates.Kernel.B3S3.Gen

public section

set_option maxRecDepth 400000

#kb3_enum CertificateChecks.KernelK426.EQ CFSG.RankThree.PartTwo.KFacts.K426.mcl3QGens
  CFSG.Sporadic.Schreier.PairMcL.baseArr 275 9
#kb3_enum CertificateChecks.KernelK426.EO CFSG.RankThree.PartTwo.KFacts.K426.mcl3OGens
  CFSG.Sporadic.Schreier.PairMcL.baseArr 275 9
#kb3_enum CertificateChecks.KernelK426.EB CFSG.RankThree.PartTwo.KFacts.K426.mcl3CBGens
  CFSG.Sporadic.Schreier.PairMcL.baseArr 275 9

end
