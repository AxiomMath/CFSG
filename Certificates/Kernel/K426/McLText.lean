module

public import Certificates.Data.K426McL
public import Certificates.Data.Kernel.Misc.HexFlat
public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.StrChunks
public meta import Certificates.Data.K426McL
import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Common.StrChunks

public section

set_option maxRecDepth 4000000

#str_chunks CertificateChecks.KernelK426.McLKT CFSG.RankThree.PartTwo.KFacts.K426.mcl3Hex 300000
  4000000 4096

#kmisc_hexflat CertificateChecks.KernelK426.McLKT CFSG.RankThree.PartTwo.KFacts.K426.mcl3Hex 3
  275 9 339

end
