module

public import Certificates.Kernel.LocalComp.BfsGenKey
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.PermData
public meta import CFSG.OddTranspositions.PartThree.Eleven.Minus.PermData

public section

namespace CertificateChecks.KernelMinusEnum

meta def rows : List (Array Nat) := CFSG.OddTranspositions.PartThree.minusTable.toList

end CertificateChecks.KernelMinusEnum

end

set_option maxRecDepth 400000

#lc_bfs_key CertificateChecks.KernelMinusEnum.ME CertificateChecks.KernelMinusEnum.rows
  CFSG.OddTranspositions.PartThree.minusBase 65 7 520
