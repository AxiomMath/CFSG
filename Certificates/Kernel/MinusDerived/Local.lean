module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.DerivedData
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.OddTranspositions.PartThree.Eleven.Minus.DerivedData

public section

namespace CertificateChecks.KernelMinusL

open CFSG.OddTranspositions.PartThree

@[expose] def locArr : Array (Array Nat) :=
  #[minusSylowA, minusSylowB, minusA5Gens[0]!, minusA5Gens[1]!]

meta def locM : Array (Array Nat) :=
  #[minusSylowA, minusSylowB, minusA5Gens[0]!, minusA5Gens[1]!]

end CertificateChecks.KernelMinusL

end

#kmisc_packarrs CertificateChecks.KernelMinusL.LX CertificateChecks.KernelMinusL.locM 7
