module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.FrameCheck
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.OddTranspositions.PartThree.Eleven.Minus.FrameCheck

public section

namespace CertificateChecks.KernelMinusFrame

open CFSG.OddTranspositions.PartThree.MinusFrame

meta def xts : Array (Array Nat) := #[tArr (), xArr] ++ t0Gens

end CertificateChecks.KernelMinusFrame

end

#kmisc_packarrs CertificateChecks.KernelMinusFrame.XT CertificateChecks.KernelMinusFrame.xts 7
