module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.OddTranspositions.PartThree.Eleven.Plus.FrameCheck
public meta import CFSG.OddTranspositions.PartThree.Eleven.Plus.FrameCheck

public section

namespace CertificateChecks.KernelPlusFr

open CFSG.OddTranspositions.PartThree.PlusFrame

meta def dsArr : Array (Array Nat) := #[derivOrder, derivSrc]

meta def daArr : Array (Array Nat) := (dActions ()).toArray

end CertificateChecks.KernelPlusFr

end

#kmisc_packarrs CertificateChecks.KernelPlusFr.DS CertificateChecks.KernelPlusFr.dsArr 12

#kmisc_packarrs CertificateChecks.KernelPlusFr.DA CertificateChecks.KernelPlusFr.daArr 6
