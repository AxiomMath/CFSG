module

public import Certificates.Kernel.Tc.HeSrc
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.Tc.HeSrc

namespace CertificateChecks.KernelTc.He

open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

meta def arrsM : Array (Array Nat) := heTcWs.toArray.map heThreeArr

meta def invsM : Array (Array Nat) := arrsM.map (CFSG.Monster.B.Co2.Native.invCand 8330)

end CertificateChecks.KernelTc.He

public section

#kmisc_packarrs CertificateChecks.KernelTc.He.HT CertificateChecks.KernelTc.He.arrsM 14

#kmisc_packarrs CertificateChecks.KernelTc.He.HTI CertificateChecks.KernelTc.He.invsM 14

end
