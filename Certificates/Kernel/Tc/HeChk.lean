module

public import Certificates.Kernel.Tc.HeSrc
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.Tc.HeSrc

namespace CertificateChecks.KernelTc.He

open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

meta def ckM : Array (Array Nat) := (Array.range 150).map fun i =>
  let wd := heTcWs.getD (i / 10) []
  if 48 * (i % 10) ≤ wd.length + 47 then heThreeArr (wd.drop (48 * (i % 10))) else #[]

end CertificateChecks.KernelTc.He

public section

#kmisc_packarrs CertificateChecks.KernelTc.He.HC CertificateChecks.KernelTc.He.ckM 14

end
