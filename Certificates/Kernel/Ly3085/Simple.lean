
module

public import Certificates.Kernel.Ly3085.SimpleBase

public import Certificates.Kernel.Ly3085.Card
public import Certificates.Kernel.Ly3085.Alg
public import CFSG.Sporadic.Ly.Setup
public import Certificates.Certificate9213Base

public section

namespace CertificateChecks.KernelLy

open CFSG.Sporadic.Ly

theorem isSimpleGroup_JS' :
    IsSimpleGroup JS := by
  obtain ⟨g, hg⟩ := orderOf_x
  exact isSimpleGroup_JS sA_sq sB_pow hg commutant_scalar card_JS

end CertificateChecks.KernelLy

end
