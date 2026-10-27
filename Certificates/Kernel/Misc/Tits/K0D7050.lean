
module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Quasithin.Recognition.RuRank3TitsClsInputs
meta import CFSG.Quasithin.Recognition.RuRank3TitsClsInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Tits7050

meta def k0BaseM : Array Nat := #[0, 12, 1]

end CertificateChecks.KernelMisc.Tits7050

#ks_rawchain_sl2_data CertificateChecks.KernelMisc.TitsK0 1755 11 16 32
  CFSG.Quasithin.RuRank3.titsK0Strong CertificateChecks.KernelMisc.Tits7050.k0BaseM 3
  CFSG.Quasithin.RuRank3.titsK0Words

end
