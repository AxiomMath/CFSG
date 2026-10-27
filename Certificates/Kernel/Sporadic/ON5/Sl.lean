
module

public import Certificates.Kernel.Sporadic.ON5.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON5K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.ONSchreier

theorem m_hd : penumHdK (pidn 120 7) ON5M.cnt 50000 ON5M.T ON5M.PL = true := by quickRfl

theorem m_gens : gensK Data.M120Chain.generators 120 7 ON5M.k ON5M.G = true := by quickRfl

theorem d_gens : gensK Data.D120Generators 120 7 4 dG = true := by quickRfl

theorem t_sel : tSelOK = true := by quickRfl

theorem small_ok : smallOK = true := by quickRfl

end CertificateChecks.KernelSpor.ON5K

#kon_slices CertificateChecks.KernelSpor.ON5K.mSl 0 20
#kon_slices CertificateChecks.KernelSpor.ON5K.dSelS 0 20

end
