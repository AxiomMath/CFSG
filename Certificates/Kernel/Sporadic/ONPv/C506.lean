module

public import Certificates.Kernel.Sporadic.ON.Data
public import Certificates.Kernel.Sporadic.ONNQ.Tabs
public import Certificates.Kernel.Sporadic.ONPv.Data
public import Certificates.Data.Kernel.Spor.ONPvK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPv

open CFSG.KS.ONPv

theorem c506_b0 : c506At ON.TT ON.UU OPV.D (nat_lit 0) = true := by quickRfl

theorem c506_b1 : c506At ON.TT ON.UU OPV.D (nat_lit 227759) = true := by quickRfl

theorem c506_b2 : c506At ON.TT ON.UU OPV.D (nat_lit 100817) = true := by quickRfl

theorem c506_wit0 : c506WitR ON.TT ON.UU OPV.D (nat_lit 0) (nat_lit 28) = true := by quickRfl

theorem c506_wit1 : c506WitR ON.TT ON.UU OPV.D (nat_lit 28) (nat_lit 28) = true := by quickRfl

theorem c506_ln : c506Ln ONNQ.TT ONNQ.UU OPV.D (nat_lit 58818) = true := by quickRfl

end CertificateChecks.KernelSpor.ONPv

end
