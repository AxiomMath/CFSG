module

public import Certificates.Data.Kernel.SporSch.HNXBind
public import CFSG.Certificates.Kernel.Local.HN.X.Data
public import CFSG.Sporadic.HNSchreier.EmbeddedOrbit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNXBind

open CFSG.KC.Enum CFSG.KC.LL CFSG.KS.SporSch CFSG.KD.LgHNX CFSG.Sporadic.HNSchreier.Native

theorem bindP : walkOK (parAt TX) (hnsOrbitData ()).parents (nat_lit 0) = true := by quickRfl
theorem bindL : walkOK (labAt TX) (hnsOrbitData ()).labels (nat_lit 0) = true := by quickRfl

theorem neg_parAt : Bool.not (parAt TX (nat_lit 1) (nat_lit 1)) = true := by quickRfl
theorem neg_labAt : Bool.not (labAt TX (nat_lit 1) (nat_lit 1)) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNXBind

end
