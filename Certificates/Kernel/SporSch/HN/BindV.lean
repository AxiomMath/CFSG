module

public import Certificates.Data.Kernel.SporSch.HNXBind
public import CFSG.Certificates.Kernel.Local.HN.X.Data
public import CFSG.Sporadic.HNSchreier.EmbeddedOrbit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNXBind

open CFSG.KC.Enum CFSG.KC.LL CFSG.KS.SporSch CFSG.KD.LgHNX CFSG.Sporadic.HNSchreier.Native

theorem bindV : walkOK (vecAt TX) (hnsOrbitData ()).vectors (nat_lit 0) = true := by quickRfl

theorem neg_vecAt : Bool.not (vecAt TX (nat_lit 1) (fldW (getRec TX (nat_lit 464) (nat_lit 0))
    (nat_lit 0) (nat_lit 399))) = true := by quickRfl
theorem neg_walk : Bool.not (walkOK (vecAt TX) (.leaf (nat_lit 399) (nat_lit 1)
    (fldW (getRec TX (nat_lit 464) (nat_lit 1)) (nat_lit 0) (nat_lit 399))) (nat_lit 0)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.HNXBind

end
