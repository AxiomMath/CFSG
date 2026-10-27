module

public import Certificates.Data.Kernel.SporSch.HNXBind
public import CFSG.Certificates.Kernel.Local.HN.X.Data
public import CFSG.Sporadic.HNSchreier.EmbeddedOrbit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNXBind

open CFSG.KC.Enum CFSG.KC.LL CFSG.KS.SporSch CFSG.KD.LgHNX CFSG.Sporadic.HNSchreier.Native

theorem bindA : walkOK (imgAt TX (nat_lit 0)) (hnsOrbitData ()).alpha (nat_lit 0) = true := by
  quickRfl
theorem bindB : walkOK (imgAt TX (nat_lit 1)) (hnsOrbitData ()).beta (nat_lit 0) = true := by
  quickRfl

theorem neg_imgAt : Bool.not (imgAt TX (nat_lit 0) (nat_lit 0)
    (fldW (getRec TX (nat_lit 464) (nat_lit 0)) (nat_lit 420) (nat_lit 21))) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNXBind

end
