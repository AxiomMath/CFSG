module

public import Certificates.Data.Kernel.LaneChain
public import Certificates.Kernel.Fi23U3.Regs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

public section

namespace CertificateChecks.KernelFi23U3

open CFSG.KC.LaneChain CertificateChecks.KernelTc.Fi23

noncomputable abbrev mul : Nat → Nat → Nat := lay.mul

noncomputable abbrev vld : Nat → Bool := CFSG.KC.Ord.validM lay.p (lay.d * lay.S) lay.L lay.H

theorem chain_ok : chainOK mul vld lay.S [] D.B D.G D.T M₀ (nat_lit 6377292) = true := by
  quickRfl

end CertificateChecks.KernelFi23U3

end
