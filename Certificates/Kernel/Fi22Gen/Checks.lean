module

public import Certificates.Data.Kernel.Fi22Gen.Defs
public import Certificates.Kernel.Fi22Gen.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Gen

open CFSG.KS.Fi22Gen CFSG.KD.Fi22Gen

set_option Elab.async false

theorem fg_tree_ok : treeK UL gw N root KP PL PI = true := by quickRfl
theorem fg_ord_ok : ordK w1 w2 = true := by quickRfl
theorem fg_trace_ok : traceK UL w1 w2 p1 p2 = true := by quickRfl
theorem fg_chain_ok : chainK p1 p2 lvW lvO lvP lvG = true := by quickRfl

end CertificateChecks.KernelFi22Gen

end
