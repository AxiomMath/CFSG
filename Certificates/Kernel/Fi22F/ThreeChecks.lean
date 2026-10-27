module

public import Certificates.Data.Kernel.Fi22F.Three
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelFi22F

open CFSG.KC CFSG.KC.Fi22F.Three CFSG.KC.Fi22B.Cov CFSG.Sporadic.Presentation.Fi22Exact

theorem xf_ok : xfOK = true := by quickRfl

theorem rels_ok : relsOK = true := by quickRfl

theorem g1_ok : g1OK = true := by quickRfl

theorem neg_e01 : notB (allOne [[(0, true), (1, true)]]) = true := by quickRfl

theorem neg_pw : notB (allOne [Pw]) = true := by quickRfl

end CertificateChecks.KernelFi22F

end
