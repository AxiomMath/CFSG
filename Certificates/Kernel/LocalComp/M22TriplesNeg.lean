module

public import Certificates.Kernel.LocalComp.M22TriplesCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.M22TrNeg

open CFSG.KC.Triple CFSG.KLie.CT CertificateChecks.KernelLC

theorem swap : notB (treeOK M22Tr.G1 M22Tr.G0 M22Tr.T M22Tr.N 145) = true := by quickRfl

theorem extra : notB (treeOK M22Tr.G0 M22Tr.G1 M22Tr.T (M22Tr.N + 1) 145) = true := by quickRfl

theorem blocks : notB (treeOK M22Tr.G0 M22Tr.G1 M22Tr.T M22Tr.N 144) = true := by quickRfl

end CertificateChecks.KernelLC.M22TrNeg

end
