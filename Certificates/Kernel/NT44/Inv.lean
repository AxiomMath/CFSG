module

public import Certificates.Kernel.NT44.Pack
public import Certificates.Data.Kernel.Misc.PermClos
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CertificateChecks.KernelNT44

open CFSG.KC.Enum (permOK)
open CFSG.KS (mask)
open CFSG.KC.LQT.P (allN)
open CFSG.KC.Misc.Clos (allR)

theorem nt44_inv_ks : allN 2 (fun i => permOK 2688 12 (mask 12) (2688 * 12) (nt44KS i)
    (nt44KSI i)) = true := by quickRfl

theorem nt44_inv_p0 : allN 9 (fun i => permOK 2688 12 (mask 12) (2688 * 12) (nt44P0 i)
    (nt44P0I i)) = true := by quickRfl

theorem nt44_inv_l0 : allR 0 64 (fun i => permOK 2688 12 (mask 12) (2688 * 12) (nt44L i)
    (nt44LI i)) = true := by quickRfl

theorem nt44_inv_l1 : allR 64 64 (fun i => permOK 2688 12 (mask 12) (2688 * 12) (nt44L i)
    (nt44LI i)) = true := by quickRfl

theorem nt44_inv_l2 : allR 128 64 (fun i => permOK 2688 12 (mask 12) (2688 * 12) (nt44L i)
    (nt44LI i)) = true := by quickRfl

theorem nt44_inv_l3 : allR 192 64 (fun i => permOK 2688 12 (mask 12) (2688 * 12) (nt44L i)
    (nt44LI i)) = true := by quickRfl

end CertificateChecks.KernelNT44

end
