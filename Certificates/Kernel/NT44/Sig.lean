module

public import Certificates.Kernel.NT44.Pack
public import Certificates.Kernel.NT44.Pack2
public import Certificates.Data.Kernel.Misc.ConjTab
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CertificateChecks.KernelNT44

open CFSG.GH74.GLS.NT44.PermutationNative CFSG.KC.Misc.ConjTab
open CFSG.KC.LQT.P (allN)
open CFSG.KC.Misc.Clos (allR)

theorem nt44_sig0 : allR 0 64 (sigAt 2688 12 nt44Sig nt44L nt44LI nt44KS) = true := by quickRfl
theorem nt44_sig1 : allR 64 64 (sigAt 2688 12 nt44Sig nt44L nt44LI nt44KS) = true := by quickRfl
theorem nt44_sig2 : allR 128 64 (sigAt 2688 12 nt44Sig nt44L nt44LI nt44KS) = true := by
  quickRfl
theorem nt44_sig3 : allR 192 64 (sigAt 2688 12 nt44Sig nt44L nt44LI nt44KS) = true := by
  quickRfl
theorem nt44_sig4 : allR 256 64 (sigAt 2688 12 nt44Sig nt44L nt44LI nt44KS) = true := by
  quickRfl
theorem nt44_sig5 : allR 320 64 (sigAt 2688 12 nt44Sig nt44L nt44LI nt44KS) = true := by
  quickRfl
theorem nt44_sig6 : allR 384 64 (sigAt 2688 12 nt44Sig nt44L nt44LI nt44KS) = true := by
  quickRfl
theorem nt44_sig7 : allR 448 64 (sigAt 2688 12 nt44Sig nt44L nt44LI nt44KS) = true := by
  quickRfl

theorem nt44_sig_id : allN 2 (fun j => Nat.beq (nt44Sig j) (nt44KS j)) = true := by quickRfl

theorem nt44_inner : allN 9 (fun i => allN 2 fun j =>
    Nat.beq (cj3 2688 12 (nt44P0 i) (nt44KS j) (nt44P0I i))
      (nt44Sig (Nat.add (Nat.mul 2 (inn ())[i]!) j))) = true := by quickRfl

theorem nt44_sep : allR 0 256 (sepAt 2688 12 nt44Sig 0 217) = true := by quickRfl

end CertificateChecks.KernelNT44

end
