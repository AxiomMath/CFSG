module

public import Certificates.Kernel.SporSch.HN.Pt2108Defs
public import Certificates.Kernel.LocalQT.Tc.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt2108

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KC.LL.HNXT4 CFSG.KC.LL.HNXSyl CFSG.KS.EnumBase
open CFSG.KD.HNPt2108 CFSG.Sporadic.HNSchreier

theorem v0 : allN 22 (fun k => bAnd(Nat.beq (f14 (VRf 0) k) k,
    Nat.beq (f21 OM k) (g0 Data.baseList k))) = true := by quickRfl

theorem w0 : allN 6 (fun j => allN 22 fun k =>
    Nat.beq (f14 (SGf j) (f14 (WRf 0) (Nat.add (Nat.mul 22 j) k))) k) = true := by quickRfl

theorem om_lt : bAnd(Nat.beq (Nat.shiftRight OM (Nat.mul 21 15312)) 0,
    allN 15312 fun t => Nat.blt (f21 OM t) 1140000) = true := by quickRfl

theorem sg_lt : allN 6 (fun j => allN 15312 fun t => Nat.blt (f14 (SGf j) t) 15312) = true := by
  quickRfl

theorem key : allN 729 (fun i => Nat.beq (f42 KY i)
    (Nat.add (f21 OM (f14 (VRf i) 0)) (Nat.mul 2097152 (f21 OM (f14 (VRf i) 1))))) = true := by
  quickRfl

theorem neg_v : Bool.not (rowK SGf VRf PARf (fun _ => 0) 22 8) = true := by quickRfl
theorem neg_l : Bool.not (imgK SGf VRf 22 0 (Lf 1 5) 5) = true := by quickRfl
theorem neg_c : Bool.not (blockK SGf VRf WRf 22 0 (Cf 0 9) 10) = true := by quickRfl
theorem neg_d : Bool.not (Nat.beq (f42 KY 3) (Nat.add (f21 OM (f14 (VRf 4) 0))
    (Nat.mul 2097152 (f21 OM (f14 (VRf 4) 1))))) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNPt2108

set_option Elab.async false

#kqb_range CertificateChecks.KernelSporSch.HNPt2108.vK CertificateChecks.KernelSporSch.HNPt2108.vS 0 12
#kqb_all CertificateChecks.KernelSporSch.HNPt2108.vK CertificateChecks.KernelSporSch.HNPt2108.vS 12
#kqb_range CertificateChecks.KernelSporSch.HNPt2108.wK CertificateChecks.KernelSporSch.HNPt2108.wS 0 12
#kqb_all CertificateChecks.KernelSporSch.HNPt2108.wK CertificateChecks.KernelSporSch.HNPt2108.wS 12
#kqb_range CertificateChecks.KernelSporSch.HNPt2108.lK CertificateChecks.KernelSporSch.HNPt2108.lS 0 18
#kqb_all CertificateChecks.KernelSporSch.HNPt2108.lK CertificateChecks.KernelSporSch.HNPt2108.lS 18
#kqb_range CertificateChecks.KernelSporSch.HNPt2108.cK CertificateChecks.KernelSporSch.HNPt2108.cS 0 18
#kqb_all CertificateChecks.KernelSporSch.HNPt2108.cK CertificateChecks.KernelSporSch.HNPt2108.cS 18
#kqb_range CertificateChecks.KernelSporSch.HNPt2108.dK CertificateChecks.KernelSporSch.HNPt2108.dS 0 12
#kqb_all CertificateChecks.KernelSporSch.HNPt2108.dK CertificateChecks.KernelSporSch.HNPt2108.dS 12

end
