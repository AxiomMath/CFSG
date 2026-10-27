module

public import Certificates.Kernel.J2Sig12648.Data
public import Certificates.Kernel.J2Sig12648.TwoData
public import Certificates.Kernel.Misc.Perm.J2EnumData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelJ2Sig

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum
open CertificateChecks.KernelMisc.J2En (EL)
open CertificateChecks.KernelMisc.J2C3 (keyF)
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2 (twoSets)

@[expose] noncomputable def GT (s k : Nat) : Nat :=
  VV (Nat.add (Nat.mul 3 ((twoSets.getD s []).getD (Nat.div k 3) 0)) (Nat.mod k 3))

theorem ch12648hd0 : headK 315 9 6 64 (GT 0) (lget T0P) = true := by decide +kernel
theorem ch12648hd1 : headK 315 9 6 64 (GT 1) (lget T1P) = true := by decide +kernel
theorem ch12648hd2 : headK 315 9 6 64 (GT 2) (lget T2P) = true := by decide +kernel
theorem ch12648hd3 : headK 315 9 9 64 (GT 3) (lget T3P) = true := by decide +kernel
theorem ch12648hd4 : headK 315 9 9 64 (GT 4) (lget T4P) = true := by decide +kernel
theorem ch12648hd5 : headK 315 9 9 64 (GT 5) (lget T5P) = true := by decide +kernel

theorem ch12648pt0 : CFSG.KC.LQT.P.allN 64
    (pointK 315 9 6 64 (GT 0) (lget T0P) (EL 6 T0E) (lget T0R) (lget T0L)) = true := by decide +kernel
theorem ch12648pt1 : CFSG.KC.LQT.P.allN 64
    (pointK 315 9 6 64 (GT 1) (lget T1P) (EL 6 T1E) (lget T1R) (lget T1L)) = true := by decide +kernel
theorem ch12648pt2 : CFSG.KC.LQT.P.allN 64
    (pointK 315 9 6 64 (GT 2) (lget T2P) (EL 6 T2E) (lget T2R) (lget T2L)) = true := by decide +kernel
theorem ch12648pt3 : CFSG.KC.LQT.P.allN 64
    (pointK 315 9 9 64 (GT 3) (lget T3P) (EL 9 T3E) (lget T3R) (lget T3L)) = true := by decide +kernel
theorem ch12648pt4 : CFSG.KC.LQT.P.allN 64
    (pointK 315 9 9 64 (GT 4) (lget T4P) (EL 9 T4E) (lget T4R) (lget T4L)) = true := by decide +kernel
theorem ch12648pt5 : CFSG.KC.LQT.P.allN 64
    (pointK 315 9 9 64 (GT 5) (lget T5P) (EL 9 T5E) (lget T5R) (lget T5L)) = true := by decide +kernel

theorem ch12648ky0 : CFSG.KC.LQT.P.allN 64 (keyF (lget T0P)) = true := by decide +kernel
theorem ch12648ky1 : CFSG.KC.LQT.P.allN 64 (keyF (lget T1P)) = true := by decide +kernel
theorem ch12648ky2 : CFSG.KC.LQT.P.allN 64 (keyF (lget T2P)) = true := by decide +kernel
theorem ch12648ky3 : CFSG.KC.LQT.P.allN 64 (keyF (lget T3P)) = true := by decide +kernel
theorem ch12648ky4 : CFSG.KC.LQT.P.allN 64 (keyF (lget T4P)) = true := by decide +kernel
theorem ch12648ky5 : CFSG.KC.LQT.P.allN 64 (keyF (lget T5P)) = true := by decide +kernel

theorem ch12648twoNeg : CFSG.KC.LQT.P.allN 64
    (pointK 315 9 6 64 (GT 1) (lget T0P) (EL 6 T0E) (lget T0R) (lget T0L)) = false := by
  decide +kernel

end CertificateChecks.KernelJ2Sig
