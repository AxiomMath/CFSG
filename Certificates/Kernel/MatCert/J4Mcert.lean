module

public import Certificates.Data.Kernel.OpsMcertN
public import CFSG.Certificates.Kernel.OpsMNSplit
public import Certificates.Kernel.MatCert.J4Seeds
public import CFSG.RankThree.Asc83Table.J4Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

#kc_regs_mn j4CS1 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog 0 615) (initN (opsF2K 112) JA.M JB.M CFSG.RankThree.Asc83Table.J4.j4Cert.nregs)) width 12544 count 88

#kc_regs_mn j4CS2 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog 615 615) j4CS1) width 12544 count 88

#kc_regs_mn j4CS3 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog 1230 615) j4CS2) width 12544 count 88

#kc_regs_mn j4CS4 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog 1845 615) j4CS3) width 12544 count 88

#kc_regs_mn j4CS5 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog 2460 615) j4CS4) width 12544 count 88

#kc_regs_mn j4CS6 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog 3075 615) j4CS5) width 12544 count 88

#kc_regs_mn j4CS7 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog 3690 615) j4CS6) width 12544 count 88

#kc_regs_mn j4CS8 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog 4305 615) j4CS7) width 12544 count 88

#kc_regs_mn j4CS9 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog 4920 615) j4CS8) width 12544 count 88

#kc_regs_mn j4CS10 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog 5535 615) j4CS9) width 12544 count 88

@[expose] def j4CCuts : List Nat := [0, 615, 1230, 1845, 2460, 3075, 3690, 4305, 4920, 5535, 6150]

@[expose] noncomputable def j4CSn : Nat → List Nat
  | 0 => initN (opsF2K 112) JA.M JB.M CFSG.RankThree.Asc83Table.J4.j4Cert.nregs
  | 1 => j4CS1
  | 2 => j4CS2
  | 3 => j4CS3
  | 4 => j4CS4
  | 5 => j4CS5
  | 6 => j4CS6
  | 7 => j4CS7
  | 8 => j4CS8
  | 9 => j4CS9
  | 10 => j4CS10
  | _ => []

theorem j4CSeg0 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog (j4CCuts.getD 0 0)
    (j4CCuts.getD (0 + 1) 0 - j4CCuts.getD 0 0)) (j4CSn 0) (j4CSn (0 + 1)) = true := by
  quickRfl

theorem j4CSeg1 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog (j4CCuts.getD 1 0)
    (j4CCuts.getD (1 + 1) 0 - j4CCuts.getD 1 0)) (j4CSn 1) (j4CSn (1 + 1)) = true := by
  quickRfl

theorem j4CSeg2 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog (j4CCuts.getD 2 0)
    (j4CCuts.getD (2 + 1) 0 - j4CCuts.getD 2 0)) (j4CSn 2) (j4CSn (2 + 1)) = true := by
  quickRfl

theorem j4CSeg3 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog (j4CCuts.getD 3 0)
    (j4CCuts.getD (3 + 1) 0 - j4CCuts.getD 3 0)) (j4CSn 3) (j4CSn (3 + 1)) = true := by
  quickRfl

theorem j4CSeg4 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog (j4CCuts.getD 4 0)
    (j4CCuts.getD (4 + 1) 0 - j4CCuts.getD 4 0)) (j4CSn 4) (j4CSn (4 + 1)) = true := by
  quickRfl

theorem j4CSeg5 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog (j4CCuts.getD 5 0)
    (j4CCuts.getD (5 + 1) 0 - j4CCuts.getD 5 0)) (j4CSn 5) (j4CSn (5 + 1)) = true := by
  quickRfl

theorem j4CSeg6 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog (j4CCuts.getD 6 0)
    (j4CCuts.getD (6 + 1) 0 - j4CCuts.getD 6 0)) (j4CSn 6) (j4CSn (6 + 1)) = true := by
  quickRfl

theorem j4CSeg7 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog (j4CCuts.getD 7 0)
    (j4CCuts.getD (7 + 1) 0 - j4CCuts.getD 7 0)) (j4CSn 7) (j4CSn (7 + 1)) = true := by
  quickRfl

theorem j4CSeg8 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog (j4CCuts.getD 8 0)
    (j4CCuts.getD (8 + 1) 0 - j4CCuts.getD 8 0)) (j4CSn 8) (j4CSn (8 + 1)) = true := by
  quickRfl

theorem j4CSeg9 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice CFSG.RankThree.Asc83Table.J4.j4Cert.prog (j4CCuts.getD 9 0)
    (j4CCuts.getD (9 + 1) 0 - j4CCuts.getD 9 0)) (j4CSn 9) (j4CSn (9 + 1)) = true := by
  quickRfl

theorem j4CRun : runS (opsF2K 112) CFSG.RankThree.Asc83Table.J4.j4Cert.prog (initN (opsF2K 112) JA.M JB.M CFSG.RankThree.Asc83Table.J4.j4Cert.nregs) = j4CS10 :=
  runS_of_cuts _ CFSG.RankThree.Asc83Table.J4.j4Cert.prog j4CCuts j4CSn 10 rfl (Nat.le_of_ble_eq_true (by quickRfl)) (by decide)
    fun j hj => match j, hj with
    | 0, _ => j4CSeg0
    | 1, _ => j4CSeg1
    | 2, _ => j4CSeg2
    | 3, _ => j4CSeg3
    | 4, _ => j4CSeg4
    | 5, _ => j4CSeg5
    | 6, _ => j4CSeg6
    | 7, _ => j4CSeg7
    | 8, _ => j4CSeg8
    | 9, _ => j4CSeg9
    | _ + 10, h => absurd h (by omega)

theorem j4_K : mcertN (opsF2K 112) JA.M JB.M CFSG.RankThree.Asc83Table.J4.j4Cert = true :=
  regsN_of_runS_init _ _ _ _ _ _ _ j4CRun (by quickRfl)

theorem j4_neg : (!mcertN (opsF2K 112) JA.M JB.M ⟨2, [], [.ord 0 3]⟩) = true := by
  quickRfl

end CertificateChecks.KernelMC

end
