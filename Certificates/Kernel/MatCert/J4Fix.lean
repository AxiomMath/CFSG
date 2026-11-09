module

public import Certificates.Data.Kernel.OpsMcertN
public import CFSG.Certificates.Kernel.OpsMNSplit
public import Certificates.Kernel.MatCert.J4Seeds
public import CFSG.RankThree.PartTwo.Sec4.T444.ONanItem434SporJ4Data
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData6
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.RankThree.PartTwo.Sec4.ONanJ4Nine CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

#kc_regs_mn j4FS1 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4Prog 0 102) (initN (opsF2K 112) JA.M JB.M j4Nregs)) width 12544 count 820

#kc_regs_mn j4FS2 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4Prog 102 102) j4FS1) width 12544 count 820

#kc_regs_mn j4FS3 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4Prog 204 102) j4FS2) width 12544 count 820

#kc_regs_mn j4FS4 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4Prog 306 103) j4FS3) width 12544 count 820

#kc_regs_mn j4FS5 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4Prog 409 102) j4FS4) width 12544 count 820

#kc_regs_mn j4FS6 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4Prog 511 102) j4FS5) width 12544 count 820

#kc_regs_mn j4FS7 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4Prog 613 102) j4FS6) width 12544 count 820

#kc_regs_mn j4FS8 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4Prog 715 103) j4FS7) width 12544 count 820

@[expose] def j4FCuts : List Nat := [0, 102, 204, 306, 409, 511, 613, 715, 818]

@[expose] noncomputable def j4FSn : Nat → List Nat
  | 0 => initN (opsF2K 112) JA.M JB.M j4Nregs
  | 1 => j4FS1
  | 2 => j4FS2
  | 3 => j4FS3
  | 4 => j4FS4
  | 5 => j4FS5
  | 6 => j4FS6
  | 7 => j4FS7
  | 8 => j4FS8
  | _ => []

theorem j4FSeg0 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4Prog (j4FCuts.getD 0 0)
    (j4FCuts.getD (0 + 1) 0 - j4FCuts.getD 0 0)) (j4FSn 0) (j4FSn (0 + 1)) = true := by
  quickRfl

theorem j4FSeg1 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4Prog (j4FCuts.getD 1 0)
    (j4FCuts.getD (1 + 1) 0 - j4FCuts.getD 1 0)) (j4FSn 1) (j4FSn (1 + 1)) = true := by
  quickRfl

theorem j4FSeg2 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4Prog (j4FCuts.getD 2 0)
    (j4FCuts.getD (2 + 1) 0 - j4FCuts.getD 2 0)) (j4FSn 2) (j4FSn (2 + 1)) = true := by
  quickRfl

theorem j4FSeg3 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4Prog (j4FCuts.getD 3 0)
    (j4FCuts.getD (3 + 1) 0 - j4FCuts.getD 3 0)) (j4FSn 3) (j4FSn (3 + 1)) = true := by
  quickRfl

theorem j4FSeg4 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4Prog (j4FCuts.getD 4 0)
    (j4FCuts.getD (4 + 1) 0 - j4FCuts.getD 4 0)) (j4FSn 4) (j4FSn (4 + 1)) = true := by
  quickRfl

theorem j4FSeg5 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4Prog (j4FCuts.getD 5 0)
    (j4FCuts.getD (5 + 1) 0 - j4FCuts.getD 5 0)) (j4FSn 5) (j4FSn (5 + 1)) = true := by
  quickRfl

theorem j4FSeg6 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4Prog (j4FCuts.getD 6 0)
    (j4FCuts.getD (6 + 1) 0 - j4FCuts.getD 6 0)) (j4FSn 6) (j4FSn (6 + 1)) = true := by
  quickRfl

theorem j4FSeg7 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4Prog (j4FCuts.getD 7 0)
    (j4FCuts.getD (7 + 1) 0 - j4FCuts.getD 7 0)) (j4FSn 7) (j4FSn (7 + 1)) = true := by
  quickRfl

theorem j4FRun : runS (opsF2K 112) j4Prog (initN (opsF2K 112) JA.M JB.M j4Nregs) = j4FS8 :=
  runS_of_cuts _ j4Prog j4FCuts j4FSn 8 rfl (Nat.le_of_ble_eq_true (by quickRfl)) (by decide)
    fun j hj => match j, hj with
    | 0, _ => j4FSeg0
    | 1, _ => j4FSeg1
    | 2, _ => j4FSeg2
    | 3, _ => j4FSeg3
    | 4, _ => j4FSeg4
    | 5, _ => j4FSeg5
    | 6, _ => j4FSeg6
    | 7, _ => j4FSeg7
    | _ + 8, h => absurd h (by omega)

theorem j4Fix_K : regsN (opsF2K 112) JA.M JB.M j4Nregs j4Prog
    (fun R => certN (opsF2K 112) R ⟨j4Nregs, j4Prog, j4Spec.facts⟩ &&
      (opsF2K 112).eq (getN R j4Spec.rA) JA.M && (opsF2K 112).eq (getN R j4Spec.rB) JB.M) =
    true :=
  regsN_of_runS_init _ _ _ _ _ _ _ j4FRun (by quickRfl)

#kc_regs_mn j4SS1 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4_7_claims.prog 0 186) (initN (opsF2K 112) JA.M JB.M j4_7_claims.nregs)) width 12544 count 755

#kc_regs_mn j4SS2 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4_7_claims.prog 186 186) j4SS1) width 12544 count 755

#kc_regs_mn j4SS3 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4_7_claims.prog 372 187) j4SS2) width 12544 count 755

#kc_regs_mn j4SS4 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4_7_claims.prog 559 186) j4SS3) width 12544 count 755

#kc_regs_mn j4SS5 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4_7_claims.prog 745 187) j4SS4) width 12544 count 755

#kc_regs_mn j4SS6 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4_7_claims.prog 932 186) j4SS5) width 12544 count 755

#kc_regs_mn j4SS7 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4_7_claims.prog 1118 186) j4SS6) width 12544 count 755

#kc_regs_mn j4SS8 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4_7_claims.prog 1304 187) j4SS7) width 12544 count 755

#kc_regs_mn j4SS9 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4_7_claims.prog 1491 186) j4SS8) width 12544 count 755

#kc_regs_mn j4SS10 := packR 12544 (runS (opsF2K 112)
    (CFSG.KC.SliceGlue.slice j4_7_claims.prog 1677 187) j4SS9) width 12544 count 755

@[expose] def j4SCuts : List Nat := [0, 186, 372, 559, 745, 932, 1118, 1304, 1491, 1677, 1864]

@[expose] noncomputable def j4SSn : Nat → List Nat
  | 0 => initN (opsF2K 112) JA.M JB.M j4_7_claims.nregs
  | 1 => j4SS1
  | 2 => j4SS2
  | 3 => j4SS3
  | 4 => j4SS4
  | 5 => j4SS5
  | 6 => j4SS6
  | 7 => j4SS7
  | 8 => j4SS8
  | 9 => j4SS9
  | 10 => j4SS10
  | _ => []

theorem j4SSeg0 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4_7_claims.prog (j4SCuts.getD 0 0)
    (j4SCuts.getD (0 + 1) 0 - j4SCuts.getD 0 0)) (j4SSn 0) (j4SSn (0 + 1)) = true := by
  quickRfl

theorem j4SSeg1 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4_7_claims.prog (j4SCuts.getD 1 0)
    (j4SCuts.getD (1 + 1) 0 - j4SCuts.getD 1 0)) (j4SSn 1) (j4SSn (1 + 1)) = true := by
  quickRfl

theorem j4SSeg2 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4_7_claims.prog (j4SCuts.getD 2 0)
    (j4SCuts.getD (2 + 1) 0 - j4SCuts.getD 2 0)) (j4SSn 2) (j4SSn (2 + 1)) = true := by
  quickRfl

theorem j4SSeg3 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4_7_claims.prog (j4SCuts.getD 3 0)
    (j4SCuts.getD (3 + 1) 0 - j4SCuts.getD 3 0)) (j4SSn 3) (j4SSn (3 + 1)) = true := by
  quickRfl

theorem j4SSeg4 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4_7_claims.prog (j4SCuts.getD 4 0)
    (j4SCuts.getD (4 + 1) 0 - j4SCuts.getD 4 0)) (j4SSn 4) (j4SSn (4 + 1)) = true := by
  quickRfl

theorem j4SSeg5 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4_7_claims.prog (j4SCuts.getD 5 0)
    (j4SCuts.getD (5 + 1) 0 - j4SCuts.getD 5 0)) (j4SSn 5) (j4SSn (5 + 1)) = true := by
  quickRfl

theorem j4SSeg6 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4_7_claims.prog (j4SCuts.getD 6 0)
    (j4SCuts.getD (6 + 1) 0 - j4SCuts.getD 6 0)) (j4SSn 6) (j4SSn (6 + 1)) = true := by
  quickRfl

theorem j4SSeg7 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4_7_claims.prog (j4SCuts.getD 7 0)
    (j4SCuts.getD (7 + 1) 0 - j4SCuts.getD 7 0)) (j4SSn 7) (j4SSn (7 + 1)) = true := by
  quickRfl

theorem j4SSeg8 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4_7_claims.prog (j4SCuts.getD 8 0)
    (j4SCuts.getD (8 + 1) 0 - j4SCuts.getD 8 0)) (j4SSn 8) (j4SSn (8 + 1)) = true := by
  quickRfl

theorem j4SSeg9 : segOK (opsF2K 112) (CFSG.KC.SliceGlue.slice j4_7_claims.prog (j4SCuts.getD 9 0)
    (j4SCuts.getD (9 + 1) 0 - j4SCuts.getD 9 0)) (j4SSn 9) (j4SSn (9 + 1)) = true := by
  quickRfl

theorem j4SRun : runS (opsF2K 112) j4_7_claims.prog (initN (opsF2K 112) JA.M JB.M j4_7_claims.nregs) = j4SS10 :=
  runS_of_cuts _ j4_7_claims.prog j4SCuts j4SSn 10 rfl (Nat.le_of_ble_eq_true (by quickRfl)) (by decide)
    fun j hj => match j, hj with
    | 0, _ => j4SSeg0
    | 1, _ => j4SSeg1
    | 2, _ => j4SSeg2
    | 3, _ => j4SSeg3
    | 4, _ => j4SSeg4
    | 5, _ => j4SSeg5
    | 6, _ => j4SSeg6
    | 7, _ => j4SSeg7
    | 8, _ => j4SSeg8
    | 9, _ => j4SSeg9
    | _ + 10, h => absurd h (by omega)

theorem j4Sec_K : mcertN (opsF2K 112) JA.M JB.M
    ⟨j4_7_claims.nregs, j4_7_claims.prog, j4_7_claims.facts⟩ = true :=
  regsN_of_runS_init _ _ _ _ _ _ _ j4SRun (by quickRfl)

theorem j4Sec_neg : (!mcertN (opsF2K 112) JA.M JB.M ⟨2, [], [.eq [(0, 1)] [(1, 1)]]⟩) = true := by
  quickRfl

theorem j4Fix_neg : (!mcertN (opsF2K 112) JA.M JB.M ⟨2, [], [.ne [(0, 1)] [(0, 1)] 0]⟩) = true := by
  quickRfl

end CertificateChecks.KernelMC

end
