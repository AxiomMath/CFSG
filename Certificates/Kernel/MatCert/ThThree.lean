module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Kernel.LocalComp.ThOrder
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThThreeInputs
public import CFSG.Certificates.Kernel.OpsMNSplit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.AGLEmbedding.R3

#kc_regs_mn ThS1 := packR 61504 (runS (opsF2K 248)
    (CFSG.KC.SliceGlue.slice thThreeProg 0 98) (initN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M thThreeN)) width 61504 count 494

#kc_regs_mn ThS2 := packR 61504 (runS (opsF2K 248)
    (CFSG.KC.SliceGlue.slice thThreeProg 98 98) ThS1) width 61504 count 494

#kc_regs_mn ThS3 := packR 61504 (runS (opsF2K 248)
    (CFSG.KC.SliceGlue.slice thThreeProg 196 98) ThS2) width 61504 count 494

#kc_regs_mn ThS4 := packR 61504 (runS (opsF2K 248)
    (CFSG.KC.SliceGlue.slice thThreeProg 294 98) ThS3) width 61504 count 494

#kc_regs_mn ThS5 := packR 61504 (runS (opsF2K 248)
    (CFSG.KC.SliceGlue.slice thThreeProg 392 100) ThS4) width 61504 count 494

@[expose] def thCuts : List Nat := [0, 98, 196, 294, 392, 492]

@[expose] noncomputable def thSn : Nat → List Nat
  | 0 => initN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M thThreeN
  | 1 => ThS1
  | 2 => ThS2
  | 3 => ThS3
  | 4 => ThS4
  | 5 => ThS5
  | _ => []

theorem thSeg0 : segOK (opsF2K 248) (CFSG.KC.SliceGlue.slice thThreeProg (thCuts.getD 0 0)
    (thCuts.getD (0 + 1) 0 - thCuts.getD 0 0)) (thSn 0) (thSn (0 + 1)) = true := by
  quickRfl

theorem thSeg1 : segOK (opsF2K 248) (CFSG.KC.SliceGlue.slice thThreeProg (thCuts.getD 1 0)
    (thCuts.getD (1 + 1) 0 - thCuts.getD 1 0)) (thSn 1) (thSn (1 + 1)) = true := by
  quickRfl

theorem thSeg2 : segOK (opsF2K 248) (CFSG.KC.SliceGlue.slice thThreeProg (thCuts.getD 2 0)
    (thCuts.getD (2 + 1) 0 - thCuts.getD 2 0)) (thSn 2) (thSn (2 + 1)) = true := by
  quickRfl

theorem thSeg3 : segOK (opsF2K 248) (CFSG.KC.SliceGlue.slice thThreeProg (thCuts.getD 3 0)
    (thCuts.getD (3 + 1) 0 - thCuts.getD 3 0)) (thSn 3) (thSn (3 + 1)) = true := by
  quickRfl

theorem thSeg4 : segOK (opsF2K 248) (CFSG.KC.SliceGlue.slice thThreeProg (thCuts.getD 4 0)
    (thCuts.getD (4 + 1) 0 - thCuts.getD 4 0)) (thSn 4) (thSn (4 + 1)) = true := by
  quickRfl

theorem thRun : runS (opsF2K 248) thThreeProg (initN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M thThreeN) =
    ThS5 :=
  runS_of_cuts _ thThreeProg thCuts thSn 5 rfl (Nat.le_of_ble_eq_true (by quickRfl)) (by decide)
    fun j hj => match j, hj with
    | 0, _ => thSeg0
    | 1, _ => thSeg1
    | 2, _ => thSeg2
    | 3, _ => thSeg3
    | 4, _ => thSeg4
    | _ + 5, h => absurd h (by omega)

theorem thTz_K : regsN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M thThreeN thThreeProg
    (fun R => certN (opsF2K 248) R ⟨thThreeN, thThreeProg, thTzSpec.facts⟩ &&
      (opsF2K 248).eq (getN R 0) KernelLC.ThA.M && (opsF2K 248).eq (getN R 1) KernelLC.ThB.M) =
    true :=
  regsN_of_runS_init _ _ _ _ _ _ _ thRun (by quickRfl)

theorem thCz_K : regsN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M thThreeN thThreeProg
    (fun R => certN (opsF2K 248) R ⟨thThreeN, thThreeProg, thCzSpec.facts⟩ &&
      (opsF2K 248).eq (getN R 0) KernelLC.ThA.M && (opsF2K 248).eq (getN R 1) KernelLC.ThB.M) =
    true :=
  regsN_of_runS_init _ _ _ _ _ _ _ thRun (by quickRfl)

theorem thTz_neg : (!regsN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M 2 []
    (fun R => (opsF2K 248).eq (getN R 0) KernelLC.ThB.M)) = true := by
  quickRfl

end CertificateChecks.KernelMC

end
