module

public import Certificates.Kernel.SporSch.HN.PtR
public import Certificates.Kernel.SporSch.HN.Pt2109Data
public import Certificates.Data.Kernel.SporSch.HNXPtL
public import CFSG.Certificates.Kernel.Local.HN.X.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt2109

open CFSG.KC.LL.HNX CFSG.KD.HNPt2109 CFSG.KD.LgHNX

local notation "R" => CFSG.KD.HNPt.R
local notation "mm" => CFSG.KC.LL.HN.mm

theorem w_S : wordC R s0c = S0 ∧ wordC R s1c = S1 ∧ wordC R s2c = S2 ∧ wordC R s3c = S3 := by
  decide +kernel
theorem w_C1 : wordC R c1c0 = C1_0 ∧ wordC R c1c1 = C1_1 ∧ wordC R c1c2 = C1_2 ∧
    wordC R c1c3 = C1_3 ∧ wordC R c1c4 = C1_4 ∧ wordC R c1c5 = C1_5 ∧ wordC R c1c6 = C1_6 ∧
    wordC R c1c7 = C1_7 := by decide +kernel
theorem w_C3 : wordC R c3c0 = C3_0 ∧ wordC R c3c1 = C3_1 ∧ wordC R c3c2 = C3_2 ∧
    wordC R c3c3 = C3_3 ∧ wordC R c3c4 = C3_4 ∧ wordC R c3c5 = C3_5 ∧ wordC R c3c6 = C3_6 := by
  decide +kernel

theorem t_S : trM S0 = TS0 ∧ trM S1 = TS1 ∧ trM S2 = TS2 ∧ trM S3 = TS3 := by decide +kernel
theorem g_S : trM (CFSG.KC.LL.HN.subI S0) = GS0 ∧ trM (CFSG.KC.LL.HN.subI S1) = GS1 ∧
    trM (CFSG.KC.LL.HN.subI S2) = GS2 ∧ trM (CFSG.KC.LL.HN.subI S3) = GS3 := by decide +kernel
theorem t_C1 : trM C1_0 = TC1_0 ∧ trM C1_1 = TC1_1 ∧ trM C1_2 = TC1_2 ∧ trM C1_3 = TC1_3 ∧
    trM C1_4 = TC1_4 ∧ trM C1_5 = TC1_5 ∧ trM C1_6 = TC1_6 ∧ trM C1_7 = TC1_7 := by decide +kernel
theorem t_C3 : trM C3_0 = TC3_0 ∧ trM C3_1 = TC3_1 ∧ trM C3_2 = TC3_2 ∧ trM C3_3 = TC3_3 ∧
    trM C3_4 = TC3_4 ∧ trM C3_5 = TC3_5 ∧ trM C3_6 = TC3_6 := by decide +kernel

theorem cm_C1 : mm C1_0 S0 = mm S0 C1_0 ∧ mm C1_1 S0 = mm S0 C1_1 ∧ mm C1_2 S0 = mm S0 C1_2 ∧
    mm C1_3 S0 = mm S0 C1_3 ∧ mm C1_4 S0 = mm S0 C1_4 ∧ mm C1_5 S0 = mm S0 C1_5 ∧
    mm C1_6 S0 = mm S0 C1_6 ∧ mm C1_7 S0 = mm S0 C1_7 := by decide +kernel
theorem cm_C3 : mm C3_0 S2 = mm S2 C3_0 ∧ mm C3_1 S2 = mm S2 C3_1 ∧ mm C3_2 S2 = mm S2 C3_2 ∧
    mm C3_3 S2 = mm S2 C3_3 ∧ mm C3_4 S2 = mm S2 C3_4 ∧ mm C3_5 S2 = mm S2 C3_5 ∧
    mm C3_6 S2 = mm S2 C3_6 := by decide +kernel

theorem fx_0 : ptsFn TX MS CM3 M TS0 (lget FX0) (lget FX0) 645 = true := by quickRfl
theorem fx_1 : ptsFn TX MS CM3 M TS1 (lget FX1) (lget FX1) 645 = true := by quickRfl
theorem fx_2 : ptsFn TX MS CM3 M TS2 (lget FX2) (lget FX2) 60 = true := by quickRfl
theorem fx_3 : ptsFn TX MS CM3 M TS3 (lget FX3) (lget FX3) 645 = true := by quickRfl

@[expose] noncomputable def treeImg (G : Nat) (P J : List Nat) : Bool :=
  ptsFn TX MS CM3 M G (lget P) (fun t => lget P (lget J t)) (List.length P)

theorem tr_1 : treeImg TC1_0 P1 J1_0 = true ∧ treeImg TC1_1 P1 J1_1 = true ∧
    treeImg TC1_2 P1 J1_2 = true ∧ treeImg TC1_3 P1 J1_3 = true ∧ treeImg TC1_4 P1 J1_4 = true ∧
    treeImg TC1_5 P1 J1_5 = true ∧ treeImg TC1_6 P1 J1_6 = true ∧ treeImg TC1_7 P1 J1_7 = true := by
  decide +kernel
theorem tr_2 : treeImg TC1_0 P2 J2_0 = true ∧ treeImg TC1_1 P2 J2_1 = true ∧
    treeImg TC1_2 P2 J2_2 = true ∧ treeImg TC1_3 P2 J2_3 = true ∧ treeImg TC1_4 P2 J2_4 = true ∧
    treeImg TC1_5 P2 J2_5 = true ∧ treeImg TC1_6 P2 J2_6 = true ∧ treeImg TC1_7 P2 J2_7 = true := by
  decide +kernel
theorem tr_0 : treeImg TC1_0 P0 J0_0 = true ∧ treeImg TC1_1 P0 J0_1 = true ∧
    treeImg TC1_2 P0 J0_2 = true ∧ treeImg TC1_3 P0 J0_3 = true ∧ treeImg TC1_4 P0 J0_4 = true ∧
    treeImg TC1_5 P0 J0_5 = true ∧ treeImg TC1_6 P0 J0_6 = true ∧ treeImg TC1_7 P0 J0_7 = true := by
  decide +kernel
theorem tr_3 : treeImg TC3_0 P3 J3_0 = true ∧ treeImg TC3_1 P3 J3_1 = true ∧
    treeImg TC3_2 P3 J3_2 = true ∧ treeImg TC3_3 P3 J3_3 = true ∧ treeImg TC3_4 P3 J3_4 = true ∧
    treeImg TC3_5 P3 J3_5 = true ∧ treeImg TC3_6 P3 J3_6 = true := by
  decide +kernel

theorem neg_fx : Bool.not (ptsFn TX MS CM3 M TS1 (lget FX0) (lget FX0) 645) = true := by quickRfl
theorem neg_tr : Bool.not (treeImg TC1_1 P1 J1_0) = true := by quickRfl
theorem neg_cm : Bool.not (Nat.beq (mm C1_2 S1) (mm S1 C1_2)) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNPt2109

end
