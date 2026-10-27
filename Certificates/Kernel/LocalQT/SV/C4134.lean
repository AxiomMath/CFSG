module

public import Certificates.Kernel.LocalQT.SV.C4134H
public import Certificates.Kernel.LocalQT.SV.C4134N0
public import Certificates.Kernel.LocalQT.SV.C4134N1
public import Certificates.Kernel.LocalQT.SV.C4134NR
public import Certificates.Kernel.LocalQT.SV.C4134Y0
public import Certificates.Kernel.LocalQT.SV.C4134Y1
public import Certificates.Kernel.LocalQT.SV.C4134Y2
public import Certificates.Kernel.LocalQT.SV.C4134Y3
public import Certificates.Kernel.LocalQT.SV.C4134Y4
public import Certificates.Kernel.LocalQT.SV.C4134Y5
public import Certificates.Kernel.LocalQT.SV.C4134Y6
public import Certificates.Kernel.LocalQT.SV.C4134Y7
public import Certificates.Kernel.LocalQT.SV.C4134Y8
public import Certificates.Kernel.LocalComp.HeFixBind
public import CFSG.Certificates.Kernel.LocalQTSlpPSound
public import CFSG.Certificates.Kernel.LocalQTSylVSound
public import CFSG.Certificates.Kernel.LocalQTNatsXSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeCheckInputs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Sporadic.HeldB.InnerCheck

public section

set_option maxRecDepth 400000

#kqb_all CFSG.KD.LQT.C4134.NT0 CFSG.KD.LQT.C4134.ckT0 25
#kqb_all CFSG.KD.LQT.C4134.NT1 CFSG.KD.LQT.C4134.ckT1 23
#kqb_all CFSG.KD.LQT.C4134.NTU CFSG.KD.LQT.C4134.ckTU 24
#kqb_all CFSG.KD.LQT.C4134.NRS CFSG.KD.LQT.C4134.ckRS 26
#kqb_all CFSG.KD.LQT.C4134.Y CFSG.KD.LQT.C4134.ckSY 512

namespace CFSG.KD.LQT.C4134

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.SP
  CFSG.KC.LQT.SV CFSG.KC.LQT.NP CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.HeldB
  CertificateChecks.KernelLC.HeFix

theorem a0p : heA0P = (unpack 8330 14 (HG.F 0), unpack 8330 14 G0I) := by
  have h := allN_spec kPL2 0 (by decide)
  simp only [L2_0, L2I, List.getD_cons_zero] at h
  unfold heA0P
  rw [heGen_eq (k := 0) (by decide), (invEqK_sound h).1]

theorem a1p : heA1P = (unpack 8330 14 (HG.F 1), unpack 8330 14 G1I) := by
  have h := allN_spec kPL2 1 (by decide)
  simp only [L2_1, L2I, List.getD_cons_succ, List.getD_cons_zero] at h
  unfold heA1P
  rw [heGen_eq (k := 1) (by decide), (invEqK_sound h).1]

theorem gens_eq : [heA0P, heA1P] = unpackP 8330 14 [HG.F 0, HG.F 1] [G0I, G1I] := by
  rw [a0p, a1p]
  rfl

theorem gensR_eq : [heA0P, heA1P, heUP] = unpackP 8330 14 [HG.F 0, HG.F 1, PU] [G0I, G1I, PU] := by
  rw [a0p, a1p]
  unfold heUP
  rw [heU_eq]
  rfl

theorem targ_eq : [heGen 0, heGen 1] = [HG.F 0, HG.F 1].map (unpack 8330 14) := by
  rw [heGen_eq (k := 0) (by decide), heGen_eq (k := 1) (by decide)]
  rfl

theorem c0 : threeConjCheck 8330 [heA0P, heA1P] heT0P heT0Words heT0Prog [heGen 0, heGen 1] =
    true := by
  have e : heT0P = (unpack 8330 14 (HG.F 0), unpack 8330 14 (HG.F 0)) := by
    unfold heT0P
    rw [heGen_eq (k := 0) (by decide)]
  rw [gens_eq, e, targ_eq]
  exact threeConj_of_SP (gi := 3) (K := 25) (L := 8) (D := D0) rfl rfl hT0
    (Nat.le_of_ble_eq_true kT0) NT0.all tT0

theorem c1 : threeConjCheck 8330 [heA0P, heA1P] heT1ArrP heT1Words heT1Prog [heGen 0, heGen 1] =
    true := by
  have e : heT1ArrP = (unpack 8330 14 PT1, unpack 8330 14 PT1) := by
    unfold heT1ArrP
    rw [heT1_eq]
  rw [gens_eq, e, targ_eq]
  exact threeConj_of_SP (gi := 3) (K := 23) (L := 8) (D := D1) rfl rfl hT1
    (Nat.le_of_ble_eq_true kT1) NT1.all tT1

theorem cU : threeConjCheck 8330 [heA0P, heA1P] heUP heUWords heUProg [heGen 0, heGen 1] =
    true := by
  have e : heUP = (unpack 8330 14 PU, unpack 8330 14 PU) := by
    unfold heUP
    rw [heU_eq]
  rw [gens_eq, e, targ_eq]
  exact threeConj_of_SP (gi := 3) (K := 24) (L := 8) (D := DU) rfl rfl hTU
    (Nat.le_of_ble_eq_true kTU) NTU.all tTU

theorem sylG : heSylGens.map Prod.fst = SY.G.map (unpack 8330 14) := by
  have h := runSP_sound (gi := 3) (K := 26) (L := 8) (D := DR) rfl rfl hR
    (Nat.le_of_ble_eq_true kRS) NRS.all hSel
  rw [← gensR_eq] at h
  exact h

theorem syl : sylVerify 8330 2048 heSylGens (parseNats heSylParStr) (parseNats heSylLabStr)
    (parseNats heSylTabStr) (sylBuild 8330 2048 heSylGens (parseNats heSylParStr)
      (parseNats heSylLabStr)) 6 = true := by
  have eP : parseNats heSylParStr = SY.ParL := by
    rw [CP.eq]
    exact natsX_sound _ _ pP
  have eL : parseNats heSylLabStr = SY.LabL := by
    rw [CL.eq]
    exact natsX_sound _ _ pL
  have eT : parseNats heSylTabStr = SY.TabL := by
    rw [CT.eq]
    exact natsX_sound _ _ pT
  rw [eP, eL, eT]
  exact (sylSV_sound (K := 512) (L := 4) (P := [0]) sylG hSY (bindSV_spec bP) (bindSV_spec bL)
    (bindSV_spec bT) (by norm_num) Y.all sSY qSY (by decide)).1

theorem facts :
    (threeConjCheck 8330 [heA0P, heA1P] heT0P heT0Words heT0Prog [heGen 0, heGen 1] = true)
    ∧ (threeConjCheck 8330 [heA0P, heA1P] heT1ArrP heT1Words heT1Prog [heGen 0, heGen 1] = true)
    ∧ (threeConjCheck 8330 [heA0P, heA1P] heUP heUWords heUProg [heGen 0, heGen 1] = true)
    ∧ (sylVerify 8330 2048 heSylGens (parseNats heSylParStr) (parseNats heSylLabStr)
            (parseNats heSylTabStr) (sylBuild 8330 2048 heSylGens (parseNats heSylParStr)
              (parseNats heSylLabStr)) 6 = true) :=
  ⟨c0, c1, cU, syl⟩

end CFSG.KD.LQT.C4134

end
