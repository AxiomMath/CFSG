module

public import Certificates.Kernel.LocalQT.SV.C4126H
public import Certificates.Kernel.LocalQT.SV.C4126N
public import Certificates.Kernel.LocalQT.SV.C4126Y0
public import Certificates.Kernel.LocalQT.SV.C4126Y1
public import Certificates.Kernel.LocalQT.SV.C4126Y2
public import Certificates.Kernel.LocalQT.SV.C4126Y3
public import Certificates.Kernel.LocalQT.SV.C4126TB
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.LocalQTSlpPSound
public import CFSG.Certificates.Kernel.LocalQTSylVSound
public import CFSG.Certificates.Kernel.LocalQTNatsXSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSCheckInputs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

set_option maxRecDepth 400000

#kqb_all CFSG.KD.LQT.C4126.NT0 CFSG.KD.LQT.C4126.ckT0 3
#kqb_all CFSG.KD.LQT.C4126.NT1 CFSG.KD.LQT.C4126.ckT1 4
#kqb_all CFSG.KD.LQT.C4126.NT2 CFSG.KD.LQT.C4126.ckT2 5
#kqb_all CFSG.KD.LQT.C4126.NT3 CFSG.KD.LQT.C4126.ckT3 4
#kqb_all CFSG.KD.LQT.C4126.Y CFSG.KD.LQT.C4126.ckSY 128

namespace CFSG.KD.LQT.C4126

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.SP
  CFSG.KC.LQT.SV CFSG.KC.LQT.NP CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Bridge.HSExcl CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native

theorem a_eq {j : Nat} (hj : j < 2) :
    hsStrongArrs[j]! = unpack 3850 12 (HS.F j) ∧
      invCand 3850 (unpack 3850 12 (HS.F j)) = unpack 3850 12 (HSI j) ∧
      isInvA 3850 (unpack 3850 12 (HS.F j)) (unpack 3850 12 (HSI j)) = true :=
  ⟨hsStrong_get hj, invEqK_sound (allN_spec hs_perms j hj)⟩

theorem gens_eq : [hsA0P, hsA1P] = unpackP 3850 12 [HS.F 0, HS.F 1] [HSI 0, HSI 1] := by
  unfold hsA0P hsA1P hsA0A hsA1A
  rw [(a_eq (j := 0) (by norm_num)).1, (a_eq (j := 1) (by norm_num)).1,
    (a_eq (j := 0) (by norm_num)).2.1, (a_eq (j := 1) (by norm_num)).2.1]
  rfl

theorem targ_eq : [hsA0A, hsA1A] = [HS.F 0, HS.F 1].map (unpack 3850 12) := by
  unfold hsA0A hsA1A
  rw [(a_eq (j := 0) (by norm_num)).1, (a_eq (j := 1) (by norm_num)).1]
  rfl

theorem tp_eq {k : Nat} (hk : k < 43) :
    hsTP k = (unpack 3850 12 (HC.F k), unpack 3850 12 (HC.F k)) := by
  unfold hsTP hsTA
  rw [hsCentTbl_eq hk]

theorem c0 : threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 5) hsT0Words hsT0Prog [hsA0A, hsA1A] =
    true := by
  rw [gens_eq, tp_eq (k := 5) (by norm_num), targ_eq]
  exact threeConj_of_SP (gi := 3) (K := 3) (L := 16) (D := D0) rfl rfl hT0
    (Nat.le_of_ble_eq_true kT0) NT0.all tT0

theorem c1 : threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 12) hsT1Words hsT1Prog [hsA0A, hsA1A] =
    true := by
  rw [gens_eq, tp_eq (k := 12) (by norm_num), targ_eq]
  exact threeConj_of_SP (gi := 3) (K := 4) (L := 16) (D := D1) rfl rfl hT1
    (Nat.le_of_ble_eq_true kT1) NT1.all tT1

theorem c2 : threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 21) hsT2Words hsT2Prog [hsA0A, hsA1A] =
    true := by
  rw [gens_eq, tp_eq (k := 21) (by norm_num), targ_eq]
  exact threeConj_of_SP (gi := 3) (K := 5) (L := 16) (D := D2) rfl rfl hT2
    (Nat.le_of_ble_eq_true kT2) NT2.all tT2

theorem c3 : threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 34) hsT3Words hsT3Prog [hsA0A, hsA1A] =
    true := by
  rw [gens_eq, tp_eq (k := 34) (by norm_num), targ_eq]
  exact threeConj_of_SP (gi := 3) (K := 4) (L := 16) (D := D3) rfl rfl hT3
    (Nat.le_of_ble_eq_true kT3) NT3.all tT3

theorem perm : isInvA 3850 hsA0A (invCand 3850 hsA0A) = true ∧
    isInvA 3850 hsA1A (invCand 3850 hsA1A) = true ∧
    ∀ k ∈ [1, 2, 3, 4, 5, 12, 21, 34], permOK 3850 (hsCentTbl k) = true := by
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · unfold hsA0A
    rw [(a_eq (j := 0) (by norm_num)).1, (a_eq (j := 0) (by norm_num)).2.1]
    exact (a_eq (j := 0) (by norm_num)).2.2
  · unfold hsA1A
    rw [(a_eq (j := 1) (by norm_num)).1, (a_eq (j := 1) (by norm_num)).2.1]
    exact (a_eq (j := 1) (by norm_num)).2.2
  · have hk' : k < 43 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with h | h | h | h | h | h | h | h <;> omega
    obtain ⟨h1, h2⟩ := invEqK_sound (allN_spec hc_perms k hk')
    unfold CFSG.Sporadic.SmallOddCore.permOK
    rw [hsCentTbl_eq hk', h1]
    exact h2

theorem sylG : hsSylGens.map Prod.fst = SY.G.map (unpack 3850 12) := by
  rw [gG]
  simp only [hsSylGens, hsSP, hsTA, List.map_cons, List.map_nil]
  rw [hsCentTbl_eq (k := 1) (by norm_num), hsCentTbl_eq (k := 2) (by norm_num),
    hsCentTbl_eq (k := 3) (by norm_num), hsCentTbl_eq (k := 4) (by norm_num)]

theorem syl : sylVerify 3850 1024 hsSylGens (parseNats hsSylParStr) (parseNats hsSylLabStr)
    (parseNats hsSylTabStr) (sylBuild 3850 1024 hsSylGens (parseNats hsSylParStr)
      (parseNats hsSylLabStr)) 6 = true := by
  have eP : parseNats hsSylParStr = SY.ParL := by
    rw [CP.eq]
    exact natsX_sound _ _ pP
  have eL : parseNats hsSylLabStr = SY.LabL := by
    rw [CL.eq]
    exact natsX_sound _ _ pL
  have eT : parseNats hsSylTabStr = SY.TabL := by
    rw [CT.eq]
    exact natsX_sound _ _ pT
  rw [eP, eL, eT]
  exact (sylSV_sound (K := 128) (L := 8) (P := [0]) sylG hSY (bindSV_spec bP) (bindSV_spec bL)
    (bindSV_spec bT) (by norm_num) Y.all sSY qSY (by decide)).1

theorem facts :
    (threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 5) hsT0Words hsT0Prog [hsA0A, hsA1A] = true)
    ∧ (threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 12) hsT1Words hsT1Prog [hsA0A, hsA1A] = true)
    ∧ (threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 21) hsT2Words hsT2Prog [hsA0A, hsA1A] = true)
    ∧ (threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 34) hsT3Words hsT3Prog [hsA0A, hsA1A] = true)
    ∧ (isInvA 3850 hsA0A (invCand 3850 hsA0A) = true ∧
            isInvA 3850 hsA1A (invCand 3850 hsA1A) = true ∧
            ∀ k ∈ [1, 2, 3, 4, 5, 12, 21, 34], permOK 3850 (hsCentTbl k) = true)
    ∧ (sylVerify 3850 1024 hsSylGens (parseNats hsSylParStr) (parseNats hsSylLabStr)
            (parseNats hsSylTabStr) (sylBuild 3850 1024 hsSylGens (parseNats hsSylParStr)
              (parseNats hsSylLabStr)) 6 = true) :=
  ⟨c0, c1, c2, c3, perm, syl⟩

end CFSG.KD.LQT.C4126

end
