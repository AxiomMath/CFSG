module

public import Certificates.Kernel.LocalQT.SV.C4127K
public import CFSG.Certificates.Kernel.LocalQTSylVSound
public import CFSG.Certificates.Kernel.LocalQTNatsXSound
public import CFSG.Certificates.Kernel.LocalQTJ2IdxSound
public import CFSG.Certificates.Kernel.LocalQTJ2FrobSound

public section

namespace CFSG.KD.LQT.C4127

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.SV CFSG.KC.LQT.JX
  CFSG.KC.LQT.NP CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.J2Excl
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Monster.B.Co2.Native
  CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2PC

theorem a_eq {j : Nat} (hj : j < 7) :
    (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ())[j]! = unpack 315 9 (J2P.S j) ∧
      invCand 315 (unpack 315 9 (J2P.S j)) = unpack 315 9 (J2P.SI j) ∧
      isInvA 315 (unpack 315 9 (J2P.S j)) (unpack 315 9 (J2P.SI j)) = true :=
  ⟨bindsP.2.2.2.2.1 j hj, invEqK_sound (allN_spec permP j hj)⟩

theorem gens_eq : [j2A0P, j2A1P] = unpackP 315 9 [J2P.S 0, J2P.S 1] [J2P.SI 0, J2P.SI 1] := by
  unfold j2A0P j2A1P j2A0A j2A1A
  rw [(a_eq (j := 0) (by norm_num)).1, (a_eq (j := 1) (by norm_num)).1,
    (a_eq (j := 0) (by norm_num)).2.1, (a_eq (j := 1) (by norm_num)).2.1]
  rfl

theorem targ_eq : [j2A0A, j2A1A] = [J2P.S 0, J2P.S 1].map (unpack 315 9) := by
  unfold j2A0A j2A1A
  rw [(a_eq (j := 0) (by norm_num)).1, (a_eq (j := 1) (by norm_num)).1]
  rfl

theorem tp_eq {k : Nat} (hk : k < 42) :
    j2TP k = (unpack 315 9 (J2CentT.F k), unpack 315 9 (J2CentT.F k)) := by
  unfold j2TP j2TA
  rw [OddCore.j2CentTbl_eq hk]

theorem perm : isInvA 315 j2A0A (invCand 315 j2A0A) = true ∧
    isInvA 315 j2A1A (invCand 315 j2A1A) = true ∧
    ∀ k ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 17, 31], permOK 315 (j2CentTbl k) = true := by
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · unfold j2A0A
    rw [(a_eq (j := 0) (by norm_num)).1, (a_eq (j := 0) (by norm_num)).2.1]
    exact (a_eq (j := 0) (by norm_num)).2.2
  · unfold j2A1A
    rw [(a_eq (j := 1) (by norm_num)).1, (a_eq (j := 1) (by norm_num)).2.1]
    exact (a_eq (j := 1) (by norm_num)).2.2
  · have h := List.all_eq_true.1 OddCore.j2_permOK_all k
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    exact h (List.mem_range.2 (by rcases hk with h | h | h | h | h | h | h | h | h | h | h <;> omega))

theorem row0 : threeConjCheck 315 [j2A0P, j2A1P] (j2TP 9) j2Row0Words j2Row0Prog
    [j2A0A, j2A1A] = true := by
  rw [gens_eq, tp_eq (k := 9) (by norm_num), targ_eq]
  exact threeConj_of_mcP tc0

theorem row1 : threeConjCheck 315 [j2A0P, j2A1P] (j2TP 17) j2Row1Words j2Row1Prog
    [j2A0A, j2A1A] = true := by
  rw [gens_eq, tp_eq (k := 17) (by norm_num), targ_eq]
  exact threeConj_of_mcP tc1

theorem row2 : threeConjCheck 315 [j2A0P, j2A1P] (j2TP 31) j2Row2Words j2Row2Prog
    [j2A0A, j2A1A] = true := by
  rw [gens_eq, tp_eq (k := 31) (by norm_num), targ_eq]
  exact threeConj_of_mcP tc2

theorem eP : j2Par = SY.ParL := by
  unfold j2Par
  rw [CP.eq]
  exact natsX_sound _ _ pP

theorem eL : j2Lab = SY.LabL := by
  unfold j2Lab
  rw [CL.eq]
  exact natsX_sound _ _ pL

theorem eT : j2Tab = SY.TabL := by
  unfold j2Tab
  rw [CT.eq]
  exact natsX_sound _ _ pT

theorem sylG : j2SylGens.map Prod.fst = SY.G.map (unpack 315 9) := by
  rw [gG]
  simp only [j2SylGens, j2SP, j2TA, List.map_cons, List.map_nil]
  rw [OddCore.j2CentTbl_eq (k := 1) (by norm_num), OddCore.j2CentTbl_eq (k := 2) (by norm_num),
    OddCore.j2CentTbl_eq (k := 3) (by norm_num), OddCore.j2CentTbl_eq (k := 4) (by norm_num),
    OddCore.j2CentTbl_eq (k := 5) (by norm_num), OddCore.j2CentTbl_eq (k := 6) (by norm_num),
    OddCore.j2CentTbl_eq (k := 7) (by norm_num), OddCore.j2CentTbl_eq (k := 8) (by norm_num)]

theorem sylAll : sylVerify 315 256 j2SylGens j2Par j2Lab j2Tab j2Al 4 = true ∧
    ∀ k < 256, j2Al[k]! = unpack 315 9 (SY.E k) := by
  unfold j2Al
  rw [eP, eL, eT]
  exact sylSV_sound (K := 8) (L := 32) (P := [0, 1]) sylG hSY (bindSV_spec bP) (bindSV_spec bL)
    (bindSV_spec bT) (by norm_num) Y.all sSY qSY (by decide)

theorem idx : j2MulOK = true ∧ j2InvOK = true ∧ j2RepsOK = true ∧ j2TripleOK = true := by
  have h := idxJX_sound (b := 8) (gb := 12) (K := 8) (L := 32) (tab := j2Tab) (par := j2Par)
    (lab := j2Lab) (reps := j2Reps) (fun i hi => by rw [eP]; exact bindSV_spec bP i hi)
    (fun i hi => by rw [eL]; exact bindSV_spec bL i hi)
    (fun i hi => by rw [eT]; exact bindSV_spec bT i hi) (by norm_num) R.all rX T.all
  exact h

theorem pairs : j2PairCertsOK = true := by
  have hAl := sylAll.2
  unfold j2PairCertsOK
  rw [List.all_eq_true]
  intro e he
  obtain ⟨hl, ha, hb, hm⟩ := pcK_spec pc e he
  rw [hAl e.1 ha, hAl e.2.1 hb, gens_eq, targ_eq, hl]
  simp only [beq_self_eq_true, Bool.true_and]
  exact mcP_sound hm

theorem frob : j2FrobOK = true := by
  have h := frobK_sound fr
  rw [← gens_eq] at h
  exact h

theorem facts : (isInvA 315 j2A0A (invCand 315 j2A0A) = true ∧
      isInvA 315 j2A1A (invCand 315 j2A1A) = true ∧
      ∀ k ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 17, 31], permOK 315 (j2CentTbl k) = true)
    ∧ (threeConjCheck 315 [j2A0P, j2A1P] (j2TP 9) j2Row0Words j2Row0Prog [j2A0A, j2A1A] = true)
    ∧ (threeConjCheck 315 [j2A0P, j2A1P] (j2TP 17) j2Row1Words j2Row1Prog [j2A0A, j2A1A] = true)
    ∧ (threeConjCheck 315 [j2A0P, j2A1P] (j2TP 31) j2Row2Words j2Row2Prog [j2A0A, j2A1A] = true)
    ∧ (sylVerify 315 256 j2SylGens j2Par j2Lab j2Tab j2Al 4 = true)
    ∧ (j2MulOK = true ∧ j2InvOK = true ∧ j2RepsOK = true ∧ j2TripleOK = true)
    ∧ (j2PairCertsOK = true)
    ∧ (j2FrobOK = true) :=
  ⟨perm, row0, row1, row2, sylAll.1, idx, pairs, frob⟩

end CFSG.KD.LQT.C4127

end
