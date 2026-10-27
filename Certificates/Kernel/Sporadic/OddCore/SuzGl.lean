module

public import Certificates.Kernel.Sporadic.OddCore.SuzGlG
public import Certificates.Kernel.Sporadic.OddCore.SuzGlH
public import Certificates.Kernel.Sporadic.OddCore.SuzGlC
public import Certificates.Kernel.Sporadic.OddCore.SuzGlAS
public import Certificates.Kernel.Sporadic.OddCore.SuzGlI0
public import Certificates.Kernel.Sporadic.OddCore.SuzGlI1
public import Certificates.Kernel.Sporadic.OddCore.SuzGlI2
public import Certificates.Kernel.Sporadic.OddCore.SuzGlI3
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.SuzGl.idxSlAll CertificateChecks.KernelSpor.SuzGl.idxSl 64
#kon_join CertificateChecks.KernelSpor.SuzGl.autSlAll CertificateChecks.KernelSpor.SuzGl.autSl 31

namespace CertificateChecks.KernelSpor.SuzGl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Sporadic.SuzRecog.B0Gluing CFSG.Sporadic.SuzRecog.B0GluingData
open CFSG.Sporadic.SuzRecog.C1Model CFSG.PSL3Four.Native CFSG.ComponentClassification.AS81.SuzB0
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzTwCF
  CertificateChecks.KernelSpor.SuzMGF CertificateChecks.KernelSpor.SuzC1BF
  CertificateChecks.KernelSpor.SuzC1EG CertificateChecks.KernelSpor.SuzC1EF
  CertificateChecks.KernelSpor.SuzC1EV CertificateChecks.KernelSpor.SuzC1EZ

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pgk" => pg 11 (mask 11)
local notation "T" => SuzC1ET.T
local notation "Id" => pidn 1782 11
local notation "g7" => pg 7 (mask 7)

@[expose] noncomputable def y0K (X m i : Nat) : Nat :=
  nIf(bAnd(Nat.blt X 2, bAnd(Nat.blt m 64, Nat.blt i 1782)),
    pgk (SuzGlY (Nat.add (Nat.mul 64 X) m)) i, 0)

theorem kT0 : Nat.beq (T 0) Id = true := by quickRfl

theorem kTG : allN 4 (fun i => Nat.beq (T (Nat.succ i)) (SuzC1ET.G i)) = true := by quickRfl

theorem kTT1 : Nat.beq (T 45) (SuzInvT1.F 0) = true := by quickRfl

theorem kTau1 : Nat.beq (fpT (pgk (pc (pc (SuzMGG 4) (T 53)) (SuzMGG 4)) 0)) 57 = true := by
  quickRfl

theorem kTau2 : Nat.beq (T 57) (pc (pc (SuzMGG 4) (T 53)) (SuzMGG 4)) = true := by quickRfl

theorem kTZ : Bool.not (Nat.beq (pc (SuzInvT1.F 0) (SuzC1BT 9)) (pc (SuzC1BT 9) (SuzInvT1.F 0))) =
    true := by quickRfl

theorem kCPL : Nat.beq cPairsK.length 496 = true := by quickRfl

theorem negNA : Bool.not (Nat.beq (fpT (pgk (pc (pc (SuzGlN 0) (T 1)) (SuzGlNI 0)) 0))
    (Nat.add (nAK 0 1) 1)) = true := by quickRfl

theorem idx_prod : (allBelow 64 fun a => allBelow 64 fun b =>
    decide (mulP a b < 64) && ttabs[mulP a b]! == comp 1782 ttabs[a]! ttabs[b]!) = true := by
  refine allBelow_of fun a ha => allBelow_of fun b hb => ?_
  have h : strictB (mulK a b) (fun m => bAnd(Nat.blt m 64, Nat.beq (T m) (pc (T a) (T b)))) =
      true := allN_spec (idxSlAll a ha) b hb
  rw [strictB_app'] at h
  obtain ⟨hm, he⟩ := (bAnd_iff _ _).1 h
  have hm' : mulK a b < 64 := Eq.mp Nat.blt_eq hm
  rw [mulP_eq, beqP (pTT hm') (pc' (pTT ha) (pTT hb)), he]
  simp [hm']

theorem tf_id : tFound (idTab 1782) = true := by
  unfold tFound
  rw [show tPos (idTab 1782) = 0 from oneI_eq, beqP (pTT (by norm_num)) pId', kT0]
  rfl

theorem tPos_gen {i : Nat} (hi : i < 4) : tPos t0Tabs[i]! = i + 1 := by
  have h := gP_eq i
  unfold gP gK at h
  rw [blt_t hi] at h
  exact h

theorem tf_gen {i : Nat} (hi : i < 4) : tFound t0Tabs[i]! = true := by
  unfold tFound
  rw [tPos_gen hi, beqP (pTT (by omega)) (pT0 hi), allN_spec kTG i hi]
  simp only [decide_eq_true (show i + 1 < 64 by omega), Bool.true_and]

theorem tf_t1 : tFound tTab = true := by
  unfold tFound
  rw [tPos_t1, beqP (pTT (by norm_num)) pt1, kTT1]
  rfl

theorem idxCheck_true : idxCheck = true := by
  have hg : (allBelow 4 fun i => tFound t0Tabs[i]!) = true := allBelow_of fun i hi => tf_gen hi
  unfold idxCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨idx_prod, tf_id⟩, ?_⟩, hg⟩, tf_t1⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩ <;>
  · simp only [mulP_eq, invP_eq, cmP_eq, oneI_eq, gP_eq, zI_eq, chi_eq, gam_eq, gamI_eq, lab_eq,
      par_eq, gammaGen_eq]
    quickRfl

theorem thetaCheck_true : thetaCheck = true := by
  unfold thetaCheck
  refine allBelow_of fun i hi => ?_
  have hθ := qTh hi
  have hθi := qThI hi
  have hk := (bAnd_iff _ _).1 (allN_spec kThT i hi)
  have hk2 := (bAnd_iff _ _).1 hk.2
  have hk3 := (bAnd_iff _ _).1 hk2.2
  have hk4 := (bAnd_iff _ _).1 hk3.2
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [hθi.1, CFSG.KS.PEnum.unpack_size]
    rfl
  · rw [beqQ (qc' hθi hθ) qId]
    exact hk4.2
  · refine allBelow_of fun k hk => ?_
    have h := allN_spec (allN_spec kTh i hi) k hk
    rw [strictB_app'] at h
    obtain ⟨hj, he⟩ := (bAnd_iff _ _).1 h
    have hj' : g7 (SuzGlP i) k < 64 := Eq.mp Nat.blt_eq hj
    have e : thK i k = g7 (SuzGlP i) k := by
      unfold thK
      rw [blt_t hi, blt_t hk]
    rw [th_eq, e]
    unfold conjTab
    have he' : Nat.beq (SuzGlR (g7 (SuzGlP i) k))
        (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (SuzGlT i) (SuzGlR k)) (SuzGlTI i)) = true := by
      rw [Nat.eq_of_beq_eq_true he]
      exact Nat.beq_refl _
    rw [beqQ (qR hj') (qc' (qc' hθ (qR hk)) hθi), he']
    simp [hj']
  · refine allBelow_of fun k hk => ?_
    rw [thI_eq, th_eq]
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec (allN_spec kThPQ i hi) k hk)
    rw [nat_beq, h2]
    simp [Eq.mp Nat.blt_eq h1]

theorem autCheck_true : autCheck = true := by
  rw [autCheck_eq, List.all_eq_true]
  intro p hp
  rw [List.all_eq_true]
  intro q hq
  rw [autBody_eq]
  rw [cPairs_eq] at hp hq
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
  have hj' : j < 496 := by
    rw [Nat.eq_of_beq_eq_true kCPL] at hj
    exact hj
  have hs : autSl (j / 16) = true := autSlAll (j / 16) (by change j / 16 < 31; omega)
  have h := allBlk_spec (len := 16) hs (j % 16) (by omega)
  rw [show Nat.add (Nat.mul 16 (j / 16)) (j % 16) = j by
    change 16 * (j / 16) + j % 16 = j
    omega, List.all_eq_true] at h
  have := h q hq
  rwa [List.getD_eq_getElem _ _ hj] at this

theorem y0_get (X m i : Nat) : ((y0Tabs[X]!)[m]!)[i]! = y0K X m i := by
  unfold y0K
  by_cases hX : X < 2
  · by_cases hm : m < 64
    · by_cases hi : i < 1782
      · rw [(pY hX hm).1, unpack_getElem! hi, blt_t hX, blt_t hm, blt_t hi]
        rfl
      · rw [(pY hX hm).1, getElem!_neg _ _ (by rw [CFSG.KS.PEnum.unpack_size]; exact hi),
          blt_t hX, blt_t hm, blt_f hi]
        rfl
    · rw [getElem!_neg (y0Tabs[X]!) m (by rw [y0_size hX]; exact hm), blt_t hX, blt_f hm]
      rfl
  · rw [getElem!_neg y0Tabs X (by simp [y0Tabs]; omega), blt_f hX]
    rfl

theorem radIdx_scatter (X : Nat) :
    radIdx X = scatter (fun i => (rads[X]!)[i]!) 64 16 (rads[X]!).size := by
  unfold radIdx scatter
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem radIdx_eq (X e : Nat) : (radIdxs[X]!)[e]! = radIdxK X e := by
  unfold radIdxK
  by_cases hX : X < 2
  · have e1 : radIdxs[X]! = radIdx X := by interval_cases X <;> rfl
    have hs : (rads[X]!).size = 16 := by
      rw [rads_get hX]
      exact Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec kRad X hX)).1
    rw [e1, radIdx_scatter, blt_t hX]
    by_cases he : e < 64
    · rw [(scatter_get _ _ _ _).2 e he, blt_t he, hs]
      exact fpL_congr fun j _ => by rw [rads_get hX]; rfl
    · rw [getElem!_neg _ _ (by rw [(scatter_get _ _ _ _).1]; exact he), blt_f he]
      rfl
  · rw [getElem!_neg radIdxs X (by simp [radIdxs]; omega), blt_f hX]
    rfl

theorem radOK_true {X : Nat} (hX : X < 2) : radOK X = true := by
  unfold radOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [rads_get hX, Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec kRad X hX)).1]
    rfl
  · interval_cases X <;> simp only [rads_eq, inRad, radIdx_eq] <;> quickRfl
  · rw [sizeP (pWI hX)]
    rfl
  · have h := (bAnd_iff _ _).1 (allN_spec kW X hX)
    have h2 := (bAnd_iff _ _).1 ((bAnd_iff _ _).1 h.2).2
    rw [beqP (pc' (pWI hX) (pW hX)) pId']
    exact h2.2
  · refine allBelow_of fun p hp => ?_
    obtain ⟨h1, h2⟩ := cA_conj hX hp
    rw [cA_eq, h2]
    simp [h1]
  · interval_cases X <;> simp only [rads_eq, inRad, radIdx_eq, oneI_eq] <;> quickRfl
  · interval_cases X <;> simp only [rads_eq, inRad, radIdx_eq, zI_eq] <;> quickRfl

theorem fix_part : (allBelow 1782 fun i => (w0T[i]! == i) == (r1T[i]! == i)) = true := by
  refine allBelow_of fun i hi => ?_
  have h := allN_spec kFixW i hi
  rw [pw0.1, pr1.1, unpack_getElem! hi, unpack_getElem! hi, nat_beq, nat_beq]
  revert h
  cases Nat.beq (pgk (SuzTwG 6) i) i <;> cases Nat.beq (pgk (SuzC1BT 11) i) i <;> decide

theorem nInv_part : (allBelow 4 fun l => (nInvs[l]!).size == 1782 &&
    comp 1782 nInvs[l]! nTabs[l]! == idTab 1782) = true := by
  refine allBelow_of fun l hl => ?_
  have h := kN
  simp only [Bool.and_eq_true] at h
  have h' := (bAnd_iff _ _).1 ((bAnd_iff _ _).1 (allN_spec h.2 l hl)).2
  rw [sizeP (pNI hl), beqP (pc' (pNI hl) (pN hl)) pId', h'.2]
  rfl

theorem planeCheck_true : planeCheck = true := by
  have h0 : radOK 0 = true := radOK_true (by norm_num)
  have h1 : radOK 1 = true := radOK_true (by norm_num)
  unfold planeCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨fix_part, nInv_part⟩, h0⟩, h1⟩, ?_⟩
  simp only [y0_get, hAct, jAct, jE, letterOK, inRad, CFSG.Sporadic.SuzRecog.B0Gluing.pT1,
    CFSG.Sporadic.SuzRecog.B0Gluing.pR0, nA_eq, cA_eq, gam_eq, gamI_eq, radIdx_eq, rads_eq, zI_eq,
    oneI_eq]
  quickRfl

theorem tauZCheck_true : tauZCheck = true := by
  have e2 : zIL[2]! = 53 := rfl
  have e3 : zIL[3]! = 57 := rfl
  have py : P (conjTab 1782 tauT tauT ttabs[53]!) (pc (pc (SuzMGG 4) (T 53)) (SuzMGG 4)) := by
    unfold conjTab
    exact pc' (pc' ptau (pTT (by norm_num))) ptau
  have h1 := kTau1
  have h2 := kTau2
  have hz : Nat.beq (pc (SuzInvT1.F 0) (SuzC1BT 9)) (pc (SuzC1BT 9) (SuzInvT1.F 0)) = false := by
    have := kTZ
    revert this
    cases Nat.beq (pc (SuzInvT1.F 0) (SuzC1BT 9)) (pc (SuzC1BT 9) (SuzInvT1.F 0)) <;> decide
  have ht : tPos (conjTab 1782 tauT tauT ttabs[53]!) = 57 := by
    rw [tPos_P py, Nat.eq_of_beq_eq_true h1]
  have hb : (ttabs[57]! == conjTab 1782 tauT tauT ttabs[53]!) = true := by
    rw [beqP (pTT (by norm_num)) py, h2]
  have hc : (comp 1782 tTab CFSG.Sporadic.SuzRecog.C1Model.zT ==
      comp 1782 CFSG.Sporadic.SuzRecog.C1Model.zT tTab) = false := by
    rw [beqP (pc' pt1 pz) (pc' pz pt1), hz]
  have hA : tFound (conjTab 1782 tauT tauT ttabs[zI[2]!]!) = true := by
    rw [zI_eq, e2]
    unfold tFound
    rw [ht, hb]
    rfl
  have hB : (tPos (conjTab 1782 tauT tauT ttabs[zI[2]!]!) == zI[3]!) = true := by
    rw [zI_eq, e2, e3, ht]
    rfl
  have hC : (!(comp 1782 tTab CFSG.Sporadic.SuzRecog.C1Model.zT ==
      comp 1782 CFSG.Sporadic.SuzRecog.C1Model.zT tTab)) = true := by
    rw [hc]
    rfl
  unfold tauZCheck
  simp only [hA, hB, hC]
  rfl

theorem rhoACheck_true : rhoACheck = true := by
  unfold rhoACheck
  dsimp only
  rw [Array.all_eq_true]
  intro i hi
  have hs : ct0Tabs.size = 192 := by
    unfold ct0Tabs
    rw [ct0E.1]
    simp [penumRec, SuzC1EZ.kCnt.1]
  have hi' : i < 192 := hs ▸ hi
  have hc : P ct0Tabs[i] (SuzC1EQ.T i) := by
    rw [← getElem!_pos ct0Tabs i hi]
    exact pQT hi'
  rw [rhoBody_eq hc]
  exact rhoK_of hi'

end CertificateChecks.KernelSpor.SuzGl

end
