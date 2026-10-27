module

public import Certificates.Kernel.KGC31HS.Glue
public import Certificates.Kernel.KGC31HS.Inv0
public import Certificates.Kernel.KGC31HS.Inv1
public import Certificates.Kernel.KGC31HS.Inv2
public import Certificates.Kernel.KGC31HS.Inv3
public import Certificates.Kernel.KGC31HS.Cnt
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Quasithin.Vol2.KGFactC31HSData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31HS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.HS
open CFSG.KS.SporSch.MOC CFSG.Monster.B.Mathieu CFSG.Certificates CertificateChecks.KernelHS100

#kc_forall_chunks invAll (fun k => invBlk k = true) 22 CertificateChecks.KernelKGC31HS.invBlk 1

theorem invOK_all : ∀ j < RH.N, invOne j = true := of_blocks fun k hk => invAll k hk

theorem inv_facts {j : Nat} (hj : j < RH.N) :
    PP 100 7 (RH.E j) ∧ porbOne 100 7 5 (FV.F 2) C5 (RH.E j) = true ∧
      pactOne 100 7 5 (FV.F 4) (RH.E j) = true ∧ pactOne 100 7 5 (FV.F 25) (RH.E j) = true ∧
      porbOne 100 7 7 X7 C7 (RH.E j) = true ∧ pactOne 100 7 11 X11 (RH.E j) = true := by
  have h := invOK_all j hj
  simp only [invOne, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨PP_of_permOK hsz h1, h2, h3, h4, h5, h6⟩

theorem hi0 : 0 < RH.CS.length := by rw [kCS]; decide
theorem hi1 : 1 < RH.CS.length := by rw [kCS]; decide

set_option maxHeartbeats 2000000 in
theorem treeA : conjTreeOK 100 genArr genInvArr b0T clA.1 clA.2.1 clA.2.2 = true := by
  rw [clA_eq]
  dsimp only
  rw [b0T_eq]
  exact tree_rec hi0

set_option maxHeartbeats 2000000 in
theorem treeB : conjTreeOK 100 genArr genInvArr rBT clB.1 clB.2.1 clB.2.2 = true := by
  rw [clB_eq]
  dsimp only
  rw [rBT_eq]
  exact tree_rec hi1

theorem keys_of {i : Nat} (hi : i < RH.CS.length) :
    keysDistinct 100 (Array.ofFn (n := lget RH.CS i)
      fun k => tabP 100 7 (RH.E (lget RH.OFF i + k.val))).toList = true := by
  apply CFSG.KS.SporSch.ClsSpec.keysDistinct_of
  rw [Array.toList_ofFn, List.map_ofFn, List.nodup_ofFn]
  intro a b e
  exact Fin.ext ((replayH hi).inj a a.2 b b.2 e)

theorem keysA : keysDistinct 100 clA.1.toList = true := by rw [clA_eq]; exact keys_of hi0
theorem keysB : keysDistinct 100 clB.1.toList = true := by rw [clB_eq]; exact keys_of hi1

theorem sizeA : clA.1.size = 5775 := by simp only [clA_eq, Array.size_ofFn, lget_CS0]
theorem sizeB : clB.1.size = 15400 := by simp only [clB_eq, Array.size_ofFn, lget_CS1]

theorem commW {X : Nat} (hX : PP 100 7 X) (ws : List (List Int)) :
    (tabsOf ws).all (commT 100 (tabP 100 7 X)) =
      (ws.map pw).all (fun g => Nat.beq (pc 100 7 X g) (pc 100 7 g X)) := by
  rw [tabsOf, mapW]
  exact all_map_congr fun g hg => commT_tabP hX (ppL ws g hg)

theorem kCommP : (caGenW.map pw).all (fun g => Nat.beq (pc 100 7 (HP.F 0) g) (pc 100 7 g (HP.F 0))) =
      true ∧ (crGenW.map pw).all (fun g => Nat.beq (pc 100 7 RB g) (pc 100 7 g RB)) = true :=
  and_split kComm

theorem commA : ((tabsOf caGenW).all fun g => commT 100 b0T g) = true := by
  have e : b0T = tabP 100 7 (HP.F 0) := aT_eq
  rw [e, commW ppA]
  exact kCommP.1

theorem commB : ((tabsOf crGenW).all fun g => commT 100 rBT g) = true := by
  rw [rBT, wT, commW (ppw' wB)]
  exact kCommP.2

theorem any_rec {X : Nat} (hX : PP 100 7 X) {i : Nat} (hi : i < RH.CS.length)
    (hE : ∀ k < lget RH.CS i, lget RH.OFF i + k < RH.N) :
    (Array.ofFn (n := lget RH.CS i) fun k => tabP 100 7 (RH.E (lget RH.OFF i + k.val))).toList.any
        (tblEq 100 (tabP 100 7 X)) =
      (List.range (lget RH.CS i)).any fun k => Nat.beq X (RH.E (lget RH.OFF i + k)) := by
  have e : (Array.ofFn (n := lget RH.CS i) fun k => tabP 100 7 (RH.E (lget RH.OFF i + k.val))).toList =
      (List.range (lget RH.CS i)).map fun k => tabP 100 7 (RH.E (lget RH.OFF i + k)) := by
    rw [Array.toList_ofFn]
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp
  rw [e, List.any_map]
  refine any_congr' fun k hk => ?_
  have hk' := List.mem_range.1 hk
  simp only [Function.comp_apply]
  exact tblEq_tabP hX (inv_facts (hE k hk')).1

theorem cov_eq {X : Nat} (hX : PP 100 7 X) : invCovered (tabP 100 7 X) = invCovK X := by
  have hE : ∀ i (hi : i < RH.CS.length), ∀ k < lget RH.CS i, lget RH.OFF i + k < RH.N :=
    fun i hi k hk => (ci_eq kOff repK_all hi hk).1
  unfold invCovered invCovK invs
  rw [compT_tabP' hX hX, idT_tabP hsz, tblEq_tabP (hX.pc hX) (PP.id hsz), tblEq_tabP hX (PP.id hsz),
    List.any_append, clA_eq, clB_eq, any_rec hX hi0 (hE 0 hi0), any_rec hX hi1 (hE 1 hi1), lget_CS0,
    lget_CS1, lget_OFF0, lget_OFF1]
  simp only [Nat.zero_add, Bool.or_assoc]

theorem cover : countProducts 100 invCovered (levelTables t0Chain) (idT 100) = 512 := by
  have hL : levelTables t0Chain = (trPL 100 7 CT0.LR CT0.TR 2).map (List.map (tabP 100 7)) :=
    levelTables_eq chainT0 (by decide) (by decide)
  have hc := countProducts_tabP (n := 100) (w := 7) (f := invCovered) (fk := invCovK)
    (fun X hX => cov_eq hX) _ kTRP.2 _ (PP.id hsz)
  rw [hL, idT_tabP hsz, hc, Nat.eq_of_beq_eq_true kCov]

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.HS CFSG.RankThree.Native in
open Certificates in
theorem cert7219 :
    (permOK (hs100Arr 0) = true) ∧ (permOK (hs100Arr 1) = true) ∧
    (permOK hs100FiveLines[0]! = true) ∧ (permOK hs100FiveLines[2]! = true) ∧
    (permOK hs100FiveLines[23]! = true) ∧
    (invOK 100 aT (invT 100 aT) = true) ∧ (invOK 100 bT (invT 100 bT) = true) ∧
    (ordTest 100 7 x7T = true) ∧ (ordTest 100 11 x11T = true) ∧
    (conjTreeOK 100 genArr genInvArr b0T clA.1 clA.2.1 clA.2.2 = true) ∧
    (conjTreeOK 100 genArr genInvArr rBT clB.1 clB.2.1 clB.2.2 = true) ∧
    (keysDistinct 100 clA.1.toList = true) ∧ (keysDistinct 100 clB.1.toList = true) ∧
    (clA.1.size = 5775) ∧ (clB.1.size = 15400) ∧
    (caChain.check = true) ∧ (caChain.orderCertificate = 7680) ∧
    (((tabsOf caGenW).all fun g => commT 100 b0T g) = true) ∧
    (crChain.check = true) ∧ (crChain.orderCertificate = 2880) ∧
    (((tabsOf crGenW).all fun g => commT 100 rBT g) = true) ∧
    (t0Chain.check = true) ∧ (t0Chain.orderCertificate = 512) ∧
    (countProducts 100 invCovered (levelTables t0Chain) (idT 100) = 512) := by
  obtain ⟨a1, a2⟩ := chainK_check (by decide) (by decide) chainCA
  obtain ⟨r1, r2⟩ := chainK_check (by decide) (by decide) chainCR
  obtain ⟨t1, t2⟩ := chainK_check (by decide) (by decide) chainT0
  obtain ⟨o1, o2, o3, -, -, -⟩ := kOrdP
  refine ⟨permOK_of arr0 kInvP.1 kInvP.2.1, permOK_of arr1 kInvP.2.2.1 kInvP.2.2.2.1,
    permOK_of line0 kInvP.2.2.2.2.1 kInvP.2.2.2.2.2.1,
    permOK_of line2 kInvP.2.2.2.2.2.2.1 kInvP.2.2.2.2.2.2.2.1,
    permOK_of line23 kInvP.2.2.2.2.2.2.2.2.1 kInvP.2.2.2.2.2.2.2.2.2, ?_, ?_, ?_, ?_, treeA, treeB,
    keysA, keysB, sizeA, sizeB, a1, a2.trans o1, commA, r1, r2.trans o2, commB, t1, t2.trans o3,
    cover⟩
  · rw [aT_eq]; exact invOK_tabP ppA
  · rw [bT_eq]; exact invOK_tabP ppB
  · rw [x7T, wT, ordTest_tabP (ppw' w7)]; exact kOrd7
  · rw [x11T, wT, ordTest_tabP (ppw' w11)]; exact kOrd11

end CertificateChecks.KernelKGC31HS

end
