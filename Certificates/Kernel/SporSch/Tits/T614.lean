module

public import Certificates.Kernel.SporSch.Tits.T614A
public import Certificates.Kernel.SporSch.Tits.T614CJ
public import Certificates.Kernel.SporSch.Tits.T614QK
public import Certificates.Kernel.SporSch.Tits.T614N
public import CFSG.Certificates.Kernel.SporSch.TitsEnum5QSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Schreier.TitsPair
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public meta import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.T614

meta def ouRepM : List (Array Nat) := (List.range 64).map CFSG.Quasithin.H13.Tits614.ouRepArr

meta def ouInvM : List (Array Nat) := (List.range 64).map fun k =>
  CFSG.Monster.B.Co2.Native.invCand 1755
    (CFSG.Quasithin.H13.Tits614.outerArr (CFSG.Quasithin.H13.Tits614.ouRepArr k))

end CertificateChecks.KernelSporSch.T614

#kst_plist CertificateChecks.KernelSporSch.T614OR 11 CertificateChecks.KernelSporSch.T614.ouRepM

#kst_plist CertificateChecks.KernelSporSch.T614OUI 11 CertificateChecks.KernelSporSch.T614.ouInvM

namespace CertificateChecks.KernelSporSch.T614

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Quasithin.H13.Tits614
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelMisc
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsAbel

theorem strictB_eq7195 (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem cjp_check_k : all5 1755 titsSLevels (fun a => !(inJ a) ||
    !(eqA 1755 (compA 1755 a pArr) (compA 1755 pArr a)) || eqA 1755 a (idA 1755) ||
    eqA 1755 a titsZArr) = true := by
  refine all5K_sound bindsS permS TitsS.hl (fun t0 t1 t2 t3 t4 c0 c1 c2 c3 c4 _ h => ?_) T614CJ.all
  rw [p_eq, ← commPts_sound c0 c1 c2 c3 c4 cP, id_eq, ← eqPts_sound c0 c1 c2 c3 c4 canId, z_eq,
    ← eqPts_sound c0 c1 c2 c3 c4 canonZ]
  change bIf(commPts 1755 11 (mask 11) T614P t0 t1 t2 t3 t4,
    bIf(eqPts 1755 11 (mask 11) (pidn 1755 11) t0 t1 t2 t3 t4, true,
      eqPts 1755 11 (mask 11) TitsZ t0 t1 t2 t3 t4), true) = true at h
  cases hc : commPts 1755 11 (mask 11) T614P t0 t1 t2 t3 t4
  · simp
  · rw [hc] at h
    cases he : eqPts 1755 11 (mask 11) (pidn 1755 11) t0 t1 t2 t3 t4
    · rw [he] at h
      simp [h]
    · simp

theorem piK : Nat.beq T614PI (pinv T614P) = true := by quickRfl

theorem cPIK : C T614PI := by
  rw [Nat.eq_of_beq_eq_true piK]
  exact cPI

theorem canJ614 : allN 4 (fun j => canonK 1755 11 (mask 11) (1755 * 11) (TitsJ.S j)) = true := by
  quickRfl

theorem inS_eq614 {X : Nat} (hX : C X) : inS (unpack 1755 11 X) = sS X :=
  siftK_eq bindsS permS TitsS.hl rfl (hi_of hX) (range_of_canonK hX)

theorem sPow_eq614 : ∀ k, (compA 1755 titsSArrs[0]!)^[k] (idA 1755) =
    unpack 1755 11 (pw (TitsS.S 0) k) ∧ C (pw (TitsS.S 0) k)
  | 0 => ⟨id_eq, canId⟩
  | k + 1 => by
    obtain ⟨e, c⟩ := sPow_eq614 k
    refine ⟨?_, cc (cS (by omega)) c⟩
    rw [Function.iterate_succ_apply', e, bindsS.2.2.2.2.1 0 (by omega), cu (cS (by omega)) c]
    rfl

theorem pConj_eq614 {X : Nat} (hX : C X) :
    compA 1755 (compA 1755 (invCand 1755 pArr) (unpack 1755 11 X)) pArr =
      unpack 1755 11 (pc (pc T614PI X) T614P) := by
  have ePI : invCand 1755 (unpack 1755 11 T614P) = unpack 1755 11 T614PI := by
    rw [Nat.eq_of_beq_eq_true piK]
    exact invCand_unpack permP'
  rw [p_eq, ePI, cu cPIK hX, cu (cc cPIK hX) cP]

theorem kSSJ : allN 4 (fun j => sS (pc (pc T614PI (TitsJ.S j)) T614P)) = true := by quickRfl

theorem kSSRJ : allN 3 (fun k => !(sfJ (pw (TitsS.S 0) (k + 1)))) = true := by quickRfl

theorem kSSRS : allN 3 (fun k => !(sS (pc (pc T614PI (pw (TitsS.S 0) (k + 1))) T614P))) = true := by
  quickRfl

theorem ssp_check_k :
    (allLt 4 fun j => inS (compA 1755 (compA 1755 (invCand 1755 pArr) titsJArrs[j]!) pArr)) =
      true ∧
    (allLt 3 fun k => !(inJ ((compA 1755 titsSArrs[0]!)^[k + 1] (idA 1755))) &&
      !(inS (compA 1755 (compA 1755 (invCand 1755 pArr)
        ((compA 1755 titsSArrs[0]!)^[k + 1] (idA 1755))) pArr))) = true := by
  refine ⟨allLt_iff.2 fun j hj => ?_, allLt_iff.2 fun k hk => ?_⟩
  · have cJ : C (TitsJ.S j) := allN_spec canJ614 j hj
    rw [bindsJ.2.2.2.2.1 j (by omega), pConj_eq614 cJ, inS_eq614 (cc (cc cPIK cJ) cP)]
    exact allN_spec kSSJ j hj
  · obtain ⟨e, c⟩ := sPow_eq614 (k + 1)
    rw [e, pConj_eq614 c, inS_eq614 (cc (cc cPIK c) cP), inJ_eq c, Bool.and_eq_true]
    exact ⟨allN_spec kSSRJ k hk, allN_spec kSSRS k hk⟩

theorem cG1 : C T614G1 := by quickRfl
theorem permG1 : permOK 1755 11 (mask 11) (1755 * 11) T614G1 (pinvS 1755 11 (mask 11) T614G1) =
    true := by quickRfl
theorem g1K : Nat.beq T614G1 (TitsText.F 1) = true := by quickRfl

theorem gen1_eq : titsGenArrs[1]! = unpack 1755 11 T614G1 := by
  rw [Nat.eq_of_beq_eq_true g1K]
  exact gen_eq (by norm_num)
theorem canKK : allN 7 (fun j => canonK 1755 11 (mask 11) (1755 * 11) (TitsK.S j)) = true := by
  quickRfl
theorem canNK : allN 10 (fun j => bAnd(canonK 1755 11 (mask 11) (1755 * 11) (TitsN.S j),
    canonK 1755 11 (mask 11) (1755 * 11) (TitsN.SI j))) = true := by quickRfl

theorem cG1I : C (pinv T614G1) := by quickRfl

theorem eG1I : invCand 1755 (unpack 1755 11 T614G1) = unpack 1755 11 (pinv T614G1) :=
  invCand_unpack permG1

theorem canHK : allN 3 (fun j => bAnd(canonK 1755 11 (mask 11) (1755 * 11) (TitsH.S j),
    canonK 1755 11 (mask 11) (1755 * 11) (TitsH.SI j))) = true := by quickRfl

@[expose] noncomputable def ouRepK (k : Nat) : Nat :=
  (ouRepWord k).foldl (fun a i => pc a (TitsS.S i)) (pidn 1755 11)

theorem ouRepWord_lt9 : ∀ k < 64, ∀ i ∈ ouRepWord k, i < 9 := by decide

theorem ouRep_eqF {k : Nat} (hk : k < 64) :
    ouRepArr k = unpack 1755 11 (ouRepK k) ∧ C (ouRepK k) := by
  have key : ∀ l : List Nat, (∀ i ∈ l, i < 9) → ∀ a, C a →
      l.foldl (fun b i => compA 1755 b titsSArrs[i]!) (unpack 1755 11 a) =
        unpack 1755 11 (l.foldl (fun b i => pc b (TitsS.S i)) a) ∧
      C (l.foldl (fun b i => pc b (TitsS.S i)) a) := by
    intro l
    induction l with
    | nil => intro _ a ha; exact ⟨rfl, ha⟩
    | cons i l ih =>
      intro hl a ha
      have hi := hl i List.mem_cons_self
      simp only [List.foldl_cons]
      rw [s_get hi, cu ha (cS hi)]
      exact ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _ (cc ha (cS hi))
  unfold ouRepArr ouRepK
  rw [id_eq]
  exact key _ (ouRepWord_lt9 k hk) _ canId

theorem orK : allN 64 (fun k => Nat.beq (T614OR.getD k 0) (ouRepK k)) = true := by quickRfl

theorem ouRep_eqK {k : Nat} (hk : k < 64) :
    ouRepArr k = unpack 1755 11 (T614OR.getD k 0) ∧ C (T614OR.getD k 0) := by
  have e : T614OR.getD k 0 = ouRepK k := Nat.eq_of_beq_eq_true (allN_spec orK k hk)
  rw [e]
  exact ouRep_eqF hk

theorem kOA : allN 5 (fun i => strictB (pc (pc (pinv T614G1) (T614EG.getD i 0)) T614G1)
    (fun X => T614EL.any (Nat.beq X))) = true := by
  quickRfl

theorem kOB : allN 3 (fun j => allN 5 (fun i =>
    strictB (pc (pc (TitsH.SI j) (T614EG.getD i 0)) (TitsH.S j))
      (fun X => T614EL.any (Nat.beq X)))) = true := by
  quickRfl

theorem kON : allN 4 (fun j => allN 5 (fun i =>
    strictB (pc (pc (TitsN.SI j) (T614EG.getD i 0)) (TitsN.S j)) sfK)) = true := by
  quickRfl

theorem kOC : allN 3 (fun g => allN 64 (fun k =>
    decide ((ouCov g k).1 < 64) && decide ((ouCov g k).2 < 32) &&
    Nat.beq (pc (TitsS.S g) (T614OR.getD k 0))
      (pc (T614OR.getD (ouCov g k).1 0) (T614EL.getD (ouCov g k).2 0)))) = true := by
  quickRfl

@[expose] noncomputable def ouTest (U UI : Nat) : Bool :=
  bAnd(permOK 1755 11 (mask 11) (1755 * 11) U UI,
  bAnd(canonK 1755 11 (mask 11) (1755 * 11) UI,
    !(allN 3 (fun i => strictB (pc (pc (pc UI (TitsH.SI i)) U) (TitsH.S i))
      (fun X => T614EL.any (Nat.beq X)))) ||
    bAnd(allN 2 (fun j => sfK (pc (pc U (TitsK.S j)) UI)),
      allN 4 (fun j => sfK (pc (pc (pc UI (TitsN.SI j)) U) (TitsN.S j))))))

theorem kOR : allN 64 (fun k => strictB (pc (T614OR.getD k 0) T614G1)
    (fun U => ouTest U (T614OUI.getD k 0))) = true := by
  quickRfl

theorem outer_check_k :
    (allLt 5 fun i => inE (compA 1755 (compA 1755 (invCand 1755 titsGenArrs[1]!) (eGenArr i))
      titsGenArrs[1]!)) = true ∧
    (allLt 3 fun j => allLt 5 fun i =>
      inE (compA 1755 (compA 1755 (invCand 1755 titsHArrs[j]!) (eGenArr i)) titsHArrs[j]!)) =
      true ∧
    (allLt 4 fun j => allLt 5 fun i =>
      inK (compA 1755 (compA 1755 (invCand 1755 titsNArrs[j]!) (eGenArr i)) titsNArrs[j]!)) =
      true ∧
    (allLt 3 fun g => allLt 64 fun k =>
      decide ((ouCov g k).1 < 64) && decide ((ouCov g k).2 < 32) &&
      eqA 1755 (compA 1755 titsSArrs[g]! (ouRepArr k))
        (compA 1755 (ouRepArr (ouCov g k).1) (eProdArr (ouCov g k).2))) = true ∧
    (allLt 64 fun k =>
      !(allLt 3 fun i => inE (commArr 1755 (outerArr (ouRepArr k)) titsHArrs[i]!)) ||
      ((allLt 2 fun j => inK (conjArr (outerArr (ouRepArr k)) titsKArrs[j]!)) &&
        (allLt 4 fun j => inK (commArr 1755 (outerArr (ouRepArr k)) titsNArrs[j]!)))) = true := by
  refine ⟨allLt_iff.2 fun i hi => ?_, allLt_iff.2 fun j hj => allLt_iff.2 fun i hi => ?_,
    allLt_iff.2 fun j hj => allLt_iff.2 fun i hi => ?_,
    allLt_iff.2 fun g hg => allLt_iff.2 fun k hk => ?_, allLt_iff.2 fun k hk => ?_⟩
  · have c := cEG hi
    rw [gen1_eq, eG1I, eg_eq hi, cu cG1I c, cu (cc cG1I c) cG1, inE_eq (cc (cc cG1I c) cG1)]
    have h := allN_spec kOA i hi
    simp only [strictB_eq7195] at h
    exact h
  · have c := cEG hi
    have cH := ((bAnd_iff _ _).1 (allN_spec canHK j hj)).1
    have cHI := ((bAnd_iff _ _).1 (allN_spec canHK j hj)).2
    have eHI := (invEqK_sound (allN_spec permH j (by omega))).1
    rw [bindsH.2.2.2.2.1 j (by omega), eHI, eg_eq hi, cu cHI c, cu (cc cHI c) cH,
      inE_eq (cc (cc cHI c) cH)]
    have h := allN_spec (allN_spec kOB j hj) i hi
    simp only [strictB_eq7195] at h
    exact h
  · have c := cEG hi
    have cN : C (TitsN.S j) := ((bAnd_iff _ _).1 (allN_spec canNK j (by omega))).1
    have cNI : C (TitsN.SI j) := ((bAnd_iff _ _).1 (allN_spec canNK j (by omega))).2
    have eNI := (invEqK_sound (allN_spec permN j (by omega))).1
    rw [bindsN.2.2.2.2.1 j (by omega), eNI, eg_eq hi, cu cNI c, cu (cc cNI c) cN,
      inK_eq (cc (cc cNI c) cN)]
    have h := allN_spec (allN_spec kON j hj) i hi
    simp only [strictB_eq7195] at h
    exact h
  · have h := allN_spec (allN_spec kOC g hg) k hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨ht, hv⟩, hb⟩ := h
    refine ⟨⟨ht, hv⟩, ?_⟩
    obtain ⟨e1, c1⟩ := ouRep_eqK hk
    obtain ⟨e2, c2⟩ := ouRep_eqK ht
    have cg : C (TitsS.S g) := cS (by omega)
    rw [s_get (by omega), e1, e2, ep_eq hv, cu cg c1, cu c2 (cEp hv),
      eqA_unpack (cc cg c1) (cc c2 (cEp hv))]
    exact hb
  · have h := allN_spec kOR k hk
    simp only [strictB_eq7195] at h
    obtain ⟨e1, c1⟩ := ouRep_eqK hk
    have cU : C (pc (T614OR.getD k 0) T614G1) := cc c1 cG1
    have hu : outerArr (ouRepArr k) = unpack 1755 11 (pc (T614OR.getD k 0) T614G1) := by
      unfold outerArr
      rw [gen1_eq, e1, cu c1 cG1]
    rw [hu]
    generalize pc (T614OR.getD k 0) T614G1 = U at h cU ⊢
    generalize T614OUI.getD k 0 = V at h
    unfold ouTest at h
    obtain ⟨kp, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨kc, h⟩ := (bAnd_iff _ _).1 h
    have eUI : invCand 1755 (unpack 1755 11 U) = unpack 1755 11 V := (invEqK_sound kp).1
    have eA : (allLt 3 fun i => inE (commArr 1755 (unpack 1755 11 U) titsHArrs[i]!)) =
        allN 3 (fun i => strictB (pc (pc (pc V (TitsH.SI i)) U) (TitsH.S i))
          (fun X => T614EL.any (Nat.beq X))) :=
      allLt_eq_allN fun i hi => by
        simp only [strictB_eq7195]
        have cH := ((bAnd_iff _ _).1 (allN_spec canHK i hi)).1
        have cHI := ((bAnd_iff _ _).1 (allN_spec canHK i hi)).2
        have eHI := (invEqK_sound (allN_spec permH i (by omega))).1
        unfold commArr
        rw [bindsH.2.2.2.2.1 i (by omega), eUI, eHI, cu kc cHI, cu (cc kc cHI) cU,
          cu (cc (cc kc cHI) cU) cH, inE_eq (cc (cc (cc kc cHI) cU) cH)]
    have eK : (allLt 2 fun j => inK (conjArr (unpack 1755 11 U) titsKArrs[j]!)) =
        allN 2 (fun j => sfK (pc (pc U (TitsK.S j)) V)) :=
      allLt_eq_allN fun j hj => by
        have cK : C (TitsK.S j) := allN_spec canKK j (by omega)
        unfold conjArr
        rw [bindsK.2.2.2.2.1 j (by omega), eUI, cu cU cK, cu (cc cU cK) kc,
          inK_eq (cc (cc cU cK) kc)]
    have eN : (allLt 4 fun j => inK (commArr 1755 (unpack 1755 11 U) titsNArrs[j]!)) =
        allN 4 (fun j => sfK (pc (pc (pc V (TitsN.SI j)) U) (TitsN.S j))) :=
      allLt_eq_allN fun j hj => by
        have cN : C (TitsN.S j) := ((bAnd_iff _ _).1 (allN_spec canNK j (by omega))).1
        have cNI : C (TitsN.SI j) := ((bAnd_iff _ _).1 (allN_spec canNK j (by omega))).2
        have eNI := (invEqK_sound (allN_spec permN j (by omega))).1
        unfold commArr
        rw [bindsN.2.2.2.2.1 j (by omega), eUI, eNI, cu kc cNI, cu (cc kc cNI) cU,
          cu (cc (cc kc cNI) cU) cN, inK_eq (cc (cc (cc kc cNI) cU) cN)]
    rw [eA, eK, eN]
    cases hA : allN 3 (fun i => strictB (pc (pc (pc V (TitsH.SI i)) U) (TitsH.S i))
        (fun X => T614EL.any (Nat.beq X)))
    · rfl
    · rw [hA, Bool.not_true, Bool.false_or] at h
      obtain ⟨hB, hC⟩ := (bAnd_iff _ _).1 h
      rw [hB, hC]
      rfl

theorem batch7195 :
    (allLt 1755 (fun x => decide (x < 3) ||
        !(allLt 3 fun j => (titsRArrs[j]!)[x]! == x)) = true)
    ∧ (lettersOK 3 pWord = true ∧ eqA 1755 (pow5Arr pArr) (idA 1755) = true)
    ∧ ((∀ i < 5, lettersOK 4 (eXWord i) = true ∧ lettersOK 4 (eYWord i) = true) ∧
      eqA 1755 (eProdArr 0) (idA 1755) = true ∧ (allLt 5 fun i => inE (eGenArr i)) = true ∧
      (allLt 32 fun v => allLt 32 fun w => inE (compA 1755 (eProdArr v) (eProdArr w)) &&
        eqA 1755 (compA 1755 (eProdArr v) (eProdArr w))
          (compA 1755 (eProdArr w) (eProdArr v))) = true ∧
      (allLt 32 fun v => eqA 1755 (compA 1755 (eProdArr v) (eProdArr v)) (idA 1755)) = true ∧
      eArrs.Pairwise (fun a b => eqA 1755 a b = false) ∧
      eArrs.all (fun c => isInvA 1755 c (invCand 1755 c)) = true ∧
      (allLt 32 fun v => inJ (eProdArr v) && inK (eProdArr v)) = true ∧
      (allLt 5 fun i => inE (conjArr pArr (eGenArr i))) = true ∧ inE titsZArr = true)
    ∧ (all5 1755 titsSLevels (fun a => !(inJ a) ||
        !(eqA 1755 (compA 1755 a pArr) (compA 1755 pArr a)) || eqA 1755 a (idA 1755) ||
        eqA 1755 a titsZArr) = true)
    ∧ (all5 1755 titsHLevels (fun a =>
        !(allLt 3 fun i => inS (conjArr a titsSArrs[i]!)) || inS a) = true)
    ∧ ((allLt 4 fun j => inS (compA 1755 (compA 1755 (invCand 1755 pArr) titsJArrs[j]!) pArr)) =
        true ∧
      (allLt 3 fun k => !(inJ ((compA 1755 titsSArrs[0]!)^[k + 1] (idA 1755))) &&
        !(inS (compA 1755 (compA 1755 (invCand 1755 pArr)
          ((compA 1755 titsSArrs[0]!)^[k + 1] (idA 1755))) pArr))) = true)
    ∧ ((allLt 5 fun i => inE (compA 1755 (compA 1755 (invCand 1755 titsGenArrs[1]!) (eGenArr i))
        titsGenArrs[1]!)) = true ∧
      (allLt 3 fun j => allLt 5 fun i =>
        inE (compA 1755 (compA 1755 (invCand 1755 titsHArrs[j]!) (eGenArr i)) titsHArrs[j]!)) =
        true ∧
      (allLt 4 fun j => allLt 5 fun i =>
        inK (compA 1755 (compA 1755 (invCand 1755 titsNArrs[j]!) (eGenArr i)) titsNArrs[j]!)) =
        true ∧
      (allLt 3 fun g => allLt 64 fun k =>
        decide ((ouCov g k).1 < 64) && decide ((ouCov g k).2 < 32) &&
        eqA 1755 (compA 1755 titsSArrs[g]! (ouRepArr k))
          (compA 1755 (ouRepArr (ouCov g k).1) (eProdArr (ouCov g k).2))) = true ∧
      (allLt 64 fun k =>
        !(allLt 3 fun i => inE (commArr 1755 (outerArr (ouRepArr k)) titsHArrs[i]!)) ||
        ((allLt 2 fun j => inK (conjArr (outerArr (ouRepArr k)) titsKArrs[j]!)) &&
          (allLt 4 fun j => inK (commArr 1755 (outerArr (ouRepArr k)) titsNArrs[j]!)))) = true) :=
  ⟨fix_check_k, p_check_k, e_check_k, cjp_check_k, nhs_check_k, ssp_check_k, outer_check_k⟩

end CertificateChecks.KernelSporSch.T614

end
