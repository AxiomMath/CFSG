
module

public import Certificates.Kernel.SporSch.Co2M.ThEA
public import Certificates.Kernel.SporSch.Co2M.ThEQC
public import Certificates.Kernel.SporSch.Co2M.ThEQJ
public import Certificates.Kernel.SporSch.Co2M.FratM
public import Certificates.Kernel.SporSch.Co2M.Span
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.MatRep CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.KS.Co2LE

local notation "teGA" => gArrsOf co2PosTable witRec

local notation "teQA" => quArrsOf (gArrsOf co2PosTable witRec)

local notation "tePis" =>
  conjPis (gArrsOf co2PosTable witRec) 1024 (leftEnum (quArrsOf (gArrsOf co2PosTable witRec)) 1024)

theorem te_rep_pow {t : Array ℕ} {p : ℕ × ℕ} (ht : MatRep.Rep 22 co2PackedVecs t p.1 p.2) :
    ∀ e, MatRep.Rep 22 co2PackedVecs (powA t e) (tePow p e).1 (tePow p e).2
  | 0 => rep_I22
  | e + 1 => rep_cmp (te_rep_pow ht e) ht

theorem te_qRep : RepT 22 co2PackedVecs teQA teQT := by
  unfold quArrsOf teQT
  refine repT_ofList fun r hr => te_rep_pow (rep_prodArrM te_gRep fun i hi => ?_) r.2
  have := List.all_eq_true.1 (List.all_eq_true.1 te_facts.2.2.2.2.2.2.1 r hr) i hi
  rw [te_gT_len]
  simpa using this

theorem te_qT_len : teQT.length = 10 := by rw [teQT, List.length_map, te_facts.2.2.2.2.2.1]

theorem te_qA_size : (teQA).size = 10 := by rw [te_qRep.1, te_qT_len]

theorem te_qgens : GensRep co2PackedVecs teQA TQG 10 := by
  refine ⟨te_qA_size, fun j hj => ⟨(teQT.getD j (0, 0)).2, ?_⟩⟩
  rw [Nat.eq_of_beq_eq_true (allN_spec te_qg j hj)]
  exact repT_get te_qRep (by rw [te_qT_len]; exact hj)

theorem te_qrec_all : ∀ k < 1024, recK TQR TQG (PV 0) 10 1024 k = true := by
  intro k hk
  rcases (by omega : k < 256 ∨ (256 ≤ k ∧ k < 512) ∨ (512 ≤ k ∧ k < 768) ∨ 768 ≤ k) with
    h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
  · exact allN_spec te_qrecs0 k h
  · have h := allN_spec te_qrecs1 (k - 256) (by omega)
    have e : Nat.add 256 (k - 256) = k := by simp only [Nat.add_eq]; omega
    rwa [e] at h
  · have h := allN_spec te_qrecs2 (k - 512) (by omega)
    have e : Nat.add 512 (k - 512) = k := by simp only [Nat.add_eq]; omega
    rwa [e] at h
  · have h := allN_spec te_qrecs3 (k - 768) (by omega)
    have e : Nat.add 768 (k - 768) = k := by simp only [Nat.add_eq]; omega
    rwa [e] at h

theorem te_qrecs : Recs TQR TQG (PV 0) 10 1024 := by
  obtain ⟨h1, h2⟩ := (bAnd_iff (Nat.beq (eM TQR 0) I22) (Nat.beq (mR TQR 10 0) 1)).1 te_qhead
  exact ⟨te_qrec_all, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, by norm_num⟩

theorem te_qconj_all : ∀ i < 15, ∀ k < 1024,
    conjK TQR (TGM i) (TGMI i) (Co2EQ.S i) 11 1024 k = true := by
  intro i hi
  rcases (by omega : i < 5 ∨ (5 ≤ i ∧ i < 10) ∨ (10 ≤ i ∧ i < 15)) with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact allN_spec (allN_spec te_qconj0 i h)
  · have h := allN_spec te_qconj1 (i - 5) (by omega)
    have e : Nat.add 5 (i - 5) = i := by simp only [Nat.add_eq]; omega
    rw [e] at h
    exact allN_spec h
  · have h := allN_spec te_qconj2 (i - 10) (by omega)
    have e : Nat.add 10 (i - 10) = i := by simp only [Nat.add_eq]; omega
    rw [e] at h
    exact allN_spec h

theorem te_hcr : ∀ i < 15, MatRep.Rep 22 co2PackedVecs teGA[i]! (TGM i) (TGMI i) := by
  intro i hi
  rw [te_gA_get hi]
  exact te_sRep hi

theorem te_pis_get : ∀ i < 15, tePis[i]! = unpack 1024 11 (Co2EQ.S i) :=
  CFSG.KS.Co2ThirdE.conjPis_get vok te_qrecs te_qgens (le_refl 1024) te_gA_size te_hcr
    te_qconj_all

theorem te_pis_size : (tePis).size = 15 := by
  unfold conjPis
  rw [Array.size_map, te_gA_size]

theorem te_enumOK : enumOK teQA 1024 (leftEnum teQA 1024) = true :=
  (leftEnum_facts vok te_qrecs te_qgens (le_refl 1024)).2.1

theorem te_conjOK : conjOK teGA tePis 1024 (leftEnum teQA 1024) = true :=
  conjOK_of vok te_qrecs te_qgens (le_refl 1024) te_gA_size te_hcr
    (fun i hi k hk => by
      rw [te_pis_get i hi]
      exact CFSG.KC.Misc.PairCount.unpack_get hk)
    te_qconj_all

theorem te_qmat_spec {i : ℕ} (hi : i < 10) : mmK (TQG i) (TQG i) = I22 ∧
    ∀ j < 10, mmK (TQG j) (TQG i) = mmK (TQG i) (TQG j) := by
  exact ⟨Nat.eq_of_beq_eq_true (allN_spec te_qsq_ok i hi),
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec (allN_spec te_qcomm_ok i hi) j hj)⟩

theorem te_qRepG {i : ℕ} (hi : i < 10) :
    MatRep.Rep 22 co2PackedVecs teQA[i]! (TQG i) (teQT.getD i (0, 0)).2 := by
  rw [Nat.eq_of_beq_eq_true (allN_spec te_qg i hi)]
  exact repT_get te_qRep (by rw [te_qT_len]; exact hi)

theorem te_qinv {i : ℕ} (hi : i < 10) : isInvA 2300 teQA[i]! (invCand 2300 teQA[i]!) = true :=
  isInvA_rep (te_qRepG hi)

theorem te_qsq {i : ℕ} (hi : i < 10) :
    eqA 2300 (compA 2300 teQA[i]! teQA[i]!) (idA 2300) = true := by
  have h := (rep_compA good (te_qRepG hi) (te_qRepG hi)).1
  rw [V_size, ← mmK_eq, (te_qmat_spec hi).1, ← idA_eq] at h
  rw [h]
  exact eqA_self _ _

theorem te_qcomm {i j : ℕ} (hi : i < 10) (hj : j < 10) :
    eqA 2300 (compA 2300 teQA[i]! teQA[j]!) (compA 2300 teQA[j]! teQA[i]!) = true := by
  have h1 := (rep_compA good (te_qRepG hi) (te_qRepG hj)).1
  have h2 := (rep_compA good (te_qRepG hj) (te_qRepG hi)).1
  rw [V_size, ← mmK_eq, (te_qmat_spec hi).2 j hj] at h1
  rw [V_size, ← mmK_eq] at h2
  rw [h1, h2]
  exact eqA_self _ _

theorem te_qmats : allLt 10 (fun i => isInvA 2300 teQA[i]! (invCand 2300 teQA[i]!) &&
    eqA 2300 (compA 2300 teQA[i]! teQA[i]!) (idA 2300) &&
    allLt 10 (fun j => eqA 2300 (compA 2300 teQA[i]! teQA[j]!) (compA 2300 teQA[j]! teQA[i]!))) =
    true := by
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  simp only [Bool.and_eq_true]
  refine ⟨⟨te_qinv hi, te_qsq hi⟩, ?_⟩
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro j hj
  exact te_qcomm hi hj

theorem te_qS_bind : (extendArrsN 1024 tePis quDerivs).size = 17 ∧
    ∀ j < 17, (extendArrsN 1024 tePis quDerivs)[j]! = unpack 1024 11 (Co2EQ.S j) := by
  rw [CFSG.KS.Co2ThirdE.extendArrsN_eq]
  exact strongOf_bind ⟨te_pis_size, te_pis_get⟩ Co2EQ.head

theorem te_qR_strong : (quRecOf tePis).strongArrs = extendArrsN 1024 tePis quDerivs := by
  unfold quRecOf ChainRecord.strongArrs
  simp only [List.map_map]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp

theorem te_qBaseOK : (Nat.beq ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List ℕ).toArray.size 10 &&
    allN 10 fun t => Nat.beq ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List ℕ).toArray[t]!
      (pg 11 (mask 11) Co2EQ.BP t)) = true := by
  quickRfl

theorem te_qBinds : Binds 1024 11 Co2EQ.S 17 10 Co2EQ.BP (quRecOf tePis).strongArrs
    (quRecOf tePis).baseArr := by
  have hb := te_qBaseOK
  rw [Bool.and_eq_true] at hb
  rw [te_qR_strong]
  exact ⟨by norm_num, by norm_num, by norm_num, te_qS_bind.1, te_qS_bind.2,
    Nat.eq_of_beq_eq_true hb.1, fun t ht => Nat.eq_of_beq_eq_true (allN_spec hb.2 t ht)⟩

theorem te_qR_gens : (quRecOf tePis).generators = (quRecOf tePis).strongGenerators.take 15 := by
  change (tePis).toList.map Array.toList =
    ((extendArrsN 1024 tePis quDerivs).toList.map Array.toList).take 15
  rw [← List.map_take, ← te_pis_size]
  exact congrArg (List.map Array.toList)
    (CFSG.KS.Co2ThirdE.extendArrsN_take 1024 tePis quDerivs).symm

theorem te_qR_glen : (quRecOf tePis).generators.length = 15 := by
  change ((tePis).toList.map Array.toList).length = 15
  simp [te_pis_size]

theorem te_qR_dlen : (quRecOf tePis).derivations.length + 15 = 17 := by
  change quDerivs.length + 15 = 17
  rw [te_facts.2.2.2.2.2.2.2.1]

theorem te_qRecord : recordOK 1024 (quRecOf tePis) 4 = true :=
  recordOK_of (NS := 64) (CH := 16) te_qR_gens te_qR_glen te_qR_dlen te_qBinds Co2EQ.head
    Co2EQ.hl (by norm_num) Co2EQ.hs

theorem te_qOrbits : recordOrbits 1024 (quRecOf tePis) = [45, 16, 1, 2, 1, 1, 1, 1, 1, 1] := by
  rw [recordOrbits_of te_qBinds Co2EQ.perm Co2EQ.hl]
  decide +kernel

theorem te_qShape : chainShapeOK (quRecOf tePis) 1024 15 17 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] =
    true := by
  have hstrong := te_qS_bind
  unfold chainShapeOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨rfl, te_qR_glen⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, rfl⟩, ?_⟩
  · change ((extendArrsN 1024 tePis quDerivs).toList.map Array.toList).length = 17
    simp [hstrong.1]
  · change quDerivs.length = 17 - 15
    rw [te_facts.2.2.2.2.2.2.2.1]
  · change ((tePis).toList.map Array.toList).all (isPermList 1024) = true
    refine CFSG.KS.Co2ThirdE.all_isPermList fun j hj => ?_
    rw [te_pis_size] at hj
    rw [te_pis_get j hj]
    exact CFSG.KS.Co2ThirdE.isPermList_unpack (allN_spec Co2EQ.perm j (by omega))
  · change ((extendArrsN 1024 tePis quDerivs).toList.map Array.toList).all
      (isPermList 1024) = true
    refine CFSG.KS.Co2ThirdE.all_isPermList fun j hj => ?_
    rw [hstrong.1] at hj
    rw [hstrong.2 j hj]
    exact CFSG.KS.Co2ThirdE.isPermList_unpack (allN_spec Co2EQ.perm j hj)
  · exact te_facts.2.2.2.2.2.2.2.2

end CertificateChecks.KernelSporSch.Co2M

end
