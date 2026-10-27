
module

public import Certificates.Kernel.SporSch.Co2M.ThEG
public import Certificates.Kernel.SporSch.Co2M.ThEJ
public import Certificates.Kernel.SporSch.Co2M.Class
public import Certificates.Kernel.SporSch.Co2M.WordsBase
public import CFSG.Certificates.Kernel.SporSch.Co2ThirdE
public import CFSG.Certificates.Kernel.SporSch.RecordSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.StrongOfSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.MatRep CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Mathieu

theorem te_facts : (oddMats witRec).length = 15 ∧ (oddMats witRec).all rows22OK = true ∧
    eDerivs.length = 11 ∧ extOK 15 eDerivs = true ∧
    ((List.range 11).all fun j => lettersOK (j + 15) (eDerivs.getD j [])) = true ∧
    quRecipe.length = 10 ∧ (quRecipe.all fun r => r.1.all fun i => decide (i < 15)) = true ∧
    quDerivs.length = 2 ∧
    ((List.range 2).all fun j => lettersOK (j + 15) (quDerivs.getD j [])) = true := by
  decide +kernel

theorem te_gA_size : (gArrsOf co2PosTable witRec).size = 15 := by
  unfold gArrsOf
  simp [te_facts.1]

theorem te_gT_len : teGT.length = 15 := by simp [teGT]

theorem te_gT_get {j : ℕ} (hj : j < 15) : teGT.getD j (0, 0) = (TGM j, TGMI j) := by
  unfold teGT
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem te_bind {j : ℕ} (hj : j < 15) : bindK (PV 0) (Co2E.S j) (TGM j) (TGMI j) = true := by
  rcases (by omega : j < 5 ∨ (5 ≤ j ∧ j < 10) ∨ (10 ≤ j ∧ j < 15)) with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact allN_spec te_bind0 j h
  · have h := allN_spec te_bind1 (j - 5) (by omega)
    have e : Nat.add 5 (j - 5) = j := by simp only [Nat.add_eq]; omega
    rwa [e] at h
  · have h := allN_spec te_bind2 (j - 10) (by omega)
    have e : Nat.add 10 (j - 10) = j := by simp only [Nat.add_eq]; omega
    rwa [e] at h

theorem te_row {j : ℕ} (hj : j < 15) : ∀ k < 22,
    row 22 (TGM j) k = (transposeRows 22 ((oddMats witRec).getD j []).toArray)[k]?.getD 0 := by
  intro k hk
  rw [← Nat.eq_of_beq_eq_true (allN_spec (allN_spec te_rows j hj) k hk)]
  exact (land_mask_eq_row M22_eq (TGM j) k).symm

theorem te_sRep {j : ℕ} (hj : j < 15) :
    MatRep.Rep 22 co2PackedVecs (unpack 2300 12 (Co2E.S j)) (TGM j) (TGMI j) :=
  rep_unpack (te_bind hj)

theorem te_hpt : ∀ j < 2300, (co2PosTable[co2PackedVecs[j]!]!).toNat = j := by
  intro j hj
  unfold co2PosTable
  exact posTable_get good.nodup good.lt (by rw [V_size]; norm_num) (by rw [V_size]; exact hj)

theorem te_gA_get {j : ℕ} (hj : j < 15) :
    (gArrsOf co2PosTable witRec)[j]! = unpack 2300 12 (Co2E.S j) := by
  have e : (gArrsOf co2PosTable witRec)[j]! = matPerm co2PosTable ((oddMats witRec).getD j []) := by
    unfold gArrsOf
    rw [getElem!_pos _ j (by simp [te_facts.1]; omega),
      List.getD_eq_getElem _ _ (by rw [te_facts.1]; omega)]
    simp
  rw [e]
  exact matPerm_eq te_hpt (te_row hj) (te_sRep hj) (by simp [unpack])

theorem te_gRep : RepT 22 co2PackedVecs (gArrsOf co2PosTable witRec) teGT := by
  refine ⟨by rw [te_gA_size, te_gT_len], fun k hk => ?_⟩
  rw [te_gT_len] at hk
  rw [te_gT_get hk, te_gA_get hk]
  exact te_sRep hk

theorem te_uRep : MatRep.Rep 22 co2PackedVecs uArr teU.1 teU.2 := uRep

theorem te_gens : allLt 15 (fun i =>
    isInvA 2300 (gArrsOf co2PosTable witRec)[i]! (invCand 2300 (gArrsOf co2PosTable witRec)[i]!) &&
      allLt 2300 (fun k => co2PackedVecs[((gArrsOf co2PosTable witRec)[i]!)[k]!]! ==
        vecMulN 22 (transposeRows 22 ((oddMats witRec).getD i []).toArray) co2PackedVecs[k]!) &&
      siftA 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr 0
        (gArrsOf co2PosTable witRec)[i]! &&
      eqA 2300 (compA 2300 (gArrsOf co2PosTable witRec)[i]! uArr)
        (compA 2300 uArr (gArrsOf co2PosTable witRec)[i]!)) = true := by
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  have hr : MatRep.Rep 22 co2PackedVecs (gArrsOf co2PosTable witRec)[i]! (TGM i) (TGMI i) := by
    rw [te_gA_get hi]
    exact te_sRep hi
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨isInvA_rep hr, ?_⟩, ?_⟩, ?_⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    have hg := get_rep hr (i := k) (by rw [V_size]; exact hk)
    rw [hg.2, vecMulN_eq_vmul (te_row hi)]
    exact beq_self_eq_true _
  · rw [te_gA_get hi]
    exact siftK_sound CertificateChecks.KernelSpor.Co2A.binds CertificateChecks.KernelSpor.Co2A.perm
      CertificateChecks.KernelSpor.Co2A.hl rfl (range_of_bindK (te_bind hi))
      (allN_spec te_sift i hi)
  · have h1 := rep_cmp (p := (TGM i, TGMI i)) (q := teU) hr te_uRep
    have h2 := rep_cmp (p := teU) (q := (TGM i, TGMI i)) te_uRep hr
    have hc := Nat.eq_of_beq_eq_true (allN_spec te_comm i hi)
    rw [te_gT_get hi] at hc
    exact eqA_of_mat h1 h2 hc

theorem te_eS_bind : (extendArrs (gArrsOf co2PosTable witRec) eDerivs).size = 26 ∧
    ∀ j < 26, (extendArrs (gArrsOf co2PosTable witRec) eDerivs)[j]! = unpack 2300 12 (Co2E.S j) := by
  rw [CFSG.KS.Co2ThirdE.extendArrs_eq]
  exact strongOf_bind ⟨te_gA_size, fun j hj => te_gA_get hj⟩ Co2E.head

theorem te_eR_strong : (eRecOf (gArrsOf co2PosTable witRec) witRec).strongArrs =
    extendArrs (gArrsOf co2PosTable witRec) eDerivs := by
  unfold eRecOf ChainRecord.strongArrs
  simp only [List.map_map]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp

theorem te_eBaseOK : (Nat.beq witRec.third.baseIndices.toArray.size 13 &&
    allN 13 fun t => Nat.beq witRec.third.baseIndices.toArray[t]! (pg 12 (mask 12) Co2E.BP t)) =
    true := by
  quickRfl

theorem te_eBinds : Binds 2300 12 Co2E.S 26 13 Co2E.BP
    (eRecOf (gArrsOf co2PosTable witRec) witRec).strongArrs
    (eRecOf (gArrsOf co2PosTable witRec) witRec).baseArr := by
  have hb := te_eBaseOK
  rw [Bool.and_eq_true] at hb
  rw [te_eR_strong]
  exact ⟨by norm_num, by norm_num, by norm_num, te_eS_bind.1, te_eS_bind.2,
    Nat.eq_of_beq_eq_true hb.1, fun t ht => Nat.eq_of_beq_eq_true (allN_spec hb.2 t ht)⟩

theorem te_eR_gens : (eRecOf (gArrsOf co2PosTable witRec) witRec).generators =
    (eRecOf (gArrsOf co2PosTable witRec) witRec).strongGenerators.take 15 := by
  change (gArrsOf co2PosTable witRec).toList.map Array.toList =
    ((extendArrs (gArrsOf co2PosTable witRec) eDerivs).toList.map Array.toList).take 15
  rw [← List.map_take, ← te_gA_size]
  exact congrArg (List.map Array.toList)
    (CFSG.KS.Co2ThirdE.extendArrsN_take 2300 (gArrsOf co2PosTable witRec) eDerivs).symm

theorem te_eR_glen : (eRecOf (gArrsOf co2PosTable witRec) witRec).generators.length = 15 := by
  change ((gArrsOf co2PosTable witRec).toList.map Array.toList).length = 15
  simp [te_gA_size]

theorem te_eR_dlen : (eRecOf (gArrsOf co2PosTable witRec) witRec).derivations.length + 15 = 26 := by
  change eDerivs.length + 15 = 26
  rw [te_facts.2.2.1]

theorem te_eRecord : recordOK 2300 (eRecOf (gArrsOf co2PosTable witRec) witRec) 4 = true :=
  recordOK_of (NS := 288) (CH := 8) te_eR_gens te_eR_glen te_eR_dlen te_eBinds Co2E.head Co2E.hl
    (by norm_num) Co2E.hs

theorem te_eOrbits : recordOrbits 2300 (eRecOf (gArrsOf co2PosTable witRec) witRec) =
    [20, 18, 32, 8, 4, 1, 2, 1, 1, 1, 1, 1, 2] := by
  rw [recordOrbits_of te_eBinds Co2E.perm Co2E.hl]
  decide +kernel

theorem te_eShape : chainShapeOK (eRecOf (gArrsOf co2PosTable witRec) witRec) 2300 15 26
    witRec.third.baseIndices = true := by
  have hstrong := te_eS_bind
  unfold chainShapeOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨rfl, te_eR_glen⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, rfl⟩, ?_⟩
  · change ((extendArrs (gArrsOf co2PosTable witRec) eDerivs).toList.map Array.toList).length = 26
    simp [hstrong.1]
  · change eDerivs.length = 26 - 15
    rw [te_facts.2.2.1]
  · change ((gArrsOf co2PosTable witRec).toList.map Array.toList).all (isPermList 2300) = true
    refine CFSG.KS.Co2ThirdE.all_isPermList fun j hj => ?_
    rw [te_gA_size] at hj
    rw [te_gA_get hj]
    have := allN_spec Co2E.perm j (by omega)
    exact CFSG.KS.Co2ThirdE.isPermList_unpack this
  · change ((extendArrs (gArrsOf co2PosTable witRec) eDerivs).toList.map Array.toList).all
      (isPermList 2300) = true
    refine CFSG.KS.Co2ThirdE.all_isPermList fun j hj => ?_
    rw [hstrong.1] at hj
    rw [hstrong.2 j hj]
    exact CFSG.KS.Co2ThirdE.isPermList_unpack (allN_spec Co2E.perm j hj)
  · exact te_facts.2.2.2.2.1

end CertificateChecks.KernelSporSch.Co2M

end
