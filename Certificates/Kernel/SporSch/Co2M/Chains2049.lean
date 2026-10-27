
module

public import Certificates.Kernel.SporSch.Co2M.Chains2049Base

public import Certificates.Kernel.SporSch.Co2M.Words
public import CFSG.Sporadic.Co2Schreier.ChainsBase
public import CFSG.Sporadic.Co2Schreier.OrbitZCheck
public import CFSG.Sporadic.Co2Schreier.OrbitTCheck
public import CFSG.Certificates.NativeSetOrbit
public import CFSG.Sporadic.Schreier.Co3Centralizers
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public import CFSG.LocalAnalysis.ComponentInitial.AutomorphismRealization
public import CFSG.Sporadic.Co2Schreier.OrbitCheck
public meta import CFSG.Sporadic.Co2Schreier.OrbitCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Mathieu CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem wfK : WordFacts := by
  have h := words_check
  simp only [wordsCheck, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', allLt_iff,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩

theorem repTupleK_a : RepTuple 2300 aArrs aSeeds := by
  refine ⟨aArrs_size, fun h hh => ?_⟩
  have hh2 : h < 2 := hh
  have ea : aArrs = co2OrigArrs := rfl
  have e0 : aSeeds.getD 0 1 = co2Gen 0 := List.getD_cons_zero
  have e1 : aSeeds.getD 1 1 = co2Gen 1 := List.getD_cons_succ.trans List.getD_cons_zero
  rw [ea]
  interval_cases h
  · rw [e0]
    exact rep_co2Gen (by norm_num)
  · rw [e1]
    exact rep_co2Gen (by norm_num)

theorem repTupleK_cInit :
    RepTuple 2300 cInitArrs cInitTuple :=
  repTupleK_a.mapWords wfK.invA localShape.cInit_letters

theorem repTupleK_d :
    RepTuple 2300 dArrs dTuple :=
  repTupleK_a.mapWords wfK.invA localShape.dWords_letters

theorem repTupleK_dStar :
    RepTuple 2300 dStarArrs dStarTuple :=
  repTupleK_d.extend (by rw [dTuple_length]; exact localShape.dDeriv_letters) wfK.invDStar

theorem repTupleK_r :
    RepTuple 2300 rArrs rTuple :=
  repTupleK_dStar.mapWords wfK.invDStar (by rw [dStarTuple_length]; exact
    localShape.rWords_letters)

theorem repK_z0 :
    Rep 2300 z0Arr locZ0 :=
  repTupleK_cInit.word wfK.invCInit (by rw [cInitTuple_length]; exact localShape.z0_letters)

theorem repK_t :
    Rep 2300 tArr locT :=
  repTupleK_d.word wfK.invD (by rw [dTuple_length]; exact localShape.t_letters)

theorem repK_z :
    Rep 2300 zArr locZ :=
  repTupleK_r.word wfK.invR (by rw [rTuple_length]; exact localShape.z_letters)

theorem repK_w :
    Rep 2300 wArr locW :=
  repTupleK_a.word wfK.invA localShape.w_letters

theorem repK_x :
    Rep 2300 xArr locX :=
  rep_compA (rep_compA repK_w repK_z0) (rep_inv_of_isInvA repK_w wfK.invW)

theorem repK_h :
    Rep 2300 hArr locH :=
  rep_compA (rep_powArr (rep_compA repK_x repK_z) _) (rep_powArr (rep_compA repK_z0 repK_x) _)

theorem repTupleK_c :
    RepTuple 2300 cArrs cTuple :=
  repTupleK_cInit.conj repK_h wfK.invH

theorem rep_aArrs_genK :
    ∀ k < aArrs.size, Rep 2300 aArrs[k]! (co2Gen k) := by
  intro k hk
  rw [aArrs_size] at hk
  exact rep_co2Gen hk

theorem co2Gen_mem_PK : ∀ k < aArrs.size, co2Gen k ∈ co2P := by
  intro k hk
  rw [aArrs_size] at hk
  interval_cases k
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem le_ncard_orbitK {g : Equiv.Perm (Fin 2300)}
    {t : Array ℕ} (ht : Rep 2300 t g) {bound : ℕ} {O : Array (List ℕ) × Array ℕ × Array ℕ}
    (h : orbitRecordOK (fixedList 2300 t) bound O = true) :
    bound ≤ (Set.range fun x : co2P => x • {p : Fin 2300 | g p = p}).ncard := by
  simp only [orbitRecordOK, Bool.and_eq_true, beq_iff_eq] at h
  have key := le_ncard_orbit_of_translatesOK (H := co2P) rep_aArrs_genK co2Gen_mem_PK
    (pointList_fixedList t) h.1.1 (CFSG.Sporadic.Schreier.Co3.keysSortedOK_nodup h.1.2)
  rw [h.2, finSet_fixedList ht] at key
  exact key

theorem closureC_le :
    Subgroup.closure (Set.range fun j : Fin 2 =>
      permOfArr 2300 localRec.chains.C.strongArrs[j.val]!) ≤
      co2P ⊓ Subgroup.centralizer {locZ} := by
  rw [Subgroup.closure_le, Set.range_subset_iff]
  intro j
  have hk := j.isLt
  have hk' : j.val < cTuple.length := by rw [cTuple_length]; exact hk
  rw [permK_eq Co2LC.binds (by omega) (MatRep.repT_get cRep (by rw [cT_len]; exact hk))
    (allN_spec orig_c j.val hk) (repTupleK_c.rep hk')]
  refine ⟨cTuple_mem _ (getD_memK hk'), ?_⟩
  change cTuple.getD j.val 1 ∈ Subgroup.centralizer {locZ}
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (commA_iff (repTupleK_c.rep hk') repK_z).1 (wfK.commZ j.val hk)

theorem closureD_le :
    Subgroup.closure (Set.range fun j : Fin 2 =>
      permOfArr 2300 localRec.chains.D.strongArrs[j.val]!) ≤
      co2P ⊓ Subgroup.centralizer {locT} := by
  rw [Subgroup.closure_le, Set.range_subset_iff]
  intro j
  have hk := j.isLt
  have hk' : j.val < dTuple.length := by rw [dTuple_length]; exact hk
  rw [permK_eq Co2LD.binds (by omega) (MatRep.repT_get dRep (by rw [dT_len]; exact hk))
    (allN_spec orig_d j.val hk) (repTupleK_d.rep hk')]
  refine ⟨dTuple_mem _ (getD_memK hk'), ?_⟩
  change dTuple.getD j.val 1 ∈ Subgroup.centralizer {locT}
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (commA_iff (repTupleK_d.rep hk') repK_t).1 (wfK.commT j.val hk)

theorem closureJ_le :
    Subgroup.closure (Set.range fun j : Fin 4 =>
      permOfArr 2300 localRec.chains.join.strongArrs[j.val]!) ≤ co2P := by
  rw [Subgroup.closure_le, Set.range_subset_iff]
  intro j
  have hk := j.isLt
  have hl : (cTuple ++ dTuple).length = 4 := by
    rw [List.length_append, cTuple_length, dTuple_length]
  have hk' : j.val < (cTuple ++ dTuple).length := by rw [hl]; exact hk
  have hT : (cT ++ dT).length = 4 := by rw [List.length_append, cT_len, dT_len]
  rw [permK_eq Co2LJ.binds (by omega)
    (MatRep.repT_get (MatRep.repT_append cRep dRep) (by rw [hT]; exact hk))
    (allN_spec orig_j j.val hk) ((repTupleK_c.append repTupleK_d).rep hk')]
  rcases List.mem_append.1 (getD_memK hk') with h | h
  · exact cTuple_mem _ h
  · exact dTuple_mem _ h

theorem chainC_ok :
    recordOK 2300 localRec.chains.C 4 = true ∧
      recordOrbits 2300 localRec.chains.C = [256, 1260, 18, 32, 2, 2] := by
  refine ⟨recordOK_of_cardK (NS := 9) (CH := 256) Co2LC.shapeOK.2.2.2.1 Co2LC.shapeOK.2.1
    (by rw [Co2LC.shapeOK.2.2.1]) Co2LC.binds Co2LC.head Co2LC.ho (by norm_num) ?_,
    Co2LC.orbits_ok⟩
  rw [Co2LC.orbits_ok]
  have h := card_mul_leK locZ_mem closureC_le (le_ncard_orbitK repK_z orbitZ_check)
  have e : [256, 1260, 18, 32, 2, 2].prod = 743178240 := by norm_num
  rw [e]
  exact Nat.le_of_mul_le_mul_right (h.trans (by norm_num)) (by norm_num : 0 < 56925)

theorem chainD_ok :
    recordOK 2300 localRec.chains.D 4 = true ∧
      recordOrbits 2300 localRec.chains.D = [1920, 56, 96, 4] := by
  refine ⟨recordOK_of_cardK (NS := 9) (CH := 256) Co2LD.shapeOK.2.2.2.1 Co2LD.shapeOK.2.1
    (by rw [Co2LD.shapeOK.2.2.1]) Co2LD.binds Co2LD.head Co2LD.ho (by norm_num) ?_,
    Co2LD.orbits_ok⟩
  rw [Co2LD.orbits_ok]
  have h := card_mul_leK locT_mem closureD_le (le_ncard_orbitK repK_t orbitT_check)
  have e : [1920, 56, 96, 4].prod = 41287680 := by norm_num
  rw [e]
  exact Nat.le_of_mul_le_mul_right (h.trans (by norm_num)) (by norm_num : 0 < 1024650)

theorem chainJ_ok :
    recordOK 2300 localRec.chains.join 4 = true ∧
      recordOrbits 2300 localRec.chains.join = [2300, 1408, 567, 192, 10, 12] := by
  refine ⟨recordOK_of_cardK (NS := 9) (CH := 256) Co2LJ.shapeOK.2.2.2.1 Co2LJ.shapeOK.2.1
    (by rw [Co2LJ.shapeOK.2.2.1]) Co2LJ.binds Co2LJ.head Co2LJ.ho (by norm_num) ?_,
    Co2LJ.orbits_ok⟩
  rw [Co2LJ.orbits_ok]
  have h := Subgroup.card_le_of_le closureJ_le
  rw [card_co2P] at h
  have e : [2300, 1408, 567, 192, 10, 12].prod = 42305421312000 := by norm_num
  rw [e]
  exact h

theorem facts2049 :
    (recordOK 2300 localRec.chains.C 4 = true ∧
      recordOrbits 2300 localRec.chains.C = [256, 1260, 18, 32, 2, 2])
    ∧ (recordOK 2300 localRec.chains.D 4 = true ∧
      recordOrbits 2300 localRec.chains.D = [1920, 56, 96, 4])
    ∧ (recordOK 2300 localRec.chains.S 4 = true ∧
      recordOrbits 2300 localRec.chains.S = [256, 256, 4])
    ∧ (recordOK 2300 localRec.chains.join 4 = true ∧
      recordOrbits 2300 localRec.chains.join = [2300, 1408, 567, 192, 10, 12])
    ∧ (wordsCheck localRec levelsS = true) :=
  ⟨chainC_ok, chainD_ok, ⟨Co2LS.record_ok, Co2LS.orbits_ok⟩, chainJ_ok, words_check⟩

end CertificateChecks.KernelSporSch.Co2M

end
