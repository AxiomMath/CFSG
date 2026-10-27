module

public import Certificates.Kernel.Sporadic.Co2.ChainA
public import Certificates.Kernel.Sporadic.Co2.ChainC
public import Certificates.Kernel.Sporadic.Co2.Card
public import CFSG.Certificates.Kernel.Spor.RawCard
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CentralizerPresented
public import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Sporadic.Presentation.Common

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co2Order

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Mathieu

theorem gens_take : co2Rec.chain.generators = co2Rec.chain.strongGenerators.take 2 := by
  decide +kernel

theorem cgens_take :
    co2Rec.coprimeChain.generators = co2Rec.coprimeChain.strongGenerators.take 2 := by
  decide +kernel

theorem lens : co2Rec.chain.generators.length = 2 ∧ co2Rec.chain.derivations.length = 9 ∧
    co2Rec.coprimeChain.generators.length = 2 ∧ co2Rec.coprimeChain.derivations.length = 15 := by
  decide +kernel

theorem extract_toArray (L : List (List Nat)) :
    ((L.map List.toArray).toArray.extract 0 2) = ((L.take 2).map List.toArray).toArray := by
  rw [List.extract_toArray]
  simp [List.extract_eq_drop_take, List.map_take]

theorem orig_eq : co2OrigArrs = co2StrongArrs.extract 0 2 := by
  unfold co2OrigArrs co2StrongArrs ChainRecord.origArrs ChainRecord.strongArrs
  rw [extract_toArray, gens_take]

theorem corig_eq : co2cOrigArrs = co2cStrongArrs.extract 0 2 := by
  unfold co2cOrigArrs co2cStrongArrs ChainRecord.origArrs ChainRecord.strongArrs
  rw [extract_toArray, cgens_take]

theorem wordArrs_eq (c : ChainRecord) {s : Nat} (hg : c.generators.length = 2)
    (hd : c.derivations.length + 2 = s) :
    c.wordArrs = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 s c.derivations := by
  unfold ChainRecord.wordArrs CFSG.Sporadic.Schreier.Co3.Native.wordsArr
  apply Array.ext
  · simp [hg]
    omega
  · intro i h1 h2
    simp only [List.getElem_toArray, Array.getElem_ofFn]
    by_cases hi : i < 2
    · rw [if_pos hi, List.getElem_append_left (by simp [hg]; omega)]
      simp
    · have hlt : i - 2 < c.derivations.length := by simp [hg] at h1; omega
      rw [if_neg hi, List.getElem_append_right (by simp [hg]; omega),
        List.getD_eq_getElem _ _ hlt]
      simp only [List.length_replicate, hg]

theorem words_eq : co2WordArrs = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 11
    CertificateChecks.KernelSpor.Co2.derivA :=
  wordArrs_eq _ lens.1 (by rw [lens.2.1])

theorem cwords_eq : co2cWordArrs = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 17
    CertificateChecks.KernelSpor.Co2.derivC :=
  wordArrs_eq _ lens.2.2.1 (by rw [lens.2.2.2])

@[expose] noncomputable def Wp : Nat :=
  pcomp 2300 12 (mask 12) (Co2A.SI 0) (pcomp 2300 12 (mask 12) (Co2A.S 1)
    (pcomp 2300 12 (mask 12) (Co2A.S 1) (pcomp 2300 12 (mask 12) (Co2A.S 0)
      (pcomp 2300 12 (mask 12) (Co2A.S 1) (Co2A.SI 0)))))

@[expose] noncomputable def Pp : Nat := pcomp 2300 12 (mask 12) (Co2C.S 0) (Co2C.S 1)

theorem canonOK : bAnd(canonK 2300 12 (mask 12) (2300 * 12) (Co2A.S 0),
    bAnd(canonK 2300 12 (mask 12) (2300 * 12) (Co2A.S 1),
    bAnd(canonK 2300 12 (mask 12) (2300 * 12) (Co2A.SI 0),
    bAnd(canonK 2300 12 (mask 12) (2300 * 12) (Co2C.S 0),
    bAnd(canonK 2300 12 (mask 12) (2300 * 12) (Co2C.S 1),
    bAnd(canonK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12),
    bAnd(idK 2300 12 (mask 12),
    bAnd(permOK 2300 12 (mask 12) (2300 * 12) Wp (pinvS 2300 12 (mask 12) Wp),
    canonK 2300 12 (mask 12) (2300 * 12) (pinvS 2300 12 (mask 12) Wp))))))))) = true := by
  quickRfl

theorem eqOK0 : Nat.beq (Co2C.S 0) (Co2A.S 0) = true := by
  quickRfl

theorem eqOK1 : Nat.beq (Co2C.S 1) (pcomp 2300 12 (mask 12) (pinvS 2300 12 (mask 12) Wp)
      (pcomp 2300 12 (mask 12) (Co2A.S 1) Wp)) = true := by
  quickRfl

theorem powOK : bAnd(Nat.beq (CFSG.KS.ppow 2300 12 (mask 12) (pidn 2300 12) (Co2C.S 0) 2) (pidn 2300 12),
    bAnd(bIf(Nat.beq (Co2C.S 0) (pidn 2300 12), false, true),
    bAnd(Nat.beq (CFSG.KS.ppow 2300 12 (mask 12) (pidn 2300 12) (Co2C.S 1) 5) (pidn 2300 12),
    bAnd(bIf(Nat.beq (Co2C.S 1) (pidn 2300 12), false, true),
    bAnd(Nat.beq (CFSG.KS.ppow 2300 12 (mask 12) (pidn 2300 12) Pp 23) (pidn 2300 12),
    bAnd(bIf(Nat.beq Pp (pidn 2300 12), false, true),
      canonK 2300 12 (mask 12) (2300 * 12) Pp)))))) = true := by
  quickRfl

theorem get_extract {S : Array (Array Nat)} {k : Nat} (hk : k < 2) (hS : 2 ≤ S.size) :
    (S.extract 0 2)[k]! = S[k]! := by
  rw [getElem!_pos _ k (by simp; omega), Array.getElem_extract, getElem!_pos S k (by omega)]
  simp

theorem a_eq (k : Nat) (hk : k < 2) : co2OrigArrs[k]! = unpack 2300 12 (Co2A.S k) := by
  rw [orig_eq, get_extract hk (by rw [Co2A.binds.2.2.2.1]; omega)]
  exact Co2A.binds.2.2.2.2.1 k (by omega)

theorem c_eq (k : Nat) (hk : k < 2) : co2cOrigArrs[k]! = unpack 2300 12 (Co2C.S k) := by
  rw [corig_eq, get_extract hk (by rw [Co2C.binds.2.2.2.1]; omega)]
  exact Co2C.binds.2.2.2.2.1 k (by omega)

theorem canon : canonK 2300 12 (mask 12) (2300 * 12) (Co2A.S 0) = true ∧
    canonK 2300 12 (mask 12) (2300 * 12) (Co2A.S 1) = true ∧
    canonK 2300 12 (mask 12) (2300 * 12) (Co2A.SI 0) = true ∧
    canonK 2300 12 (mask 12) (2300 * 12) (Co2C.S 0) = true ∧
    canonK 2300 12 (mask 12) (2300 * 12) (Co2C.S 1) = true ∧
    canonK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) = true ∧ idK 2300 12 (mask 12) = true ∧
    permOK 2300 12 (mask 12) (2300 * 12) Wp (pinvS 2300 12 (mask 12) Wp) = true ∧
    canonK 2300 12 (mask 12) (2300 * 12) (pinvS 2300 12 (mask 12) Wp) = true := by
  simpa only [bAnd_iff] using canonOK

theorem inv0 : invCand 2300 (unpack 2300 12 (Co2A.S 0)) = unpack 2300 12 (Co2A.SI 0) :=
  (invEqK_sound (allN_spec Co2A.perm 0 (by norm_num))).1

theorem w_eq : co2WArr = unpack 2300 12 Wp := by
  obtain ⟨c0, c1, cI0, -⟩ := canon
  unfold co2WArr Wp
  rw [a_eq 0 (by norm_num), a_eq 1 (by norm_num), inv0, compA_unpack c1 cI0,
    compA_unpack c0 (canonK_pcomp c1 cI0), compA_unpack c1 (canonK_pcomp c0 (canonK_pcomp c1 cI0)),
    compA_unpack c1 (canonK_pcomp c1 (canonK_pcomp c0 (canonK_pcomp c1 cI0))),
    compA_unpack cI0 (canonK_pcomp c1 (canonK_pcomp c1 (canonK_pcomp c0 (canonK_pcomp c1 cI0))))]

theorem idA_eq : idA 2300 = unpack 2300 12 (pidn 2300 12) := (idK_sound canon.2.2.2.2.2.2.1).symm

theorem wfacts : isInvA 2300 co2WArr (invCand 2300 co2WArr) = true ∧
    invCand 2300 co2WArr = unpack 2300 12 (pinvS 2300 12 (mask 12) Wp) := by
  rw [w_eq, invCand_unpack canon.2.2.2.2.2.2.2.1]
  exact ⟨(invEqK_sound canon.2.2.2.2.2.2.2.1).2, rfl⟩

theorem c0_eq : Co2C.S 0 = Co2A.S 0 := Nat.eq_of_beq_eq_true eqOK0

theorem c1_eq : Co2C.S 1 = pcomp 2300 12 (mask 12) (pinvS 2300 12 (mask 12) Wp)
    (pcomp 2300 12 (mask 12) (Co2A.S 1) Wp) := Nat.eq_of_beq_eq_true eqOK1

theorem powArr_eq (n : Nat) (t : Array Nat) : ∀ e, powArr n t e = CFSG.Sporadic.Schreier.Co3.co3PowA n t e
  | 0 => rfl
  | e + 1 => by
    rw [powArr, CFSG.Sporadic.Schreier.Co3.co3PowA, powArr_eq n t e]

theorem pow_id {P e : Nat} (hP : canonK 2300 12 (mask 12) (2300 * 12) P = true)
    (h : Nat.beq (CFSG.KS.ppow 2300 12 (mask 12) (pidn 2300 12) P e) (pidn 2300 12) = true) :
    eqA 2300 (powArr 2300 (unpack 2300 12 P) e) (idA 2300) = true := by
  rw [powArr_eq, powEqK_sound (r := pidn 2300 12) ((bAnd_iff _ _).2 ⟨hP, h⟩), idA_eq,
    eqA_unpack canon.2.2.2.2.2.1 canon.2.2.2.2.2.1, Nat.beq_refl]

theorem ne_id {P : Nat} (hP : canonK 2300 12 (mask 12) (2300 * 12) P = true)
    (h : bIf(Nat.beq P (pidn 2300 12), false, true) = true) :
    eqA 2300 (unpack 2300 12 P) (idA 2300) = false := by
  rw [idA_eq]
  exact neK_sound ((bAnd_iff _ _).2 ⟨hP, (bAnd_iff _ _).2 ⟨canon.2.2.2.2.2.1, h⟩⟩)

theorem prod_eq : co2cProdArr = unpack 2300 12 Pp := by
  unfold co2cProdArr Pp
  rw [c_eq 0 (by norm_num), c_eq 1 (by norm_num), compA_unpack canon.2.2.2.1 canon.2.2.2.2.1]

theorem words_facts : isInvA 2300 co2WArr (invCand 2300 co2WArr) = true ∧
       eqA 2300 co2cOrigArrs[0]! co2OrigArrs[0]! = true ∧
       eqA 2300 co2cOrigArrs[1]!
         (compA 2300 (invCand 2300 co2WArr) (compA 2300 co2OrigArrs[1]! co2WArr)) = true ∧
       eqA 2300 (powArr 2300 co2cOrigArrs[0]! 2) (idA 2300) = true ∧
       eqA 2300 co2cOrigArrs[0]! (idA 2300) = false ∧
       eqA 2300 (powArr 2300 co2cOrigArrs[1]! 5) (idA 2300) = true ∧
       eqA 2300 co2cOrigArrs[1]! (idA 2300) = false ∧
       eqA 2300 (powArr 2300 co2cProdArr 23) (idA 2300) = true ∧
       eqA 2300 co2cProdArr (idA 2300) = false := by
  obtain ⟨cA0, cA1, cI0, cC0, cC1, cid, -, pW, cWI⟩ := canon
  obtain ⟨p1, n1, p2, n2, p3, n3, cP⟩ := (by simpa only [bAnd_iff] using powOK :
    Nat.beq (CFSG.KS.ppow 2300 12 (mask 12) (pidn 2300 12) (Co2C.S 0) 2) (pidn 2300 12) = true ∧
    bIf(Nat.beq (Co2C.S 0) (pidn 2300 12), false, true) = true ∧
    Nat.beq (CFSG.KS.ppow 2300 12 (mask 12) (pidn 2300 12) (Co2C.S 1) 5) (pidn 2300 12) = true ∧
    bIf(Nat.beq (Co2C.S 1) (pidn 2300 12), false, true) = true ∧
    Nat.beq (CFSG.KS.ppow 2300 12 (mask 12) (pidn 2300 12) Pp 23) (pidn 2300 12) = true ∧
    bIf(Nat.beq Pp (pidn 2300 12), false, true) = true ∧
    canonK 2300 12 (mask 12) (2300 * 12) Pp = true)
  have cW : canonK 2300 12 (mask 12) (2300 * 12) Wp = true := by
    unfold Wp
    exact canonK_pcomp cI0 (canonK_pcomp cA1 (canonK_pcomp cA1 (canonK_pcomp cA0
      (canonK_pcomp cA1 cI0))))
  refine ⟨wfacts.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c_eq 0 (by norm_num), a_eq 0 (by norm_num), eqA_unpack cC0 cA0, c0_eq, Nat.beq_refl]
  · rw [c_eq 1 (by norm_num), a_eq 1 (by norm_num), wfacts.2, w_eq, compA_unpack cA1 cW,
      compA_unpack cWI (canonK_pcomp cA1 cW), eqA_unpack cC1 (canonK_pcomp cWI (canonK_pcomp cA1 cW)),
      c1_eq, Nat.beq_refl]
  · rw [c_eq 0 (by norm_num)]
    exact pow_id cC0 p1
  · rw [c_eq 0 (by norm_num)]
    exact ne_id cC0 n1
  · rw [c_eq 1 (by norm_num)]
    exact pow_id cC1 p2
  · rw [c_eq 1 (by norm_num)]
    exact ne_id cC1 n2
  · rw [prod_eq]
    exact pow_id cP p3
  · rw [prod_eq]
    exact ne_id cP n3

theorem orbitsA : rawOrbitSizes 2300 co2StrongArrs co2BaseArr = [2300, 1408, 567, 192, 30, 4] := by
  rw [rawOrbitSizesK_sound Co2A.binds Co2A.perm Co2A.hl]
  decide

theorem orbitsC : rawOrbitSizes 2300 co2cStrongArrs co2cBaseArr = [2300, 1408, 567, 192, 30, 4] := by
  rw [rawOrbitSizesK_orb Co2C.binds Co2C.perm Co2C.ho (by norm_num)]
  decide

theorem sA (k : Nat) (hk : k < 2) : co2StrongArrs[k]! = co2OrigArrs[k]! := by
  rw [orig_eq, get_extract hk (by rw [Co2A.binds.2.2.2.1]; omega)]

theorem sC (k : Nat) (hk : k < 2) : co2cStrongArrs[k]! = co2cOrigArrs[k]! := by
  rw [corig_eq, get_extract hk (by rw [Co2C.binds.2.2.2.1]; omega)]

theorem range_two (f : Nat → Equiv.Perm (Fin 2300)) :
    (Set.range fun j : Fin 2 => f j.val) = {f 0, f 1} := by
  ext g
  simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff,
    Fin.val_zero, Fin.val_one]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm

theorem closureA : Subgroup.closure (Set.range fun j : Fin 2 => permOfArr 2300 co2StrongArrs[j.val]!) =
    co2P := by
  rw [range_two (fun j => permOfArr 2300 co2StrongArrs[j]!), sA 0 (by norm_num), sA 1 (by norm_num)]
  rfl

theorem rep_unpack {P Q : Nat} (h : permOK 2300 12 (mask 12) (2300 * 12) P Q = true) :
    Rep 2300 (unpack 2300 12 P) (permOfArr 2300 (unpack 2300 12 P)) ∧
      Rep 2300 (unpack 2300 12 Q) (permOfArr 2300 (unpack 2300 12 P))⁻¹ :=
  rep_permOfArr (invEqK_sound h).2

theorem closureC_le :
    Subgroup.closure (Set.range fun j : Fin 2 => permOfArr 2300 co2cStrongArrs[j.val]!) ≤ co2P := by
  obtain ⟨cA0, cA1, cI0, cC0, cC1, cid, -, pW, cWI⟩ := canon
  have cW : canonK 2300 12 (mask 12) (2300 * 12) Wp = true := by
    unfold Wp
    exact canonK_pcomp cI0 (canonK_pcomp cA1 (canonK_pcomp cA1 (canonK_pcomp cA0
      (canonK_pcomp cA1 cI0))))
  rw [range_two (fun j => permOfArr 2300 co2cStrongArrs[j]!), Subgroup.closure_le]
  have g0 : co2Gen 0 ∈ co2P := Subgroup.subset_closure (Set.mem_insert _ _)
  have g1 : co2Gen 1 ∈ co2P := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have r0 := rep_unpack (allN_spec Co2A.perm 0 (by norm_num))
  have r1 := rep_unpack (allN_spec Co2A.perm 1 (by norm_num))
  have e0 : permOfArr 2300 (unpack 2300 12 (Co2A.S 0)) = co2Gen 0 := by
    rw [co2Gen, a_eq 0 (by norm_num)]
  have e1 : permOfArr 2300 (unpack 2300 12 (Co2A.S 1)) = co2Gen 1 := by
    rw [co2Gen, a_eq 1 (by norm_num)]
  rw [e0] at r0
  rw [e1] at r1
  set w := (co2Gen 0)⁻¹ * (co2Gen 1 * (co2Gen 1 * (co2Gen 0 * (co2Gen 1 * (co2Gen 0)⁻¹))))
  have rW : Rep 2300 (unpack 2300 12 Wp) w := by
    unfold Wp
    rw [← compA_unpack cI0 (canonK_pcomp cA1 (canonK_pcomp cA1 (canonK_pcomp cA0
        (canonK_pcomp cA1 cI0)))),
      ← compA_unpack cA1 (canonK_pcomp cA1 (canonK_pcomp cA0 (canonK_pcomp cA1 cI0))),
      ← compA_unpack cA1 (canonK_pcomp cA0 (canonK_pcomp cA1 cI0)),
      ← compA_unpack cA0 (canonK_pcomp cA1 cI0), ← compA_unpack cA1 cI0]
    exact rep_compA r0.2 (rep_compA r1.1 (rep_compA r1.1 (rep_compA r0.1 (rep_compA r1.1 r0.2))))
  have rWI : Rep 2300 (unpack 2300 12 (pinvS 2300 12 (mask 12) Wp)) w⁻¹ :=
    rep_inv_of_isInvA rW (invEqK_sound pW).2
  have hw : w ∈ co2P := co2P.mul_mem (co2P.inv_mem g0) (co2P.mul_mem g1 (co2P.mul_mem g1
    (co2P.mul_mem g0 (co2P.mul_mem g1 (co2P.inv_mem g0)))))
  rintro g (rfl | rfl)
  · rw [sC 0 (by norm_num), c_eq 0 (by norm_num), c0_eq, e0]
    exact g0
  · have rc := rep_unpack (allN_spec Co2C.perm 1 (by norm_num))
    have rc' : Rep 2300 (unpack 2300 12 (Co2C.S 1)) (w⁻¹ * (co2Gen 1 * w)) := by
      rw [c1_eq, ← compA_unpack cWI (canonK_pcomp cA1 cW), ← compA_unpack cA1 cW]
      exact rep_compA rWI (rep_compA r1.1 rW)
    rw [sC 1 (by norm_num), c_eq 1 (by norm_num), rc.1.unique rc']
    exact co2P.mul_mem (co2P.inv_mem hw) (co2P.mul_mem g1 hw)

theorem chains :
    (rawChainOK 2300 co2OrigArrs co2StrongArrs co2BaseArr co2WordArrs 4 = true ∧
       rawOrbitSizes 2300 co2StrongArrs co2BaseArr = [2300, 1408, 567, 192, 30, 4]) ∧
    (rawChainOK 2300 co2cOrigArrs co2cStrongArrs co2cBaseArr co2cWordArrs 4 = true ∧
       rawOrbitSizes 2300 co2cStrongArrs co2cBaseArr = [2300, 1408, 567, 192, 30, 4]) := by
  have hN := Co2Card.card_co2P_le
  refine ⟨⟨?_, orbitsA⟩, ⟨?_, orbitsC⟩⟩
  · rw [orig_eq, words_eq]
    refine rawChainK_of_card 4 Co2A.binds Co2A.head Co2A.hl ?_
    rw [closureA, orbitsA]
    exact hN.trans (by norm_num)
  · rw [corig_eq, cwords_eq]
    refine rawChainK_of_card_orb 4 Co2C.binds Co2C.head Co2C.ho (by norm_num) ?_
    rw [orbitsC]
    exact (Subgroup.card_le_of_le closureC_le).trans (hN.trans (by norm_num))

theorem facts :
    (rawChainOK 2300 co2OrigArrs co2StrongArrs co2BaseArr co2WordArrs 4 = true ∧
       rawOrbitSizes 2300 co2StrongArrs co2BaseArr = [2300, 1408, 567, 192, 30, 4])
    ∧ (rawChainOK 2300 co2cOrigArrs co2cStrongArrs co2cBaseArr co2cWordArrs 4 = true ∧
       rawOrbitSizes 2300 co2cStrongArrs co2cBaseArr = [2300, 1408, 567, 192, 30, 4])
    ∧ (isInvA 2300 co2WArr (invCand 2300 co2WArr) = true ∧
       eqA 2300 co2cOrigArrs[0]! co2OrigArrs[0]! = true ∧
       eqA 2300 co2cOrigArrs[1]!
         (compA 2300 (invCand 2300 co2WArr) (compA 2300 co2OrigArrs[1]! co2WArr)) = true ∧
       eqA 2300 (powArr 2300 co2cOrigArrs[0]! 2) (idA 2300) = true ∧
       eqA 2300 co2cOrigArrs[0]! (idA 2300) = false ∧
       eqA 2300 (powArr 2300 co2cOrigArrs[1]! 5) (idA 2300) = true ∧
       eqA 2300 co2cOrigArrs[1]! (idA 2300) = false ∧
       eqA 2300 (powArr 2300 co2cProdArr 23) (idA 2300) = true ∧
       eqA 2300 co2cProdArr (idA 2300) = false) :=
  ⟨chains.1, chains.2, words_facts⟩

end CertificateChecks.KernelSpor.Co2Order

end
