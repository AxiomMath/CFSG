module

public import Certificates.Kernel.SporSch.J1.Checks
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Sporadic.Bridge.J1
public import CFSG.Monster.B.Mathieu.ChainCheck
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Pres
open CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Mathieu CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

theorem strong_len : j1Chain.strongGenerators.length = 4 := rfl

theorem gen_len : j1Chain.generators.length = 2 := rfl

theorem strong_eq (j : Nat) (hj : j < 4) : j1Chain.strongArrs[j]! = unpack 3080 12 (J1C.S j) := by
  have h := toArray_eq_of_bindListK (allN_spec bindsOK j hj)
  unfold ChainRecord.strongArrs
  rw [getElem!_pos _ j (by simp [strong_len]; omega)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [← h, List.getD_eq_getElem _ _ (by rw [strong_len]; omega)]

theorem gen_eq (j : Nat) (hj : j < 2) : j1Chain.origArrs[j]! = unpack 3080 12 (J1C.S j) := by
  have h := toArray_eq_of_bindListK (allN_spec genOK j hj)
  unfold ChainRecord.origArrs
  rw [getElem!_pos _ j (by simp [gen_len]; omega)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [← h, List.getD_eq_getElem _ _ (by rw [gen_len]; omega)]

theorem binds : Binds 3080 12 J1C.S 4 3 J1C.BP j1Chain.strongArrs j1Chain.baseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [ChainRecord.strongArrs, strong_len],
    strong_eq, rfl, fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOK t ht)⟩

theorem orig_eq : j1Chain.origArrs = j1Chain.strongArrs.extract 0 2 := by
  apply Array.ext (by simp [ChainRecord.origArrs, ChainRecord.strongArrs, gen_len, strong_len])
  intro k h1 h2
  have hk : k < 2 := by simpa [ChainRecord.origArrs, gen_len] using h1
  rw [← getElem!_pos j1Chain.origArrs k h1, gen_eq k hk, Array.getElem_extract,
    ← getElem!_pos j1Chain.strongArrs (0 + k)
      (by simp [ChainRecord.strongArrs, strong_len]; omega), Nat.zero_add,
    strong_eq k (by omega)]

theorem words_eq : j1Chain.wordArrs = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 4 derivs := by
  unfold ChainRecord.wordArrs CFSG.Sporadic.Schreier.Co3.Native.wordsArr derivs
  apply Array.ext
  · simp [gen_len]
    rfl
  · intro i h1 h2
    simp only [List.getElem_toArray, Array.getElem_ofFn]
    have hd : j1Chain.derivations.length = 2 := rfl
    by_cases hi : i < 2
    · rw [ite_eq_left hi, List.getElem_append_left (by simp [gen_len]; omega)]
      simp
    · have hlt : i - 2 < j1Chain.derivations.length := by simp [gen_len] at h1; omega
      rw [ite_eq_right hi, List.getElem_append_right (by simp [gen_len]; omega),
        List.getD_eq_getElem _ _ hlt]
      simp only [List.length_replicate, gen_len]

@[expose] noncomputable def g (k : Nat) : Equiv.Perm (Fin 3080) :=
  permOfArr 3080 (unpack 3080 12 (J1C.S k))

theorem rep_g (k : Nat) (hk : k < 4) : Rep 3080 (unpack 3080 12 (J1C.S k)) (g k) ∧
    Rep 3080 (unpack 3080 12 (J1C.SI k)) (g k)⁻¹ :=
  rep_permOfArr (invEqK_sound (allN_spec perm k hk)).2

theorem rels_eq : TauCeti.Sporadic.j1Presentation.relatorLetters = rels := by
  rw [J1.relatorLetters_eq]
  simp only [rels, abW, repW, fifthW, squareW, J1.abWord, J1.repWord, J1.fifthBase, J1.squareBase]


theorem relators : ∀ v ∈ TauCeti.Sporadic.j1Presentation.relatorLetters,
    wordProd (img2 (g 0) (g 1)) v = 1 := by
  rw [rels_eq]
  have hi : ∀ i, img2 (g 0) (g 1) i = g (if i = 0 then 0 else 1) := by
    intro i
    unfold img2
    split <;> rfl
  have hGi : ∀ i, G i = J1C.S (if i = 0 then 0 else 1) ∧
      GI i = J1C.SI (if i = 0 then 0 else 1) := by
    intro i
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      exact ⟨rfl, rfl⟩
    · have hb : Nat.beq i 0 = false := by cases i with | zero => omega | succ k => rfl
      unfold G GI
      rw [hb, ite_eq_right_iff.2 (fun h => absurd h (by omega))]
      exact ⟨rfl, rfl⟩
  have hid := (bAnd_iff (canonK 3080 12 (mask 12) (3080 * 12) (pidn 3080 12))
    (idK 3080 12 (mask 12))).1 idOK
  refine relators_of_wordPK (G := G) (GI := GI) (fun i => ?_) (fun i => ?_) (fun i => ?_)
    hid.1 (idK_sound hid.2).symm relsOK
  · rw [hi, (hGi i).1]
    exact (rep_g _ (by split <;> omega)).1
  · rw [hi, (hGi i).2]
    exact (rep_g _ (by split <;> omega)).2
  · rw [(hGi i).1, (hGi i).2]
    exact (bAnd_iff _ _).1 (allN_spec canonOK _ (by split <;> omega))

theorem orbits : rawOrbitSizes 3080 j1Chain.strongArrs j1Chain.baseArr = [3080, 19, 3] := by
  rw [rawOrbitSizesK_orb binds perm J1C.ho (by norm_num)]
  decide

theorem range_two (f : Nat → Equiv.Perm (Fin 3080)) :
    (Set.range fun j : Fin 2 => f j.val) = {f 0, f 1} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff,
    Fin.val_zero, Fin.val_one]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm

theorem card_le :
    Nat.card (Subgroup.closure (Set.range fun j : Fin 2 =>
      permOfArr 3080 j1Chain.strongArrs[j.val]!)) ≤
      (rawOrbitSizes 3080 j1Chain.strongArrs j1Chain.baseArr).prod := by
  have hfin : Finite TauCeti.Sporadic.j1Presentation.Group := J1.finite_card_le.1
  rw [range_two (fun j => permOfArr 3080 j1Chain.strongArrs[j]!), strong_eq 0 (by norm_num),
    strong_eq 1 (by norm_num), orbits]
  exact (card_closure_le TauCeti.Sporadic.j1Presentation J1.generatorCount_eq relators).trans
    (J1.finite_card_le.2.trans (by norm_num))

set_option maxRecDepth 100000 in
theorem chain_eq : J1Certificate.chain = j1Chain := by
  delta J1Certificate j1CertLit
  rfl

theorem chainOK : rawChainOK 3080 j1Chain.origArrs j1Chain.strongArrs j1Chain.baseArr
    j1Chain.wordArrs 1 = true := by
  rw [orig_eq, words_eq]
  exact rawChainK_of_card_orb 1 binds J1C.head J1C.ho (by norm_num) card_le

theorem origInv (k : Nat) (hk : k < 2) :
    isInvA 3080 j1Chain.origArrs[k]! (invCand 3080 j1Chain.origArrs[k]!) = true := by
  have i := invEqK_sound (allN_spec perm k (by omega))
  rw [gen_eq k hk, i.1]
  exact i.2

theorem check : j1Chain.check 3080 = true := by
  have hsize : j1Chain.origArrs.size = 2 := rfl
  have hall : allLt j1Chain.origArrs.size
      (fun k => isInvA 3080 j1Chain.origArrs[k]! (invCand 3080 j1Chain.origArrs[k]!)) = true := by
    rw [hsize]
    simp only [allLt, Nat.all_succ, Nat.all_zero, Bool.true_and, Bool.and_eq_true]
    exact ⟨origInv 0 (by norm_num), origInv 1 (by norm_num)⟩
  unfold ChainRecord.check arraysOK
  rw [hall, chainOK]
  decide

theorem facts : (J1Certificate.chain.check 3080 = true)
    ∧ (J1Certificate.chain.base = [0, 1, 2])
    ∧ (J1Certificate.chain.orbitSizes 3080 = [3080, 19, 3]) := by
  rw [chain_eq]
  exact ⟨check, rfl, orbits⟩

end CertificateChecks.KernelSporSch.J1

end
