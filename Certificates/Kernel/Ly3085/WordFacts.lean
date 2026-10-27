
module

public import CFSG.Sporadic.Ly.WordFacts
public import CFSG.Certificates.Kernel.LyOmega.WordsSound
public import Certificates.Kernel.Ly3085.Omega.Data
public import Certificates.Kernel.SporSch.Ly.BSData
public import CFSG.Sporadic.Ly.PrimitiveBase
public import Certificates.Kernel.Ly3085.Words.Gen
import Certificates.Kernel.Ly3085.SeedFacts
import Certificates.Kernel.Ly3085.Bridge
import Certificates.Kernel.Ly3085.Words.Tw
import Certificates.Kernel.Ly3085.Words.HH
public import CFSG.Sporadic.HN.ConjSimple
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.FiveFacts
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.OrbitSpec
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.Ord
open CertificateChecks.KernelSporSch
open CFSG.Sporadic.Th (wordG)
open CFSG.Sporadic.Fi23 (slpG slpG_eq)

@[expose] noncomputable def matHom [LySeed] : J →* Matrix (Fin 111) (Fin 111) (ZMod 5) where
  toFun := mat
  map_one' := mat_one
  map_mul' := mat_mul

abbrev Rp [LySeed] (X : ℕ) (g : J) : Prop := LRep matHom X g

theorem rp_A [LySeed] : Rp LyBS.A a := ⟨cA, by rw [bigM_A]; rfl⟩

theorem rp_Ai [LySeed] : Rp LyBS.A a⁻¹ := by rw [a_inv]; exact rp_A

theorem rp_B [LySeed] : Rp LyBS.B b := ⟨cB, by rw [bigM_B]; rfl⟩

theorem rp_Bi [LySeed] : Rp LyBS.B4 b⁻¹ := by
  have e : b⁻¹ = b ^ 4 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact b_pow_five
  refine ⟨cB4, ?_⟩
  rw [bigM_B4, e, map_pow]
  rfl

theorem seedL_eq [LySeed] : seedL a b = seedLetter := by
  funext z
  unfold seedL seedLetter
  rfl

theorem vals_facts [LySeed] (ws : List (List ℤ)) :
    (slpVals CFSG.KD.LyOm.BC LyBS.A LyBS.B LyBS.B4 ws).length = ws.length ∧ ∀ i < ws.length,
      Rp ((slpVals CFSG.KD.LyOm.BC LyBS.A LyBS.B LyBS.B4 ws).getD i
          (CFSG.KD.LyOm.BC.ONEF, CFSG.KD.LyOm.BC.ONEF)).1 (slpG seedLetter ws.toArray i) ∧
        Rp ((slpVals CFSG.KD.LyOm.BC LyBS.A LyBS.B LyBS.B4 ws).getD i
          (CFSG.KD.LyOm.BC.ONEF, CFSG.KD.LyOm.BC.ONEF)).2 (slpG seedLetter ws.toArray i)⁻¹ := by
  have h := slpVals_hom hBC one_facts rp_A rp_Ai rp_B rp_Bi ws
  rw [seedL_eq] at h
  exact h

theorem eq_of_lanes [LySeed] {X Y : ℕ} {g h : J} (hX : Rp X g) (hY : Rp Y h)
    (e : Nat.beq X Y = true) : g = h := by
  have e1 := hX.eq
  have e2 := hY.eq
  rw [Nat.eq_of_beq_eq_true e, e2] at e1
  exact mat_injective e1.symm

theorem ne_of_lanes [LySeed] {X Y : ℕ} {g h : J} (hX : Rp X g) (hY : Rp Y h)
    (e : notB (Nat.beq X Y) = true) : g ≠ h := by
  intro hgh
  have hXY : X = Y := lcanon_eq hX.canon hY.canon (by rw [hX.eq, hY.eq, hgh])
  rw [hXY, Nat.beq_refl] at e
  exact absurd e (by decide)

theorem slpG_out [LySeed] (words : Array (List ℤ)) {i : ℕ} (hi : words.size ≤ i) :
    slpG seedLetter words i = 1 := by
  rw [slpG_eq, getElem!_neg words i (by omega)]
  rfl

theorem slpLetter_eq [LySeed] (words : Array (List ℤ)) :
    slpLetter words = relLetter seedLetter (slpG seedLetter words) := by
  funext z
  unfold slpLetter relLetter
  rfl

theorem relSide_facts [LySeed] (ws : List (List ℤ)) (w : List ℤ) :
    Rp (relLanes CFSG.KD.LyOm.BC LyBS.A LyBS.B LyBS.B4
        (slpVals CFSG.KD.LyOm.BC LyBS.A LyBS.B LyBS.B4 ws) w)
      (wordG (slpLetter ws.toArray) w) := by
  obtain ⟨hlen, hv⟩ := vals_facts ws
  have h := relLanes_hom hBC one_facts rp_A rp_Ai rp_B rp_Bi
    (slpVals CFSG.KD.LyOm.BC LyBS.A LyBS.B LyBS.B4 ws) (slpG seedLetter ws.toArray)
    (fun i hi => hv i (by omega)) (fun i hi => slpG_out _ (by simp; omega)) w
  rw [seedL_eq, ← slpLetter_eq] at h
  exact h

theorem rels_of_check [LySeed] (ws : List (List ℤ)) (rels : List (List ℤ × List ℤ))
    (h : relsOK CFSG.KD.LyOm.BC LyBS.A LyBS.B LyBS.B4
      (slpVals CFSG.KD.LyOm.BC LyBS.A LyBS.B LyBS.B4 ws) rels = true) :
    ∀ r ∈ rels, wordG (slpLetter ws.toArray) r.1 = wordG (slpLetter ws.toArray) r.2 := by
  intro r hr
  have := List.all_eq_true.1 h r hr
  exact eq_of_lanes (relSide_facts ws r.1) (relSide_facts ws r.2) this

theorem nes_of_check [LySeed] (ws : List (List ℤ)) (nes : List (List ℤ × List ℤ × ℕ))
    (h : nesOK CFSG.KD.LyOm.BC LyBS.A LyBS.B LyBS.B4
      (slpVals CFSG.KD.LyOm.BC LyBS.A LyBS.B LyBS.B4 ws) nes = true) :
    ∀ r ∈ nes, wordG (slpLetter ws.toArray) r.1 ≠ wordG (slpLetter ws.toArray) r.2.1 := by
  intro r hr
  have := List.all_eq_true.1 h r hr
  exact ne_of_lanes (relSide_facts ws r.1) (relSide_facts ws r.2.1) this

theorem twFacts [LySeed] : LyTwFacts := by
  have h := rels_of_check CFSG.Sporadic.Ly.TwoWeights.twWords.toList _ CFSG.KD.LyOm.tw_checks
  rw [Array.toArray_toList] at h
  exact h

theorem hhFacts [LySeed] : LyHHFacts := by
  refine ⟨?_, ?_⟩
  · have h := rels_of_check CFSG.Sporadic.Ly.HH.hhWords.toList _ CFSG.KD.LyOm.hh_rels_checks
    rw [Array.toArray_toList] at h
    exact h
  · have h := nes_of_check CFSG.Sporadic.Ly.HH.hhWords.toList _ CFSG.KD.LyOm.hh_nes_checks
    rw [Array.toArray_toList] at h
    exact h

theorem slpG_congr {G : Type*} [Group G] (s : ℤ → G) {ws ws' : Array (List ℤ)} :
    ∀ j, (∀ i ≤ j, ws[i]! = ws'[i]!) → slpG s ws j = slpG s ws' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [slpG_letG, slpG_letG, h j le_rfl]
    congr 1
    funext z
    unfold letG
    split_ifs with h1 h2 h3
    · rfl
    · rw [ih _ h2 fun i hi => h i (by omega)]
    · rw [ih _ h2 fun i hi => h i (by omega)]
    · rfl

theorem genExt_letters : ∀ j, 6 ≤ j → j < 13 → ∀ z ∈ CFSG.KD.LyOm.genExt.toArray[j]!,
    z.natAbs = 7 ∨ z.natAbs = 8 ∨ (9 ≤ z.natAbs ∧ z.natAbs - 3 < j) := by
  decide +kernel

theorem genExt_size : CFSG.KD.LyOm.genExt.toArray.size = 13 := by decide +kernel

theorem genExt_prefix : ∀ i ≤ 5, CFSG.KD.LyOm.genExt.toArray[i]! =
    CFSG.Sporadic.Ly.Gen.genWords[i]! := by
  decide +kernel

theorem genExt_mem {G : Type*} [Group G] (s : ℤ → G) :
    ∀ j, 6 ≤ j → j < 13 → slpG s CFSG.KD.LyOm.genExt.toArray j ∈
      Subgroup.closure {slpG s CFSG.KD.LyOm.genExt.toArray 4,
        slpG s CFSG.KD.LyOm.genExt.toArray 5} := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj1 hj2
    rw [slpG_letG s CFSG.KD.LyOm.genExt.toArray j]
    unfold wordG
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    have hl := genExt_letters j hj1 hj2 z hz
    have h4 : slpG s CFSG.KD.LyOm.genExt.toArray 4 ∈ Subgroup.closure
        {slpG s CFSG.KD.LyOm.genExt.toArray 4, slpG s CFSG.KD.LyOm.genExt.toArray 5} :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have h5 : slpG s CFSG.KD.LyOm.genExt.toArray 5 ∈ Subgroup.closure
        {slpG s CFSG.KD.LyOm.genExt.toArray 4, slpG s CFSG.KD.LyOm.genExt.toArray 5} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    unfold letG
    have hn2 : ¬ z.natAbs ≤ 2 := by omega
    have hlt : z.natAbs - 3 < j := by omega
    rw [if_neg hn2, if_pos hlt]
    rcases hl with h7 | h8 | ⟨h9, -⟩
    · rw [h7]
      split_ifs
      · exact h4
      · exact Subgroup.inv_mem _ h4
    · rw [h8]
      split_ifs
      · exact h5
      · exact Subgroup.inv_mem _ h5
    · have hm := ih (z.natAbs - 3) hlt (by omega) (by omega)
      split_ifs
      · exact hm
      · exact Subgroup.inv_mem _ hm

theorem genExt_eq [LySeed] {i : ℕ} (hi : i ≤ 5) :
    slpG seedLetter CFSG.KD.LyOm.genExt.toArray i = slpG seedLetter CFSG.Sporadic.Ly.Gen.genWords i :=
  slpG_congr _ i fun k hk => genExt_prefix k (by omega)

theorem genFacts [LySeed] : LyGenFacts := by
  have h := CFSG.KD.LyOm.gen_checks
  unfold CFSG.KD.LyOm.genChecksOf at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hu21, hu7⟩, hu3⟩, hau⟩, haz⟩, hut⟩, hz22⟩, hz2⟩, h8⟩, h9⟩, h10⟩, h11⟩,
    h12⟩ := h
  obtain ⟨hlen, hv⟩ := vals_facts CFSG.KD.LyOm.genExt
  have hl : CFSG.KD.LyOm.genExt.length = 13 := by
    have := genExt_size
    simpa using this
  have hrep : ∀ i < 13, Rp (CFSG.KD.LyOm.genVals.getD i (0, 0)).1
      (slpG seedLetter CFSG.KD.LyOm.genExt.toArray i) := by
    intro i hi
    have e : CFSG.KD.LyOm.genVals.getD i (0, 0) = CFSG.KD.LyOm.genVals.getD i
        (CFSG.KD.LyOm.BC.ONEF, CFSG.KD.LyOm.BC.ONEF) := by
      unfold CFSG.KD.LyOm.genVals
      rw [List.getD_eq_getElem _ _ (by rw [hlen, hl]; exact hi),
        List.getD_eq_getElem _ _ (by rw [hlen, hl]; exact hi)]
    rw [e]
    exact (hv i (by rw [hl]; exact hi)).1
  have hU := hrep 2 (by norm_num)
  have hZ := hrep 4 (by norm_num)
  have hT := hrep 5 (by norm_num)
  rw [genExt_eq (by norm_num)] at hU hZ hT
  have hone := LRep.one (φ := matHom) one_facts
  have hU7 := fPow_hom hBC one_facts hU 7
  refine ⟨eq_of_lanes (fPow_hom hBC one_facts hU 21) hone hu21,
    ne_of_lanes hU7 hone hu7, ne_of_lanes (fPow_hom hBC one_facts hU 3) hone hu3,
    eq_of_lanes (LRep.mul hBC rp_A hU) (LRep.mul hBC hU rp_A) hau,
    eq_of_lanes (LRep.mul hBC rp_A hZ) (LRep.mul hBC hZ rp_A) haz,
    eq_of_lanes (LRep.mul hBC hU7 hT) (LRep.mul hBC hT hU7) hut,
    eq_of_lanes (fPow_hom hBC one_facts hZ 22) hone hz22,
    ne_of_lanes (fPow_hom hBC one_facts hZ 2) hone hz2, fun j hj1 hj2 => ?_⟩
  have hAF : ∀ i j : ℕ, 8 ≤ i → i < 13 → j = i - 6 →
      Nat.beq (CFSG.KD.LyOm.genVals.getD i (0, 0)).1 (LySv.AF j) = true →
        CFSG.Sporadic.LySchreier.aStar j ∈ Subgroup.closure {genZ, genT} := by
    intro i j hi1 hi2 hj hb
    obtain ⟨c1, e1, -, -⟩ := af_facts (j := j) (by omega)
    have heq := eq_of_lanes (hrep i hi2) ⟨c1, e1⟩ hb
    rw [← heq]
    have hm := genExt_mem seedLetter i (by omega) hi2
    rw [genExt_eq (by norm_num), genExt_eq (by norm_num)] at hm
    exact hm
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have hk : k < 5 := by omega
  interval_cases k
  · exact hAF 8 2 (by norm_num) (by norm_num) (by norm_num) h8
  · exact hAF 9 3 (by norm_num) (by norm_num) (by norm_num) h9
  · exact hAF 10 4 (by norm_num) (by norm_num) (by norm_num) h10
  · exact hAF 11 5 (by norm_num) (by norm_num) (by norm_num) h11
  · exact hAF 12 6 (by norm_num) (by norm_num) (by norm_num) h12

theorem wordFacts [LySeed] : LyWordFacts :=
  ⟨genFacts, twFacts, hhFacts⟩

end CertificateChecks.KernelLy.Omega
