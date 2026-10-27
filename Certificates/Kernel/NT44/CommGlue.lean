module

public import Certificates.Data.NT44Commutator
import Certificates.Kernel.NT44.BindEq
import Certificates.Kernel.NT44.BindTr
import Certificates.Kernel.NT44.Inv
import Certificates.Kernel.NT44.Pair
import CFSG.Certificates.Kernel.Misc.IdxMulSound
import CFSG.Certificates.Kernel.Misc.ConjTree
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.Misc.RowsBind
import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.Enum.ZCSound
import CFSG.Certificates.Kernel.LocalQTCovTPrim
import CFSG.Certificates.Kernel.BfsPinAlg
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000
set_option quotPrecheck false

namespace CertificateChecks.KernelNT44.CommGlue

open CFSG.GH74.GLS.NT44.PermutationNative CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2 (Rep rep_compA rep_idA eqA_iff allLt_iff toLetters)
open CFSG.KC.Enum (pg pcomp permOK pidn)
open CFSG.KS (mask)
open CFSG.KS.Raw (unpack)
open CFSG.KS.Raw.Orb (PRep prep_pcomp prep_pidn rep_unpack unpack_get)
open CFSG.KC.Misc.ConjTab (cj3 parentAt)
open CFSG.KC.Misc.ArrEnum (allNP_iff rowsBind_arr)
open CFSG.KC.Misc.Clos (allR allR_iff)
open CFSG.KC.Misc.IdxMul
open CFSG.KC.Ord (andB notB)
open CFSG.KC.Loop (strictN)
open CFSG.KC.LQT.P (andB_iff orB_iff notB_iff impB_iff beq_iff letB_eq allN_iff anyN_iff
  anyL_iff)
open CertificateChecks.KernelNT44

local notation "𝔖" => Equiv.Perm (Fin 2688)
local notation "𝒫" => (parent ()).toList

theorem i_tr : (inputs ()).tr = tr () := rfl
theorem i_parent : (inputs ()).parent = parent () := rfl

theorem arr_get {α : Type} [Inhabited α] {N i : ℕ} (f : ℕ → α) (h : i < N) :
    ((List.range N).map f).toArray[i]! = f i := by
  rw [getElem!_pos _ i (by simpa using h)]
  simp

theorem map_get {α β : Type} [Inhabited α] [Inhabited β] {a : Array α} (f : α → β) {i : ℕ}
    (h : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos _ i (by simpa using h), getElem!_pos a i h, Array.getElem_map]

theorem pg8_lt (P k : ℕ) : pg 8 (mask 8) P k < 256 := by
  unfold pg
  have h1 : Nat.land (Nat.shiftRight P (Nat.mul 8 k)) (mask 8) ≤ mask 8 := Nat.and_le_right
  have h2 : mask 8 = 255 := by decide
  omega

theorem tr_size : (tr ()).size = 256 := by
  simp only [tr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil]

theorem tr_eq : tr () = ((List.range 256).map fun i => unpack 4 8 (nt44Tr i)).toArray :=
  rowsBind_arr tr_size nt44_tr_bind

theorem tr_get {i k : ℕ} (hi : i < 256) (hk : k < 4) :
    ((tr ())[i]!)[k]! = pg 8 (mask 8) (nt44Tr i) k := by
  rw [tr_eq, arr_get _ hi, unpack_get hk]

theorem parent_size : (parent ()).size = 256 := by
  simp only [parent, Array.size_append, List.size_toArray, List.length_cons, List.length_nil]

theorem par_get {i : ℕ} (hi : i < 256) : (parent ())[i]! = (𝒫).getD i [] := by
  have hs : i < (parent ()).size := by rw [parent_size]; exact hi
  simp [hs, List.getD_eq_getElem?_getD]

theorem pl_len : (𝒫).length = 256 := by
  rw [Array.length_toList, parent_size]

theorem trf {x k : ℕ} (hx : x < 256) (hk : k < 4) :
    stepF 8 4 (nt44TF 0) x k = pg 8 (mask 8) (nt44Tr x) k :=
  beq_iff.1 ((allN_iff _ _).1 ((allN_iff _ _).1 nt44_trf x hx) k hk)

theorem step_val (i : Fin 256) (k : Fin 4) :
    (step (tr ()) i k).val = stepF 8 4 (nt44TF 0) i.val k.val := by
  have e := tr_get i.2 k.2
  have hl : ((tr ())[i.val]!)[k.val]! < 256 := e ▸ pg8_lt _ _
  rw [step, dif_pos hl]
  exact e.trans (trf i.2 k.2).symm

theorem walk_append (t : Array (Array ℕ)) : ∀ (i : Fin 256) (w : List (Fin 4 × Bool)) (k : Fin 4),
    walk t i (w ++ [(k, true)]) = step t (walk t i w) k
  | i, [], k => rfl
  | i, (k', true) :: w, k => walk_append t (step t i k') w k
  | i, (k', false) :: w, k => walk_append t i w k

theorem pl_facts {j : ℕ} (hj : j < 256) : ((𝒫).getD j []).length < 8 ∧
    (∀ l ∈ (𝒫).getD j [], 1 ≤ l ∧ l ≤ 4) ∧
    (j ≠ 0 → pg 10 (mask 10) (nt44PL 0) j =
      4 * pg 8 (mask 8) (nt44Par 0) j + ((((𝒫).getD j []).getLastD 0).toNat - 1)) := by
  have h := plAt_spec 𝒫 0 nt44_pl j (by rw [pl_len]; exact hj)
  simp only [Nat.zero_add] at h
  exact ⟨h.1, fun l hl => by have := h.2.1 l hl; push_cast at this; exact this, h.2.2⟩

theorem par_facts : (𝒫).getD 0 [] = [] ∧ ∀ j, 1 ≤ j → j < 256 →
    (𝒫).getD j [] = (𝒫).getD (pg 8 (mask 8) (nt44Par 0) j) [] ++ [((𝒫).getD j []).getLastD 0] ∧
      1 ≤ ((𝒫).getD j []).getLastD 0 ∧ ((𝒫).getD j []).getLastD 0 ≤ 4 := by
  have hpar := nt44_parent
  rw [Bool.and_eq_true, decide_eq_true_eq] at hpar
  obtain ⟨h0, hR⟩ := hpar
  refine ⟨h0, fun j h1 h2 => ?_⟩
  have h := (allR_iff _ _ _).1 hR j h1 (by omega)
  unfold parentAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

theorem toLetters_last {w : List ℤ} {l : ℤ} (h1 : 1 ≤ l) (h4 : l ≤ 4) :
    toLetters 4 (w ++ [l]) = toLetters 4 w ++ [(⟨l.toNat - 1, by omega⟩, true)] := by
  rw [toLetters, List.filterMap_append, ← toLetters]
  congr 1
  have h : l ≠ 0 ∧ l.natAbs ≤ 4 := ⟨by omega, by omega⟩
  simp only [List.filterMap_cons, List.filterMap_nil, dif_pos h]
  congr
  · omega
  · simp
    omega

theorem mul_walk : ∀ f j, j < 256 → ((𝒫).getD j []).length < f → ∀ i : Fin 256,
    (walk (tr ()) i (toLetters 4 ((𝒫).getD j []))).val = mulK 8 10 4 (nt44TF 0) (nt44PL 0) f i.val j
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | f + 1, j, hj, hf, i => by
    by_cases j0 : j = 0
    · subst j0
      rw [par_facts.1]
      rfl
    · obtain ⟨hw, hl1, hl4⟩ := par_facts.2 j (by omega) hj
      have hP := (pl_facts hj).2.2 j0
      generalize ((𝒫).getD j []).getLastD 0 = l at hw hl1 hl4 hP
      have e1 : pg 10 (mask 10) (nt44PL 0) j / 4 = pg 8 (mask 8) (nt44Par 0) j := by omega
      have e2 : pg 10 (mask 10) (nt44PL 0) j % 4 = l.toNat - 1 := by omega
      have hlen : ((𝒫).getD (pg 8 (mask 8) (nt44Par 0) j) []).length < f := by
        have := congrArg List.length hw
        simp only [List.length_append, List.length_singleton] at this
        omega
      rw [mulK_succ j0, e1, e2, hw, toLetters_last hl1 hl4, walk_append, step_val,
        mul_walk f _ (pg8_lt _ _) hlen i]

theorem mul_val (i j : Fin 256) :
    (mulIndex (inputs ()).tr (inputs ()).parent i j).val = nt44Mul i.val j.val := by
  rw [i_tr, i_parent, mulIndex, par_get j.2]
  exact mul_walk 8 j.val j.2 (pl_facts j.2).1 i

theorem pow_val (i : Fin 256) : ∀ e,
    (powIndex (inputs ()).tr (inputs ()).parent i e).val = powK nt44Mul i.val e
  | 0 => rfl
  | e + 1 => by
    rw [powIndex.eq_2, mul_val, pow_val i e]
    change nt44Mul (powK nt44Mul i.val e) i.val =
      strictN (powK nt44Mul i.val e) (fun a => nt44Mul a i.val)
    rw [strictN_eq]

theorem ord_mem {i : Fin 256} (h4 : powIndex (inputs ()).tr (inputs ()).parent i 4 = 0)
    (h2 : powIndex (inputs ()).tr (inputs ()).parent i 2 ≠ 0) :
    ∃ a < 84, pg 8 (mask 8) (nt44O4 0) a = i.val := by
  have h := (allN_iff _ _).1 nt44_ord i.val i.2
  rw [ordAt, impB_iff, andB_iff, notB_iff, beq_iff, beq_iff, anyN_iff] at h
  have e4 : powK nt44Mul i.val 4 = 0 := by rw [← pow_val, h4]; rfl
  have e2 : ¬ powK nt44Mul i.val 2 = 0 := fun e => h2 (Fin.ext (by rw [pow_val, e]; rfl))
  obtain ⟨a, ha, e⟩ := h ⟨e4, e2⟩
  exact ⟨a, ha, beq_iff.1 e⟩

theorem row_all : ∀ a < 84, nt44Row a = true := by
  intro a ha
  rcases (by omega : a < 21 ∨ (21 ≤ a ∧ a < 42) ∨ (42 ≤ a ∧ a < 63) ∨ 63 ≤ a) with
    h | h | h | h
  · exact (allR_iff _ _ _).1 nt44_pair0 a (by omega) (by omega)
  · exact (allR_iff _ _ _).1 nt44_pair1 a (by omega) (by omega)
  · exact (allR_iff _ _ _).1 nt44_pair2 a (by omega) (by omega)
  · exact (allR_iff _ _ _).1 nt44_pair3 a (by omega) (by omega)

theorem ofFn16 (g : ℕ → ℕ → ℕ) : (List.ofFn (n := 16) fun q : Fin 16 =>
    g (finProdFinEquiv.symm q : Fin 4 × Fin 4).1.val
      (finProdFinEquiv.symm q : Fin 4 × Fin 4).2.val) =
    [g 0 0, g 0 1, g 0 2, g 0 3, g 1 0, g 1 1, g 1 2, g 1 3,
      g 2 0, g 2 1, g 2 2, g 2 3, g 3 0, g 3 1, g 3 2, g 3 3] := by
  simp only [List.ofFn_succ, List.ofFn_zero]
  rfl

theorem prods_val (i j : Fin 256) :
    (pairProducts (inputs ()).tr (inputs ()).parent i j).map Fin.val =
      prods4 nt44Mul (powK nt44Mul i.val 0) (powK nt44Mul i.val 1) (powK nt44Mul i.val 2)
        (powK nt44Mul i.val 3) (powK nt44Mul j.val 0) (powK nt44Mul j.val 1)
        (powK nt44Mul j.val 2) (powK nt44Mul j.val 3) := by
  simp only [pairProducts, List.map_ofFn, Function.comp_def, mul_val, pow_val]
  exact ofFn16 (fun r s => nt44Mul (powK nt44Mul i.val r) (powK nt44Mul j.val s))

theorem actor_ok : ActorSetsOK (actorSets ()) := by decide +kernel

theorem pair_ok : PairActorOK (inputs ()).tr (inputs ()).parent (actorSets ()) := by
  intro i j hv
  obtain ⟨hc, hi4, hi2, hj4, hj2, hnd⟩ := hv
  obtain ⟨a, ha, ea⟩ := ord_mem hi4 hi2
  obtain ⟨b, hb, eb⟩ := ord_mem hj4 hj2
  have hr := row_all a ha
  rw [nt44Row, pairRow] at hr
  have h : pairAt nt44Mul nt44Am 3 (pg 8 (mask 8) (nt44O4 0) a) (pg 8 (mask 8) (nt44O4 0) b) =
      true := (allN_iff _ _).1 hr b hb
  simp only [ea, eb, pairAt, orB_iff, notB_iff, beq_iff, letB_eq, anyN_iff, ← prods_val] at h
  have hcomm : nt44Mul i.val j.val = nt44Mul j.val i.val := by rw [← mul_val, ← mul_val, hc]
  rcases h with h | h
  · exact absurd hcomm h
  have hndL := List.Nodup.map Fin.val_injective hnd
  rcases h with h0 | ⟨a', ha', e⟩
  · exfalso
    have hx : nt44Mul (powK nt44Mul i.val 0) (powK nt44Mul j.val 0) ∈
        (pairProducts (inputs ()).tr (inputs ()).parent i j).map Fin.val := by
      rw [prods_val]
      simp [prods4]
    have := ndMask_mem hndL hx
    rw [h0, Nat.zero_testBit] at this
    exact Bool.false_ne_true this
  have sub : pairProducts (inputs ()).tr (inputs ()).parent i j ⊆ (actorSets ())[a']! := by
    intro x hx
    have hb' := ndMask_mem hndL (List.mem_map_of_mem hx)
    rw [e] at hb'
    have hm := (allN_iff _ _).1 ((allN_iff _ _).1 nt44_am a' ha') x.val x.2
    rw [impB_iff] at hm
    obtain ⟨y, hy, ey⟩ := (anyL_iff _ _).1 (hm ((bitB_iff _ _).2 hb'))
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have hzx : z = x := Fin.ext (beq_iff.1 ey)
    rw [← hzx]
    exact hz
  have hl1 : (pairProducts (inputs ()).tr (inputs ()).parent i j).length = 16 := by
    simp [pairProducts]
  have hl2 : ((actorSets ())[a']!).length = 16 := (actor_ok.2 ⟨a', ha'⟩).2
  exact ⟨⟨a', ha'⟩, (hnd.subperm sub).perm_of_length_le (hl2.trans hl1.symm).le⟩

theorem data_ok : DataOK (inputs ()) := by
  refine ⟨rfl, ?_, rfl, ?_, ?_, fun i => ⟨?_, fun k => ?_⟩, ?_⟩
  · change (lifts ()).size = 256
    simp only [lifts, Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
  · rw [i_parent, parent_size]
  · rw [i_tr, tr_size]
  · rw [i_tr, tr_eq, arr_get _ i.2]
    simp [unpack]
  · rw [i_tr, tr_get i.2 k.2]
    exact pg8_lt _ _
  · unfold positiveWordsOK
    rw [i_parent, parent_size, allLt_iff]
    intro i hi
    rw [par_get hi, List.all_eq_true]
    intro z hz
    have := (pl_facts hi).2.1 z hz
    simp only [Bool.or_eq_true, beq_iff_eq]
    omega

open scoped Classical in
noncomputable def pOf (P : ℕ) : 𝔖 := if h : ∃ g, PRep 2688 12 P g then h.choose else 1

theorem prep_unique {P : ℕ} {g h : 𝔖} (hg : PRep 2688 12 P g) (hh : PRep 2688 12 P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem perm_of {P Q : ℕ} (h : permOK 2688 12 (mask 12) (2688 * 12) P Q = true) :
    PRep 2688 12 P (pOf P) ∧ PRep 2688 12 Q (pOf P)⁻¹ := by
  obtain ⟨g, hg, hq⟩ := CFSG.KC.EnumSound.permOK_perm h
  have hex : ∃ g, PRep 2688 12 P g := ⟨g, hg⟩
  have e : pOf P = g := by
    rw [pOf, dif_pos hex]
    exact prep_unique hex.choose_spec hg
  rw [e]
  exact ⟨hg, hq⟩

theorem prep_cj3 {a b c : ℕ} {α β γ : 𝔖} (ha : PRep 2688 12 a α) (hb : PRep 2688 12 b β)
    (hc : PRep 2688 12 c γ) : PRep 2688 12 (cj3 2688 12 a b c) (α * β * γ) :=
  prep_pcomp (by norm_num) (prep_pcomp (by norm_num) ha hb) hc

theorem arr_eq {t u : Array ℕ} {g : 𝔖} (ht : t.size = 2688) (hu : u.size = 2688)
    (rt : Rep 2688 t g) (ru : Rep 2688 u g) : t = u := by
  apply Array.ext (ht.trans hu.symm)
  intro i h1 h2
  have e := (rt ⟨i, ht ▸ h1⟩).trans (ru ⟨i, ht ▸ h1⟩).symm
  rwa [getElem!_pos t i h1, getElem!_pos u i h2] at e

theorem inv_ks : ∀ i < 2, permOK 2688 12 (mask 12) (2688 * 12) (nt44KS i) (nt44KSI i) = true :=
  fun i hi => allNP_iff.1 nt44_inv_ks i hi

theorem inv_p0 : ∀ i < 9, permOK 2688 12 (mask 12) (2688 * 12) (nt44P0 i) (nt44P0I i) = true :=
  fun i hi => allNP_iff.1 nt44_inv_p0 i hi

theorem inv_l : ∀ i < 256, permOK 2688 12 (mask 12) (2688 * 12) (nt44L i) (nt44LI i) = true := by
  intro i hi
  rcases (by omega : i < 64 ∨ (64 ≤ i ∧ i < 128) ∨ (128 ≤ i ∧ i < 192) ∨ 192 ≤ i) with
    h | h | h | h
  · exact (allR_iff _ _ _).1 nt44_inv_l0 i (by omega) (by omega)
  · exact (allR_iff _ _ _).1 nt44_inv_l1 i (by omega) (by omega)
  · exact (allR_iff _ _ _).1 nt44_inv_l2 i (by omega) (by omega)
  · exact (allR_iff _ _ _).1 nt44_inv_l3 i (by omega) (by omega)

theorem l_rep {i : ℕ} (hi : i < 256) : Rep 2688 (lifts ())[i]! (pOf (nt44L i)) ∧
    Rep 2688 ((lifts ()).map (invCand 2688))[i]! (pOf (nt44L i))⁻¹ ∧
    (lifts ())[i]! = unpack 2688 12 (nt44L i) := by
  have e : (lifts ())[i]! = unpack 2688 12 (nt44L i) := by rw [nt44_lifts_eq, arr_get _ hi]
  have hs : i < (lifts ()).size := by
    rw [nt44_lifts_eq]
    simpa using hi
  refine ⟨?_, ?_, e⟩
  · rw [e]
    exact rep_unpack (perm_of (inv_l i hi)).1
  · rw [map_get _ hs, e, CFSG.KC.LQT.Cov.T.invCand_unpack (inv_l i hi)]
    exact rep_unpack (perm_of (inv_l i hi)).2

theorem ks_rep {i : ℕ} (hi : i < 2) : Rep 2688 (ks ())[i]! (pOf (nt44KS i)) := by
  rw [nt44_ks_eq, arr_get _ hi]
  exact rep_unpack (perm_of (inv_ks i hi)).1

theorem p0_perms : CFSG.KC.Enum.allN 9
    (fun j => permOK 2688 12 (mask 12) (2688 * 12) (nt44P0 j) (nt44P0I j)) = true :=
  CFSG.KS.Raw.Orb.allN_iff.2 inv_p0

theorem witK_ok (W : CommutatorWitness) {c ci t ti : ℕ} (hs : W.sIndex.val < 256)
    (ha : W.aIndex.val < 256)
    (h : witK 2688 12 9 nt44P0 nt44P0I nt44L nt44LI nt44KS W.sIndex.val W.aIndex.val W.cWord
      W.sign c ci t ti = true) :
    lettersOK 9 W.cWord = true ∧
    let D := inputs ()
    let li := liftInvArrays D
    let c := evalP0Word D (p0InvArrays D) W.cWord
    let t := termArray D li W.aIndex c
    let s := D.lifts[W.sIndex.val]!
    let w := witnessW D li W
    isInvA 2688 c (invCand 2688 c) = true ∧
    isInvA 2688 t (invCand 2688 t) = true ∧
    eqA 2688 (compA 2688 (compA 2688 s c) (invCand 2688 s)) c = true ∧
      eqA 2688 (compA 2688 w w) (idA 2688) = true ∧
      eqA 2688 w (idA 2688) = false ∧
      eqA 2688 (compA 2688 w D.ks[0]!) (compA 2688 D.ks[0]! w) = true ∧
      eqA 2688 (compA 2688 w D.ks[1]!) (compA 2688 D.ks[1]! w) = true := by
  rw [witK] at h
  obtain ⟨hw, h⟩ := andB_iff.1 h
  obtain ⟨hp1, h⟩ := andB_iff.1 h
  obtain ⟨hp2, h⟩ := andB_iff.1 h
  obtain ⟨ht, h⟩ := andB_iff.1 h
  obtain ⟨hsc, h⟩ := andB_iff.1 h
  rw [letB_eq] at h
  obtain ⟨hv2, h⟩ := andB_iff.1 h
  obtain ⟨hv1, h⟩ := andB_iff.1 h
  obtain ⟨hk0, hk1⟩ := andB_iff.1 h
  obtain ⟨hcarr, hl⟩ := CFSG.KS.Prim.wordEqK_sound (S := p0 ()) (kS := 9)
    ⟨rfl, fun j hj => by rw [nt44_p0_eq, arr_get _ hj]⟩ p0_perms hw
  refine ⟨hl, ?_⟩
  intro D li carr tarr sarr warr
  have hC : carr = unpack 2688 12 c := hcarr
  have pC := perm_of hp1
  have pT := perm_of hp2
  have pL := perm_of (inv_l _ ha)
  have pS := perm_of (inv_l _ hs)
  obtain ⟨rL, rLI, -⟩ := l_rep ha
  obtain ⟨rS, -, eS⟩ := l_rep hs
  have rSI : Rep 2688 (invCand 2688 sarr) (pOf (nt44L W.sIndex.val))⁻¹ := by
    change Rep 2688 (invCand 2688 (lifts ())[W.sIndex.val]!) _
    rw [eS, CFSG.KC.LQT.Cov.T.invCand_unpack (inv_l _ hs)]
    exact rep_unpack pS.2
  have rC : Rep 2688 carr (pOf c) := by rw [hC]; exact rep_unpack pC.1
  have rCI : Rep 2688 (invCand 2688 carr) (pOf c)⁻¹ := by
    rw [hC, CFSG.KC.LQT.Cov.T.invCand_unpack hp1]
    exact rep_unpack pC.2
  have rT : Rep 2688 tarr ((pOf c)⁻¹ * (pOf (nt44L W.aIndex.val) * pOf c *
      (pOf (nt44L W.aIndex.val))⁻¹)) :=
    rep_compA rCI (rep_compA (rep_compA rL rC) rLI)
  have eT : pOf t = (pOf c)⁻¹ * (pOf (nt44L W.aIndex.val) * pOf c *
      (pOf (nt44L W.aIndex.val))⁻¹) := by
    refine prep_unique pT.1 ?_
    rw [Nat.eq_of_beq_eq_true ht]
    exact prep_pcomp (by norm_num) pC.2 (prep_cj3 pL.1 pC.1 pL.2)
  have hsz : tarr.size = 2688 := by
    change (compA 2688 _ _).size = 2688
    simp [compA]
  have rTu : Rep 2688 (unpack 2688 12 t) ((pOf c)⁻¹ * (pOf (nt44L W.aIndex.val) * pOf c *
      (pOf (nt44L W.aIndex.val))⁻¹)) := by
    rw [← eT]
    exact rep_unpack pT.1
  have hT : tarr = unpack 2688 12 t := arr_eq hsz (by simp [unpack]) rT rTu
  have ew : warr = if W.sign then tarr else invCand 2688 tarr := rfl
  obtain ⟨om, rW, pV⟩ : ∃ om : 𝔖, Rep 2688 warr om ∧
      PRep 2688 12 (Bool.rec (motive := fun _ => ℕ) ti t W.sign) om := by
    cases hsg : W.sign
    · refine ⟨(pOf t)⁻¹, ?_, pT.2⟩
      rw [ew, hsg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hT, CFSG.KC.LQT.Cov.T.invCand_unpack hp2]
      exact rep_unpack pT.2
    · refine ⟨pOf t, ?_, pT.1⟩
      rw [ew, hsg]
      simp only [↓reduceIte]
      rw [hT]
      exact rep_unpack pT.1
  generalize Bool.rec (motive := fun _ => ℕ) ti t W.sign = v at hv2 hv1 hk0 hk1 pV
  have rK0 := ks_rep (i := 0) (by norm_num)
  have rK1 := ks_rep (i := 1) (by norm_num)
  have pK0 := (perm_of (inv_ks 0 (by norm_num))).1
  have pK1 := (perm_of (inv_ks 1 (by norm_num))).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hC, CFSG.KC.LQT.Cov.T.invCand_unpack hp1]
    exact CFSG.KS.Raw.Orb.isInvA_unpack hp1
  · rw [hT, CFSG.KC.LQT.Cov.T.invCand_unpack hp2]
    exact CFSG.KS.Raw.Orb.isInvA_unpack hp2
  · refine (eqA_iff (rep_compA (rep_compA rS rC) rSI) rC).2
      (prep_unique (prep_cj3 pS.1 pC.1 pS.2) ?_)
    rw [Nat.eq_of_beq_eq_true hsc]
    exact pC.1
  · refine (eqA_iff (rep_compA rW rW) rep_idA).2 (prep_unique (prep_pcomp (by norm_num) pV pV) ?_)
    rw [Nat.eq_of_beq_eq_true hv2]
    exact prep_pidn (by norm_num) (by norm_num)
  · rw [anyN_iff] at hv1
    obtain ⟨x, hx, hne⟩ := hv1
    rw [notB_iff, beq_iff] at hne
    refine Bool.eq_false_iff.2 fun he => hne ?_
    have e1 := (eqA_iff rW rep_idA).1 he
    have := pV ⟨x, hx⟩
    rw [e1] at this
    simpa using this
  · refine (eqA_iff (rep_compA rW rK0) (rep_compA rK0 rW)).2
      (prep_unique (prep_pcomp (by norm_num) pV pK0) ?_)
    rw [Nat.eq_of_beq_eq_true hk0]
    exact prep_pcomp (by norm_num) pK0 pV
  · refine (eqA_iff (rep_compA rW rK1) (rep_compA rK1 rW)).2
      (prep_unique (prep_pcomp (by norm_num) pV pK1) ?_)
    rw [Nat.eq_of_beq_eq_true hk1]
    exact prep_pcomp (by norm_num) pK1 pV

theorem wit_ok (W : CommutatorWitness) (L : List (Fin 256))
    (h : andB (Nat.beq (nt44Mul W.sIndex.val W.sIndex.val) 0)
      (witL 2688 12 9 nt44P0 nt44P0I nt44L nt44LI nt44KS W.sIndex.val W.aIndex.val W.cWord
        W.sign) = true)
    (hm : W.sIndex ∈ L ∧ W.aIndex ∈ L ∧ W.sIndex ≠ 0) :
    WitnessOK (inputs ()) (liftInvArrays (inputs ())) L W := by
  obtain ⟨hss, h⟩ := andB_iff.1 h
  unfold witL at h
  simp only [letB_eq] at h
  have hk := witK_ok W W.sIndex.2 W.aIndex.2 h
  exact ⟨hm.1, hm.2.1, hk.1, Fin.ext (by rw [mul_val]; exact beq_iff.1 hss), hm.2.2, hk.2⟩

theorem wit_small : ∀ a : Fin 3, ((witnesses ())[a.val]!).sIndex ∈ (actorSets ())[a.val]! ∧
    ((witnesses ())[a.val]!).aIndex ∈ (actorSets ())[a.val]! ∧
    ((witnesses ())[a.val]!).sIndex ≠ 0 := by decide +kernel

theorem wit_all : ∀ q < 3, nt44Wit q = true := by
  intro q hq
  interval_cases q
  · exact nt44_wit0
  · exact nt44_wit1
  · exact nt44_wit2

public theorem nt44_comm :
    CommutatorCheckProp (inputs ()) (actorSets ()) (witnesses ()) := by
  refine ⟨data_ok, actor_ok, rfl, fun a => ?_, pair_ok⟩
  have h := wit_all a.val a.2
  rw [nt44Wit] at h
  exact wit_ok _ _ h (wit_small a)

end CertificateChecks.KernelNT44.CommGlue
