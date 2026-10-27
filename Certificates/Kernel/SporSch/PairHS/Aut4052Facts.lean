
module

public import Certificates.Kernel.SporSch.PairHS.Aut4052Small
public import Certificates.Kernel.SporSch.PairHS.Aut4052Srch
public import Certificates.Kernel.SporSch.PairHS.Check2220
public import CFSG.Certificates.Kernel.SporSch.SrchPSound
public import CFSG.Certificates.Kernel.SporSch.PairHeCntSound
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHSBase
import CFSG.Sporadic.Schreier.Co3ChainUtil

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PHSAFacts

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Certificates
open CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.PJ3Group CertificateChecks.KernelSporSch.PHSCount
open CertificateChecks.KernelSporSch.PHSClass CFSG.QuasithinUnique.Ch1.SporAutHS

theorem repF_of_rep {P : Nat} {g : Equiv.Perm (Fin 3850)} (h : Rep 3850 (unpack 3850 12 P) g) :
    RepF 3850 (pg 12 (mask 12) P) g := fun x hx => by
  have e := h ⟨x, hx⟩
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn] at e
  exact e

theorem smallParts :
    hexTabK PS0T.chars 4 3850 12 3 PS0 = true ∧
    allN 3 (fun j => nfValidK 4 PHSC.LR (PHSA.nfG j)) = true ∧
    nfValidK 4 PHSC.LR PA4.d = true ∧
    allN 4 (fun k => PHSA.eqB (fun x => PHSA.a0P (PHSA.wP [k] x))
      (fun x => PHSA.wP [k] (PHSA.a0P x))) = true ∧
    PHSA.eqB (fun x => PHSA.wP bWord (PHSA.a0P x))
      (fun x => PHSA.wP yWord (PHSA.wP bWord x)) = true ∧
    PHSA.eqB PHSA.a1P (PHSA.wP (t0Word ++ bWord ++ bWord ++ t1Word ++ bWord ++ bWord ++ bWord ++
      bWord ++ t2Word)) = true ∧
    ordDL PHSCn.bs (PHSA.wP bWord) 15 [5, 3] = true ∧
    ordDL PHSCn.bs (fun x => PHSA.wP l1Word (PHSA.wP bWord x)) 5 [1] = true ∧
    ordDL PHSCn.bs (fun x => PHSA.wP l2Word (PHSA.wP bWord x)) 12 [6, 4] = true ∧
    allN 4 (fun k => bAnd(Nat.blt (PHSA.diAt k) 512,
      PHSA.eqB (fun x => PHSCn.nfp PA4.d (PHSA.wP [k] x))
        (fun x => PHSCn.nfp (PHSCn.r2 (PHSA.diAt k)) (PHSCn.nfp PA4.d x)))) = true ∧
    allN 3 (fun l => bAnd((PHSA.swAt l).all (fun k => Nat.blt k 4),
      PHSA.eqB (fun x => PHSCn.nfp (PHSCn.r2 (PHSCn.gr2 l)) (PHSCn.nfp PA4.d x))
        (fun x => PHSCn.nfp PA4.d (PHSA.wP (PHSA.swAt l) x)))) = true := by
  have h := PHSA.small
  unfold PHSA.smallB at h
  simpa only [bAnd_iff, and_assoc] using h

theorem s0Arr_eq {j : Nat} (hj : j < 3) : s0Arr j = unpack 3850 12 (PS0 j) := by
  have h := hexTabK_sound smallParts.1 j hj
  rw [← PS0T.eq] at h
  exact h

theorem rep_PS0 {j : Nat} (hj : j < 3) :
    Rep 3850 (unpack 3850 12 (PS0 j)) (permOfArr 3850 (unpack 3850 12 (PS0 j))) :=
  (rep_permOfArr (invEqK_sound (allN_spec PHSA.perm j hj)).2).1

theorem s0Strong_succ {j : Nat} (hj : j < 3) : s0Strong[j + 1]! = s0Arr j := by
  rw [s0Strong, getElem!_pos _ (j + 1) (by simp; omega)]
  interval_cases j <;> rfl

theorem ltrP_rep (k : Nat) : RepF 3850 (pg 12 (mask 12) (PHSA.ltrP k)) (hsLtr k) := by
  rcases Nat.lt_or_ge k 4 with hk | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hp
    · have e : hsLtr 0 = PHSCheck.g 0 := by
        rw [ltr_zero, hsGen, hsStrongPerm, PHSCheck.arr_eq 0 (by norm_num)]
        rfl
      rw [e]
      exact repF_of_rep (PHSCheck.rep_g 0 (by norm_num)).1
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : j < 3 := by omega
      have e1 : PHSA.ltrP (j + 1) = PS0 j := by
        unfold PHSA.ltrP
        have hb : Nat.beq (j + 1) 0 = false := rfl
        have hl : Nat.blt (j + 1) 4 = true := Nat.blt_eq.mpr hk
        rw [hb, hl]
        rfl
      rw [e1, ltr_lt hk, s0Strong_succ hj, s0Arr_eq hj]
      exact repF_of_rep (rep_PS0 hj)
  · have e1 : PHSA.ltrP k = PHSC.S 1 := by
      unfold PHSA.ltrP
      have hb : Nat.beq k 0 = false := by
        cases k with
        | zero => omega
        | succ k => rfl
      have hl : Nat.blt k 4 = false := by
        cases h : Nat.blt k 4
        · rfl
        · exact absurd (Nat.blt_eq.mp h) (by omega)
      rw [hb, hl]
    have e : hsLtr k = PHSCheck.g 1 := by
      rw [hsLtr, if_neg (by omega), hsGen, hsStrongPerm, PHSCheck.arr_eq 1 (by norm_num)]
      rfl
    rw [e1, e]
    exact repF_of_rep (PHSCheck.rep_g 1 (by norm_num)).1

theorem a0_rep : RepF 3850 PHSA.a0P (hsLtr 0) := ltrP_rep 0

theorem a1_rep : RepF 3850 PHSA.a1P (hsGen 1) := by
  have h := ltrP_rep 4
  rw [hsLtr, if_neg (by norm_num)] at h
  exact h

theorem wP_rep : ∀ w : List Nat, RepF 3850 (PHSA.wP w) (wordElt w)
  | [] => fun _ _ => rfl
  | k :: w => by
    rw [wordElt_cons]
    exact (ltrP_rep k).comp (wP_rep w)

theorem wordElt_append (u v : List Nat) : wordElt (u ++ v) = wordElt u * wordElt v := by
  simp only [wordElt, List.map_append, List.prod_append]

theorem wordElt_single (k : Nat) : wordElt [k] = hsLtr k := by
  rw [wordElt_cons, wordElt_nil, mul_one]

section HS

theorem ltr_eq_E {j : Nat} (hj : j < 3) : hsLtr (j + 1) = E (PHSA.nfG j) := by
  have hv : nfValidK 4 PHSC.LR (PHSA.nfG j) = true := allN_spec smallParts.2.1 j hj
  have hb : ∀ x < 3850, bindAt 3850 12 PHST.NR PHST.NR PHST.LT PHST.PT (PHSA.nfG j) (PS0 j) x =
      true := by
    intro x hx
    have h := PHSA.bindG_all j hj (x / 770) (by change x / 770 < 5; omega)
    unfold PHSA.bindG PHSCn.bindR at h
    have h2 := allBlk_spec h (x % 770) (Nat.mod_lt _ (by norm_num))
    have e : Nat.add (Nat.mul (x / 770) 770) (x % 770) = x := split
    rwa [e] at h2
  have hR := bind_spec tc hv hb
  have hL := ltrP_rep (j + 1)
  have e1 : PHSA.ltrP (j + 1) = PS0 j := by
    unfold PHSA.ltrP
    have hb' : Nat.beq (j + 1) 0 = false := rfl
    have hl : Nat.blt (j + 1) 4 = true := Nat.blt_eq.mpr (by omega)
    rw [hb', hl]
    rfl
  rw [e1] at hL
  exact hL.unique hR

theorem ltrK_mem (k : Nat) : hsLtr k ∈ P3 := by
  rcases Nat.lt_or_ge k 4 with hk | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hp
    · rw [ltr_zero]
      exact hsGen_mem 0 (by norm_num)
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [ltr_eq_E (by omega)]
      exact E_mem (allN_spec smallParts.2.1 j (by omega))
  · rw [hsLtr, if_neg (by omega)]
    exact hsGen_mem 1 (by norm_num)

theorem wordK_mem : ∀ w : List Nat, wordElt w ∈ P3
  | [] => P3.one_mem
  | k :: w => by
    rw [wordElt_cons]
    exact P3.mul_mem (ltrK_mem k) (wordK_mem w)

theorem eqB_eq {f g : Nat → Nat} {u v : Equiv.Perm (Fin 3850)} (hf : RepF 3850 f u)
    (hg : RepF 3850 g v) (hu : u ∈ P3) (hv : v ∈ P3) (h : PHSA.eqB f g = true) : u = v :=
  eq_of_eqOnL hH' hf hg hu hv h

theorem ltrK_comm : ∀ k < 4, hsLtr 0 * hsLtr k = hsLtr k * hsLtr 0 := by
  intro k hk
  have h := eqB_eq (a0_rep.comp (wP_rep [k])) ((wP_rep [k]).comp a0_rep)
    (P3.mul_mem (ltrK_mem 0) (wordK_mem [k])) (P3.mul_mem (wordK_mem [k]) (ltrK_mem 0))
    (allN_spec smallParts.2.2.2.1 k hk)
  rwa [wordElt_single] at h

theorem bK_conj : wordElt bWord * hsLtr 0 = wordElt yWord * wordElt bWord :=
  eqB_eq ((wP_rep bWord).comp a0_rep) ((wP_rep yWord).comp (wP_rep bWord))
    (P3.mul_mem (wordK_mem _) (ltrK_mem 0)) (P3.mul_mem (wordK_mem _) (wordK_mem _))
    smallParts.2.2.2.2.1

theorem a1K_word : hsGen 1 = wordElt t0Word * wordElt bWord ^ 2 * wordElt t1Word *
    wordElt bWord ^ 4 * wordElt t2Word := by
  have h := eqB_eq a1_rep (wP_rep _) (hsGen_mem 1 (by norm_num)) (wordK_mem _)
    smallParts.2.2.2.2.2.1
  rw [h]
  simp only [wordElt_append, pow_succ, pow_zero, one_mul, mul_assoc]

theorem ds5 : ∀ q, q.Prime → q ∣ 5 → 5 / q ∈ [1] := by
  intro q hq hd
  have := Nat.le_of_dvd (by norm_num) hd
  interval_cases q <;> revert hq hd <;> decide

theorem bK_orders : orderOf (wordElt bWord) = 15 ∧ orderOf (wordElt l1Word * wordElt bWord) = 5 ∧
    orderOf (wordElt l2Word * wordElt bWord) = 12 :=
  ⟨(ordDL_iff hH' hbs' (wP_rep bWord) (wordK_mem _) (by norm_num) ds15 (by decide)).1
      smallParts.2.2.2.2.2.2.1,
    (ordDL_iff hH' hbs' ((wP_rep l1Word).comp (wP_rep bWord))
      (P3.mul_mem (wordK_mem _) (wordK_mem _)) (by norm_num) ds5 (by decide)).1
      smallParts.2.2.2.2.2.2.2.1,
    (ordDL_iff hH' hbs' ((wP_rep l2Word).comp (wP_rep bWord))
      (P3.mul_mem (wordK_mem _) (wordK_mem _)) (by norm_num) ds12 (by decide)).1
      smallParts.2.2.2.2.2.2.2.2.1⟩

noncomputable abbrev Dm : Equiv.Perm (Fin 3850) := E PA4.d

theorem Dm_rep : RepF 3850 (PHSCn.nfp PA4.d) Dm := E_rep smallParts.2.2.1

theorem Dm_mem : Dm ∈ P3 := E_mem smallParts.2.2.1

theorem conj_ltr {k : Nat} (hk : k < 4) :
    PHSA.diAt k < 512 ∧ Dm * hsLtr k * Dm⁻¹ = r2E (PHSA.diAt k) := by
  have h := allN_spec smallParts.2.2.2.2.2.2.2.2.2.1 k hk
  rw [bAnd_iff] at h
  have hi : PHSA.diAt k < 512 := Nat.blt_eq.mp h.1
  refine ⟨hi, ?_⟩
  have e := eqB_eq (Dm_rep.comp (wP_rep [k])) ((E_rep (s2_parts hi).1).comp Dm_rep)
    (P3.mul_mem Dm_mem (wordK_mem _)) (P3.mul_mem (r2_mem hi) Dm_mem) h.2
  rw [wordElt_single] at e
  rw [e, mul_inv_cancel_right]

theorem conj_gen {l : Nat} (hl : l < 3) : (∀ k ∈ PHSA.swAt l, k < 4) ∧
    Dm * wordElt (PHSA.swAt l) * Dm⁻¹ = r2E (PHSCn.gr2 l) := by
  have h := allN_spec smallParts.2.2.2.2.2.2.2.2.2.2 l hl
  rw [bAnd_iff] at h
  refine ⟨fun k hk => Nat.blt_eq.mp (List.all_eq_true.1 h.1 k hk), ?_⟩
  have hq := gr2_lt hl
  have e := eqB_eq ((E_rep (s2_parts hq).1).comp Dm_rep) (Dm_rep.comp (wP_rep _))
    (P3.mul_mem (r2_mem hq) Dm_mem) (P3.mul_mem Dm_mem (wordK_mem _)) h.2
  rw [← e, mul_inv_cancel_right]

theorem r2_mem_conj : ∀ i < 512,
    r2E i ∈ s0Chain.originalSubgroup.map (MulAut.conj Dm).toMonoidHom := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hp
    · rw [r2_one]
      exact Subgroup.one_mem _
    · obtain ⟨h1, h2, h3⟩ := r2_tree hi hp
      rw [h3]
      refine Subgroup.mul_mem _ (ih _ h1 (h1.trans hi)) ⟨wordElt (PHSA.swAt (PHSCn.lab2 i)),
        wordElt_memS0 (conj_gen h2).1, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (conj_gen h2).2

def s2P : Set (Equiv.Perm (Fin 3850)) := {g | ∃ i < 512, g = r2E i}

theorem s2P_closed : ∀ a ∈ s2P, ∀ b ∈ s2P, a * b ∈ s2P := by
  rintro a ⟨i, hi, rfl⟩ b ⟨j, hj, rfl⟩
  obtain ⟨t, ht, hte⟩ := mul_mem_of_table (N := 512) (k := 3) (r := r2E) (gi := PHSCn.gr2)
    (par := PHSCn.par2) (lab := PHSCn.lab2) (m := PHSCn.m2) r2_one (fun i hi hp => r2_tree hi hp)
    (fun i hi l hl => r2_mul hi hl) j hj i hi
  exact ⟨t, ht, hte⟩

noncomputable def S2P : Subgroup (Equiv.Perm (Fin 3850)) :=
  mulClosed s2P s2P_closed (r2E 0) ⟨0, by norm_num, rfl⟩

theorem card_S2P : Nat.card S2P = 512 := by
  have hb : Function.Bijective (fun i : Fin 512 =>
      (⟨r2E i, mem_mulClosed.2 ⟨i, i.2, rfl⟩⟩ : S2P)) := by
    refine ⟨fun i j h => Fin.ext (r2_inj i.2 j.2 (congrArg Subtype.val h)), fun g => ?_⟩
    obtain ⟨i, hi, he⟩ := mem_mulClosed.1 g.2
    exact ⟨⟨i, hi⟩, Subtype.ext he.symm⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_fin]

theorem card_s0 : Nat.card s0Chain.originalSubgroup = 512 := by
  have hinj : Function.Injective (MulAut.conj Dm).toMonoidHom := (MulAut.conj Dm).injective
  have hmap : s0Chain.originalSubgroup.map (MulAut.conj Dm).toMonoidHom = S2P := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap, s0Chain,
        CFSG.Sporadic.Schreier.Co3.ofArrays_originalSubgroup, Subgroup.closure_le]
      rintro _ ⟨⟨i, hi⟩, rfl⟩
      dsimp only
      rw [← ltr_lt hi, SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, (conj_ltr hi).2]
      exact mem_mulClosed.2 ⟨_, (conj_ltr hi).1, rfl⟩
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := mem_mulClosed.1 hg
      exact r2_mem_conj i hi
  rw [← Subgroup.card_map_of_injective hinj, hmap, card_S2P]

theorem hFl : ∀ g ∈ hsChain.originalSubgroup, ∀ f : Nat → Nat, RepF 3850 f g →
    (PHSA.flt f = true ↔ orderOf g = 15 ∧ orderOf (wordElt l1Word * g) = 5 ∧
      orderOf (wordElt l2Word * g) = 12) := by
  intro g hg f hf
  unfold PHSA.flt
  rw [bAnd_iff, bAnd_iff,
    ordDL_iff hH' hbs' ((wP_rep l1Word).comp hf) (P3.mul_mem (wordK_mem _) hg) (by norm_num)
      ds5 (by decide),
    ordDL_iff hH' hbs' ((wP_rep l2Word).comp hf) (P3.mul_mem (wordK_mem _) hg) (by norm_num)
      ds12 (by decide),
    ordDL_iff hH' hbs' hf hg (by norm_num) ds15 (by decide)]
  exact ⟨fun ⟨a, b, c⟩ => ⟨c, a, b⟩, fun ⟨c, a, b⟩ => ⟨a, b, c⟩⟩

theorem card_cnt : Nat.card {g : hsChain.originalSubgroup // (g : Equiv.Perm (Fin 3850)) * hsLtr 0 =
    wordElt yWord * g ∧ orderOf (g : Equiv.Perm (Fin 3850)) = 15 ∧
    orderOf (wordElt l1Word * g) = 5 ∧ orderOf (wordElt l2Word * g) = 12} = 2 := by
  have h := Tab.srchP_sound (b0 := 0) (b1 := 1) (bs := [2, 3]) hsChainArrays
    PairHS.chain_check.1 (by norm_num) tc a0_rep (wP_rep yWord) (ltrK_mem 0) (wordK_mem _)
    (Nat.eq_of_beq_eq_true PHSA.a0_01) hFl
  rw [← h, Nat.eq_of_beq_eq_true PHSCn.c0]
  refine (chunk_sum 25 154 _ PHSA.vAt fun q hq => ?_).trans (Nat.eq_of_beq_eq_true PHSA.vSum)
  have := Nat.eq_of_beq_eq_true (PHSA.sr_all (q / 5) (by change q / 5 < 5; omega) (q % 5) (Nat.mod_lt _ (by norm_num)))
  rw [split] at this
  exact this

theorem facts : Nat.card s0Chain.originalSubgroup = 512
    ∧ (∀ k < 4, hsLtr k ∈ hsChain.originalSubgroup)
    ∧ (∀ k < 4, hsLtr 0 * hsLtr k = hsLtr k * hsLtr 0)
    ∧ wordElt bWord * hsLtr 0 = wordElt yWord * wordElt bWord
    ∧ hsGen 1 = wordElt t0Word * wordElt bWord ^ 2 * wordElt t1Word * wordElt bWord ^ 4 *
        wordElt t2Word
    ∧ (orderOf (wordElt bWord) = 15 ∧ orderOf (wordElt l1Word * wordElt bWord) = 5 ∧
        orderOf (wordElt l2Word * wordElt bWord) = 12)
    ∧ Nat.card {g : hsChain.originalSubgroup // (g : Equiv.Perm (Fin 3850)) * hsLtr 0 =
        wordElt yWord * g ∧ orderOf (g : Equiv.Perm (Fin 3850)) = 15 ∧
        orderOf (wordElt l1Word * g) = 5 ∧ orderOf (wordElt l2Word * g) = 12} = 2 :=
  ⟨card_s0, fun k _ => ltrK_mem k, ltrK_comm, bK_conj, a1K_word, bK_orders, card_cnt⟩

end HS

end CertificateChecks.KernelSporSch.PHSAFacts

end
