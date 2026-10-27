
module

public import Certificates.Kernel.SporSch.PairHe.S2Chk
public import Certificates.Kernel.SporSch.PairHe.Check2223
public import Certificates.Kernel.SporSch.PairHS.ClassCard
public import Certificates.Kernel.SporSch.PairJ3.CntGroup
public import Certificates.Kernel.SporSch.Pair.GenCertK
public import CFSG.Certificates.Kernel.SporSch.PairHSCntSound
public import CFSG.Certificates.Kernel.SporSch.ClosNFTClosedProof
public import CFSG.Sporadic.Schreier.PairHeClassesBase
public import CFSG.Sporadic.Schreier.PairHeCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairHeCheck
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.CertPChainData
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
import Mathlib.Tactic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PHeCount

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Certificates
open CFSG.Certificates.Native CFSG.Sporadic.HeldB
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CertificateChecks.KernelSporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSporSch.PJ3Group CertificateChecks.KernelSporSch.PHSClass

noncomputable abbrev P3 : Subgroup (Equiv.Perm (Fin 8330)) := heChain.originalSubgroup

theorem tc : TabChain 8330 14 9 5 HeC.BP 131 64 PHeT.NR PHeT.NR 147 1024 9 1024 HeC.S HeC.SI
    HeC.LR PHeT.Ts PHeT.LT PHeT.PT PHeT.QT heStrongArrs heBase.toArray PairHe.bs :=
  ⟨He2112.binds, He2112.perm, HeC.ho, by decide, PHeCheck.tabs, rfl⟩

noncomputable abbrev E (F : Nat) : Equiv.Perm (Fin 8330) :=
  nfElt 8330 heStrongArrs heBase.toArray (nfArr 5 F)

theorem E_rep {F : Nat} (hF : nfValidK 5 HeC.LR F = true) : RepF 8330 (PHeSn.nfp F) (E F) :=
  (nfPtT_sound tc hF).2

theorem hbs' : ∀ b ∈ PHeSn.bs, b < 8330 := he_bs_lt

theorem blk_spec {R B N : Nat} {f : Nat → Bool} {h : Nat → Nat → Bool}
    (hh : ∀ g r, h g r = allBlk (Nat.mul (Nat.add (Nat.mul g R) r) B) f B)
    (hall : ∀ g < N, ∀ r < R, h g r = true) (hR : 0 < R) (hB : 0 < B) {i : Nat}
    (hi : i < N * R * B) : f i = true := by
  have hg : i / (R * B) < N := by
    rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos hR hB)]
    rw [Nat.mul_assoc] at hi
    exact hi
  have h0 := hall (i / (R * B)) hg (i / B % R) (Nat.mod_lt _ hR)
  rw [hh] at h0
  have h1 := allBlk_spec h0 (i % B) (Nat.mod_lt _ hB)
  have e : Nat.add (Nat.mul (Nat.add (Nat.mul (i / (R * B)) R) (i / B % R)) B) (i % B) = i := by
    change (i / (R * B) * R + i / B % R) * B + i % B = i
    have h2 : i / (R * B) * R + i / B % R = i / B := by
      rw [Nat.mul_comm R B, ← Nat.div_div_eq_div_mul]
      exact Nat.div_add_mod' (i / B) R
    rw [h2]
    exact Nat.div_add_mod' i B
  rwa [e] at h1

theorem keyL_congr (n : Nat) {f g : Nat → Nat} :
    ∀ {bs : List Nat}, (∀ b ∈ bs, f b = g b) → keyL n f bs = keyL n g bs
  | [], _ => rfl
  | b :: bs, h => by
    change strictN (keyL n f bs) (fun r => Nat.add (f b) (Nat.mul n r)) =
      strictN (keyL n g bs) (fun r => Nat.add (g b) (Nat.mul n r))
    rw [strictN_val, strictN_val, keyL_congr n fun c hc => h c (List.mem_cons_of_mem b hc),
      h b List.mem_cons_self]

theorem evR_unpack : ∀ (RP : List Nat), (∀ P ∈ RP, ∀ y < 8330, pg 14 (mask 14) P y < 8330) →
    ∀ x < 8330, evR (RP.map (unpack 8330 14)) x = PHeSn.wordP RP x
  | [], _, x, _ => rfl
  | P :: RP, h, x, hx => by
    rw [List.map_cons, evR_cons, PairGen.unpack_get hx]
    exact evR_unpack RP (fun Q hQ => h Q (List.mem_cons_of_mem P hQ)) _
      (h P List.mem_cons_self x hx)

theorem gen_lt (k : Nat) (hk : k < 9) (y : Nat) (hy : y < 8330) :
    pg 14 (mask 14) (HeC.S k) y < 8330 := by
  have hI := (invEqK_sound (allN_spec He2112.perm k hk)).2
  have := PairGen.lt_of_isInvA hI hy
  rwa [PairGen.unpack_get hy] at this

section He

theorem hH : BaseFaithful P3 PairHe.bs := he_baseFaithful

theorem hbs : ∀ b ∈ PairHe.bs, b < 8330 := he_bs_lt

theorem E_mem {F : Nat} (hF : nfValidK 5 HeC.LR F = true) : E F ∈ P3 :=
  nfElt_mem heChainArrays (chainCheckFacts heChain_check.1) heChain_valid.1
    (nfPtT_sound tc hF).1

theorem card_P3 : Nat.card P3 = 4030387200 := by
  rw [P3, ← heP_eq_originalSubgroup]
  exact card_heP

abbrev mk (x : Equiv.Perm (Fin 8330)) (hx : x ∈ P3) : P3 := ⟨x, hx⟩

theorem orderOf_conj (c x : P3) : orderOf (c * x * c⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem orderOf_of_isConj {x y : P3} (h : IsConj x y) : orderOf y = orderOf x := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact orderOf_conj c x

theorem isConj_of_eq {d y r : P3} (h : d * y = r * d) : IsConj y r :=
  isConj_iff.2 ⟨d, by rw [h, mul_inv_cancel_right]⟩

theorem not_conj_of_card {x y : P3} {N M : Nat} (hx : Nat.card {u : P3 // IsConj x u} = N)
    (hy : Nat.card {u : P3 // IsConj y u} = M) (hNM : N ≠ M) : ¬IsConj x y := by
  intro h
  have e : {u : P3 // IsConj x u} ≃ {u : P3 // IsConj y u} :=
    Equiv.subtypeEquivRight fun u => ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩
  rw [Nat.card_congr e, hy] at hx
  exact hNM hx.symm

theorem fact2 : (Nat.card P3).factorization 2 = 10 :=
  factorization_eq Nat.prime_two (m := 3935925) (by norm_num) (by rw [card_P3]; norm_num)

noncomputable abbrev EA : Array (Array Nat) × Array Nat × Array Nat := PairHe.closureOf PairHe.wA

noncomputable abbrev EB : Array (Array Nat) × Array Nat × Array Nat := PairHe.closureOf PairHe.wT

theorem hgen : P3 ≤ Subgroup.closure {g | ∃ l < PairHe.gens.size, heGenPerm l = g} := by
  rw [P3, ← heP_eq_originalSubgroup, heP]
  refine Subgroup.closure_mono ?_
  rintro g (rfl | rfl)
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩

theorem closedA : ∀ i < EA.1.size, ∀ l < PairHe.gens.size, ∃ j < EA.1.size,
    baseImgs PairHe.bs (nfWord (rawLevels 8330 heStrongArrs heBase.toArray) EA.1[j]!) =
      conjImgs PairHe.bs PairHe.gens[l]! PairHe.gensInv[l]!
        (nfWord (rawLevels 8330 heStrongArrs heBase.toArray) EA.1[i]!) :=
  ClTP.closNFT_closedP (bs := PairHe.bs) (rep := PairHe.wA) He2112.binds He2112.perm HeC.ho
    (by decide) PHeCheck.tabs rfl PHeCheck.hg PHeCheck.repA_eq PHeCheck.okA

theorem closedB : ∀ i < EB.1.size, ∀ l < PairHe.gens.size, ∃ j < EB.1.size,
    baseImgs PairHe.bs (nfWord (rawLevels 8330 heStrongArrs heBase.toArray) EB.1[j]!) =
      conjImgs PairHe.bs PairHe.gens[l]! PairHe.gensInv[l]!
        (nfWord (rawLevels 8330 heStrongArrs heBase.toArray) EB.1[i]!) :=
  ClTP.closNFT_closedP (bs := PairHe.bs) (rep := PairHe.wT) He2112.binds He2112.perm HeC.ho
    (by decide) PHeCheck.tabs rfl PHeCheck.hg PHeCheck.repB_eq PHeCheck.okB

theorem sizeA : EA.1.size = 24990 :=
  (ClTP.closNFT_proved (bs := PairHe.bs) (rep := PairHe.wA) He2112.binds He2112.perm HeC.ho
    (by decide) PHeCheck.tabs rfl PHeCheck.hg PHeCheck.repA_eq PHeCheck.okA).2.1.trans
    (Nat.eq_of_beq_eq_true PHeCl.cASz)

theorem sizeB : EB.1.size = 187425 :=
  (ClTP.closNFT_proved (bs := PairHe.bs) (rep := PairHe.wT) He2112.binds He2112.perm HeC.ho
    (by decide) PHeCheck.tabs rfl PHeCheck.hg PHeCheck.repB_eq PHeCheck.okB).2.1.trans
    (Nat.eq_of_beq_eq_true PHeCl.cBSz)

theorem okA : closureOK (rawLevels 8330 heStrongArrs heBase.toArray) PairHe.bs PairHe.gens
    PairHe.gensInv PairHe.wA EA.1 EA.2.1 EA.2.2 = true :=
  PHeCheck.facts.2.2.2.1 (PairHe.wA, EA) (by simp [PairHe.cl])

theorem okB : closureOK (rawLevels 8330 heStrongArrs heBase.toArray) PairHe.bs PairHe.gens
    PairHe.gensInv PairHe.wT EB.1 EB.2.1 EB.2.2 = true :=
  PHeCheck.facts.2.2.2.1 (PairHe.wT, EB) (by simp [PairHe.cl])

noncomputable abbrev keysOf (E : Array (Array Nat)) : List Nat :=
  E.toList.map fun nf => imgKey 8330 (baseImgs PairHe.bs
    (nfWord (rawLevels 8330 heStrongArrs heBase.toArray) nf))

theorem keys_nodup : (keysOf EA.1 ++ keysOf EB.1).Nodup := by
  have h := PHeCheck.facts.2.2.2.2.1
  unfold keysDistinctNF at h
  have hn := CFSG.KS.SporSch.nodup_of_strictInc_mergeSort h
  simp only [PairHe.cl, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] at hn
  exact hn

theorem rp_lt {RP : List Nat} (h : ∀ P ∈ RP, P = HeC.S 0 ∨ P = HeC.S 1) :
    ∀ P ∈ RP, ∀ y < 8330, pg 14 (mask 14) P y < 8330 := by
  intro P hP y hy
  rcases h P hP with rfl | rfl
  · exact gen_lt 0 (by norm_num) y hy
  · exact gen_lt 1 (by norm_num) y hy

theorem tARep : RepF 8330 PHeSn.tAP (heGenPerm 0) := by
  intro x hx
  have h := rep_heGen (k := 0) (by norm_num) ⟨x, hx⟩
  rw [PHeCheck.gen_eq 0 (by norm_num)] at h
  change (unpack 8330 14 (HeC.S 0))[x]! = _ at h
  rw [PairGen.unpack_get hx] at h
  exact h

theorem rpb_mem {a b P : Nat} (hP : P ∈ [b, b, b, a, b, b, b, a, b, b, b, a, b, b, b, a]) :
    P = a ∨ P = b := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  omega

theorem tBRep : RepF 8330 PHeSn.tBP heT1 := by
  intro x hx
  have h := repW_hewT ⟨x, hx⟩
  change evR PairHe.wT x = _ at h
  rw [PHeCheck.repB_eq, evR_unpack PHeCl.RPB (rp_lt fun P hP => rpb_mem hP) x hx] at h
  exact h

theorem tAMem : heGenPerm 0 ∈ P3 := heGenPerm_mem_orig (by norm_num)

theorem tBMem : heT1 ∈ P3 := heT1_mem

theorem tAOrd : orderOf (heGenPerm 0) = 2 :=
  he_orderOf_of_word repW_hewA tAMem (by norm_num) PHeCheck.facts.1.1

theorem tBOrd : orderOf heT1 = 2 :=
  he_orderOf_of_word repW_hewT tBMem (by norm_num)
    (PHeCheck.facts.2.2.1 (PairHe.wT, EB) (by simp [PairHe.cl]))

theorem card_clA : Nat.card {y : P3 // IsConj (mk (heGenPerm 0) tAMem) y} = 24990 := by
  rw [card_class_of_closed heChainArrays (chainCheckFacts heChain_check.1) heChain_valid.1
    hH hbs he_gens hgen repW_hewA tAMem okA closedA (List.nodup_append.1 keys_nodup).1, sizeA]

theorem card_clB : Nat.card {y : P3 // IsConj (mk heT1 tBMem) y} = 187425 := by
  rw [card_class_of_closed heChainArrays (chainCheckFacts heChain_check.1) heChain_valid.1
    hH hbs he_gens hgen repW_hewT tBMem okB closedB (List.nodup_append.1 keys_nodup).2.1, sizeB]

noncomputable abbrev tAK : P3 := mk (heGenPerm 0) tAMem
noncomputable abbrev tBK : P3 := mk heT1 tBMem

theorem not_conj_AB : ¬IsConj tAK tBK := not_conj_of_card card_clA card_clB (by norm_num)

theorem s2_row {i : Nat} (hi : i < 1024) : PHeSn.s2At i = true :=
  blk_spec (R := 8) (B := 16) (N := 8) (h := PHeSn.s2B) (fun _ _ => rfl) PHeSn.s2B_all
    (by norm_num) (by norm_num) (by norm_num; exact hi)

theorem s2_parts {i : Nat} (hi : i < 1024) :
    nfValidK 5 HeC.LR (PHeSn.r2 i) = true ∧
    (0 < i → PHeSn.par2 i < i ∧ PHeSn.lab2 i < 5 ∧ eqOnL PHeSn.bs (PHeSn.nfp (PHeSn.r2 i))
      (fun b => PHeSn.nfp (PHeSn.r2 (PHeSn.par2 i))
        (PHeSn.nfp (PHeSn.r2 (PHeSn.gr2 (PHeSn.lab2 i))) b)) = true) ∧
    (i = 0 → eqOnL PHeSn.bs (PHeSn.nfp (PHeSn.r2 i)) (fun x => x) = true) ∧
    (∀ l < 5, PHeSn.m2 i l < 1024 ∧ eqOnL PHeSn.bs
      (fun b => PHeSn.nfp (PHeSn.r2 i) (PHeSn.nfp (PHeSn.r2 (PHeSn.gr2 l)) b))
      (PHeSn.nfp (PHeSn.r2 (PHeSn.m2 i l))) = true) ∧
    (ordPL PHeSn.bs (PHeSn.nfp (PHeSn.r2 i)) 2 = true → nfValidK 5 HeC.LR (PHeSn.d2 i) = true ∧
      eqOnL PHeSn.bs (fun b => PHeSn.nfp (PHeSn.d2 i) (PHeSn.tSel (PHeSn.c2 i) b))
        (fun b => PHeSn.nfp (PHeSn.r2 i) (PHeSn.nfp (PHeSn.d2 i) b)) = true) := by
  have h := s2_row hi
  unfold PHeSn.s2At at h
  rw [bAnd_iff, bAnd_iff, bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun hp => ?_, fun h0 => ?_, fun l hl => ?_, fun ho => ?_⟩
  · rw [blt_true hp, bAnd_iff, bAnd_iff] at h2
    exact ⟨Nat.blt_eq.mp h2.1, Nat.blt_eq.mp h2.2.1, h2.2.2⟩
  · subst h0
    exact h2
  · have := allN_spec h3 l hl
    rw [bAnd_iff] at this
    exact ⟨Nat.blt_eq.mp this.1, this.2⟩
  · rw [ho, bAnd_iff] at h4
    exact h4

noncomputable abbrev r2E (i : Nat) : Equiv.Perm (Fin 8330) := E (PHeSn.r2 i)

theorem r2_mem {i : Nat} (hi : i < 1024) : r2E i ∈ P3 := E_mem (s2_parts hi).1

theorem gr2_lt {l : Nat} (hl : l < 5) : PHeSn.gr2 l < 1024 :=
  Nat.blt_eq.mp (allN_spec PHeSn.gens l hl)

theorem r2_one : r2E 0 = 1 :=
  eq_of_eqOnL hH (E_rep (s2_parts (by norm_num)).1) RepF.one (r2_mem (by norm_num)) P3.one_mem
    ((s2_parts (by norm_num)).2.2.1 rfl)

theorem r2_tree {i : Nat} (hi : i < 1024) (hp : 0 < i) :
    PHeSn.par2 i < i ∧ PHeSn.lab2 i < 5 ∧
      r2E i = r2E (PHeSn.par2 i) * r2E (PHeSn.gr2 (PHeSn.lab2 i)) := by
  obtain ⟨h1, h2, h3⟩ := (s2_parts hi).2.1 hp
  have hq := gr2_lt h2
  exact ⟨h1, h2, eq_of_eqOnL hH (E_rep (s2_parts hi).1)
    ((E_rep (s2_parts (h1.trans hi)).1).comp (E_rep (s2_parts hq).1)) (r2_mem hi)
    (P3.mul_mem (r2_mem (h1.trans hi)) (r2_mem hq)) h3⟩

theorem r2_mul {i l : Nat} (hi : i < 1024) (hl : l < 5) :
    PHeSn.m2 i l < 1024 ∧ r2E i * r2E (PHeSn.gr2 l) = r2E (PHeSn.m2 i l) := by
  obtain ⟨hm, he⟩ := (s2_parts hi).2.2.2.1 l hl
  have hq := gr2_lt hl
  exact ⟨hm, eq_of_eqOnL hH ((E_rep (s2_parts hi).1).comp (E_rep (s2_parts hq).1))
    (E_rep (s2_parts hm).1) (P3.mul_mem (r2_mem hi) (r2_mem hq)) (r2_mem hm) he⟩

theorem K2_inj {i j : Nat} (hi : i < 1024) (hj : j < 1024) (h : PHeSn.K2 i = PHeSn.K2 j) :
    i = j := by
  have srt := keysK_sound (cs := [(1024, PHeSn.K2)]) (nB := 8) (R := 8) (B := 16) (by simp)
    (by decide) PHeSn.srt2_all
  have hnd := nodup_of_strictInc_mergeSort srt
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hnd
  exact List.inj_on_of_nodup_map hnd (List.mem_range.2 hi) (List.mem_range.2 hj) h

theorem r2_inj {i j : Nat} (hi : i < 1024) (hj : j < 1024) (h : r2E i = r2E j) : i = j := by
  refine K2_inj hi hj ?_
  unfold PHeSn.K2
  refine keyL_congr 8330 fun b hb => ?_
  have h' : E (PHeSn.r2 i) = E (PHeSn.r2 j) := h
  rw [E_rep (s2_parts hi).1 b (hbs' b hb), E_rep (s2_parts hj).1 b (hbs' b hb), h']

def s2Set : Set P3 := {g | ∃ i < 1024, (g : Equiv.Perm (Fin 8330)) = r2E i}

theorem s2_closed : ∀ a ∈ s2Set, ∀ b ∈ s2Set, a * b ∈ s2Set := by
  rintro a ⟨i, hi, ha⟩ b ⟨j, hj, hb⟩
  obtain ⟨t, ht, hte⟩ := mul_mem_of_table (N := 1024) (k := 5) (r := r2E) (gi := PHeSn.gr2)
    (par := PHeSn.par2) (lab := PHeSn.lab2) (m := PHeSn.m2) r2_one
    (fun i hi hp => r2_tree hi hp) (fun i hi l hl => r2_mul hi hl) j hj i hi
  exact ⟨t, ht, by rw [Subgroup.coe_mul, ha, hb, hte]⟩

noncomputable def S2 : Subgroup P3 :=
  mulClosed s2Set s2_closed (mk (r2E 0) (r2_mem (by norm_num))) ⟨0, by norm_num, rfl⟩

theorem card_S2 : Nat.card S2 = 1024 := by
  have hb : Function.Bijective (fun i : Fin 1024 =>
      (⟨mk (r2E i) (r2_mem i.2), mem_mulClosed.2 ⟨i, i.2, rfl⟩⟩ : S2)) := by
    refine ⟨fun i j h => Fin.ext (r2_inj i.2 j.2 ?_), fun g => ?_⟩
    · have := congrArg (fun g : S2 => ((g : P3) : Equiv.Perm (Fin 8330))) h
      exact this
    · obtain ⟨i, hi, he⟩ := mem_mulClosed.1 g.2
      exact ⟨⟨i, hi⟩, Subtype.ext (Subtype.ext he.symm)⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_fin]

theorem tSel_rep (c : Nat) : RepF 8330 (PHeSn.tSel c) (if c = 0 then heGenPerm 0 else heT1) := by
  intro x hx
  by_cases hc : c = 0
  · subst hc
    rw [ite_eq_left rfl]
    exact tARep x hx
  · rw [ite_eq_right hc]
    have : Nat.beq c 0 = false := by
      cases h : Nat.beq c 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hc
    change Bool.rec (motive := fun _ => Nat) (PHeSn.tBP x) (PHeSn.tAP x) (Nat.beq c 0) = _
    rw [this]
    exact tBRep x hx

theorem invol_conj {x : P3} (hx : orderOf x = 2) : IsConj tAK x ∨ IsConj tBK x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_conj_mem S2 (by rw [card_S2, fact2]; norm_num) (k := 1)
    (by rw [hx, pow_one])
  obtain ⟨i, hi, he⟩ := mem_mulClosed.1 hg
  have ho : orderOf (r2E i) = 2 := by
    rw [← he, Subgroup.orderOf_coe, orderOf_conj, hx]
  obtain ⟨hd, heq⟩ := (s2_parts hi).2.2.2.2
    ((ordPL_iff hH hbs (E_rep (s2_parts hi).1) (r2_mem hi) Nat.prime_two).2 ho)
  have hD := E_mem hd
  have hT : (if PHeSn.c2 i = 0 then heGenPerm 0 else heT1) ∈ P3 := by
    split
    · exact tAMem
    · exact tBMem
  have h1 := eq_of_eqOnL hH ((E_rep hd).comp (tSel_rep (PHeSn.c2 i)))
    ((E_rep (s2_parts hi).1).comp (E_rep hd)) (P3.mul_mem hD hT) (P3.mul_mem (r2_mem hi) hD) heq
  have hb : IsConj (g * x * g⁻¹) x := isConj_iff.2 ⟨g⁻¹, by group⟩
  by_cases hc : PHeSn.c2 i = 0
  · rw [ite_eq_left hc] at h1
    refine Or.inl ((isConj_of_eq (d := mk _ hD) (r := g * x * g⁻¹) (Subtype.ext ?_)).trans hb)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, he]
    exact h1
  · rw [ite_eq_right hc] at h1
    refine Or.inr ((isConj_of_eq (d := mk _ hD) (r := g * x * g⁻¹) (Subtype.ext ?_)).trans hb)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, he]
    exact h1

theorem card_two : Nat.card {x : P3 // orderOf x = 2} = 212415 := by
  have e : {x : P3 // orderOf x = 2} ≃ {y : P3 // IsConj tAK y ∨ IsConj tBK y} :=
    Equiv.subtypeEquivRight fun x => ⟨invol_conj, fun h => by
      rcases h with h | h
      · rw [orderOf_of_isConj h, Subgroup.orderOf_mk]
        exact tAOrd
      · rw [orderOf_of_isConj h, Subgroup.orderOf_mk]
        exact tBOrd⟩
  have hd : Disjoint (fun y : P3 => IsConj tAK y) (fun y => IsConj tBK y) := by
    rw [Pi.disjoint_iff]
    intro y
    rw [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩
    exact not_conj_AB (h1.trans h2.symm)
  classical
  rw [Nat.card_congr (e.trans (subtypeOrEquiv _ _ hd)), Nat.card_sum, card_clA, card_clB]

theorem facts : countOrd PairHe.bs 2 heBlocks = 212415 := by
  rw [← he_card_order 2 (by norm_num)]
  exact card_two

end He

end CertificateChecks.KernelSporSch.PHeCount

end
