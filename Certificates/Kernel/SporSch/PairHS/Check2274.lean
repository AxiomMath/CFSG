
module

public import Certificates.Kernel.SporSch.PairHS.Check2220
public import Certificates.Kernel.SporSch.PairHS.WScanZ
public import Certificates.Kernel.SporSch.PairHS.WScanZI
public import Certificates.Kernel.SporSch.PairHS.WOrd2274
public import CFSG.Certificates.Kernel.SporSch.PairHSWScanSound
public import CFSG.Sporadic.SmallOddCore.HSWordBoundBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PHS2274

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Certificates
open CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.PHSClass CertificateChecks.KernelSporSch.PHSCount
open CFSG.Sporadic.SmallOddCore

section HS

theorem srch_eqP {X Y : Nat → Nat} {x y : Equiv.Perm (Fin 3850)} (hX : RepF 3850 X x)
    (hY : RepF 3850 Y y) (hx : x ∈ P3) (hy : y ∈ P3) (h01 : X 0 = 1) {V : Nat → Nat}
    (hV : ∀ g < 5, ∀ r < 5, Nat.beq (PHSCn.srAt X Y (Nat.add (Nat.mul g 5) r))
      (V (Nat.add (Nat.mul g 5) r)) = true) :
    Nat.card {g : P3 // (g : Equiv.Perm (Fin 3850)) * x = y * g} = sumN 25 V := by
  have h := Tab.srch4_proved (b0 := 0) (b1 := 1) (bs := [2, 3]) hsChainArrays
    PairHS.chain_check.1 (by norm_num) tc hX hY hx hy h01
  rw [← h, Nat.eq_of_beq_eq_true PHSCn.c0]
  refine chunk_sum 25 154 _ V fun q hq => ?_
  have := Nat.eq_of_beq_eq_true (hV (q / 5) (by omega) (q % 5) (Nat.mod_lt _ (by norm_num)))
  rw [split] at this
  exact this

theorem cent_zP : Nat.card {g : P3 // (g : Equiv.Perm (Fin 3850)) * zE = zE * g} = 11 := by
  rw [srch_eqP zRep zRep zMem zMem
    (Nat.eq_of_beq_eq_true repsF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) PHSCn.srZ_all]
  exact Nat.eq_of_beq_eq_true PHSCn.vZ

theorem cent_ziP : Nat.card {g : P3 // (g : Equiv.Perm (Fin 3850)) * zE = ziE * g} = 0 := by
  rw [srch_eqP zRep ziRep zMem ziMem
    (Nat.eq_of_beq_eq_true repsF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) PHSCn.srZI_all]
  exact Nat.eq_of_beq_eq_true PHSCn.vZI

theorem not_conj_zP : ¬IsConj zK zK⁻¹ := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hc' : (c : Equiv.Perm (Fin 3850)) * zE = ziE * c := by
    have : c * zK = zK⁻¹ * c := by rw [← hc, inv_mul_cancel_right]
    have := congrArg Subtype.val this
    rw [ziE_eq]
    exact this
  have hne : Nonempty {g : P3 // (g : Equiv.Perm (Fin 3850)) * zE = ziE * g} := ⟨⟨c, hc'⟩⟩
  have := Nat.card_pos (α := {g : P3 // (g : Equiv.Perm (Fin 3850)) * zE = ziE * g})
  rw [cent_ziP] at this
  exact absurd this (lt_irrefl 0)

theorem closedAP : ∀ i < EA.1.size, ∀ l < PairHS.gens.size, ∃ j < EA.1.size,
    baseImgs PairHS.bs (nfWord (rawLevels 3850 hsStrongArrs PairHS.baseArr) EA.1[j]!) =
      conjImgs PairHS.bs PairHS.gens[l]! PairHS.gensInv[l]!
        (nfWord (rawLevels 3850 hsStrongArrs PairHS.baseArr) EA.1[i]!) :=
  ClTP.closNFT_closedP (bs := PairHS.bs) (rep := PairHS.wA) PHSCheck.binds PHSCheck.perm PHSC.ho
    (by decide) PHSCheck.tabs rfl PHSCheck.hg PHSCheck.repA_eq PHSCheck.okA

theorem card_clAP : Nat.card {y : P3 // IsConj tAK y} = 5775 := by
  rw [card_class_of_closed hsChainArrays (chainCheckFacts PairHS.chain_check.1) hsChain_valid.1
    hH hbs hs_gens hgen repWA tAMem okA closedAP (List.nodup_append.1 keys_nodup).1, sizeA]

theorem keysA : EA.1.toList.map (fun nf => imgKey 3850 (baseImgs PairHS.bs
      (nfWord (rawLevels 3850 hsStrongArrs PairHS.baseArr) nf))) =
    (List.range PHST.c).map PHSCl.KA :=
  (ClTP.closNFT_proved (bs := PairHS.bs) (rep := PairHS.wA) PHSCheck.binds PHSCheck.perm PHSC.ho
    (by decide) PHSCheck.tabs rfl PHSCheck.hg PHSCheck.repA_eq PHSCheck.okA).2.2

theorem keyL_keyElt {f : Nat → Nat} {g : Equiv.Perm (Fin 3850)} (hf : RepF 3850 f g) :
    keyL 3850 f PairHS.bs = keyElt 3850 PairHS.bs g := by
  rw [ClP.keyL_eq, keyElt]
  congr 1
  refine List.map_congr_left fun b hb => ?_
  rw [dite_eq_left (hbs b hb)]
  exact hf b (hbs b hb)

theorem xA_conj {i : Nat} (hi : i < 5775) : IsConj tAK (mk (xA i) (xA_mem hi)) := by
  have hsz : EA.1.size = 5775 := sizeA
  have hi' : i < EA.1.size := hsz ▸ hi
  obtain ⟨hnf, c, hc, hce⟩ := closureOK_spec hsChainArrays (chainCheckFacts PairHS.chain_check.1)
    hsChain_valid.1 hH hbs hs_gens repWA tAMem okA i hi'
  have hmem := nfElt_mem hsChainArrays (chainCheckFacts PairHS.chain_check.1) hsChain_valid.1 hnf
  have hk : (EA.1.toList.map fun nf => imgKey 3850 (baseImgs PairHS.bs
      (nfWord (rawLevels 3850 hsStrongArrs PairHS.baseArr) nf)))[i]? = some (PHSCl.KA i) := by
    rw [keysA, List.getElem?_map, List.getElem?_range (cSzA ▸ hi), Option.map_some]
  rw [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hi', Option.map_some,
    ← getElem!_pos EA.1 i hi', imgKey_baseImgs hbs (repW_nfWord hsChainArrays
      (chainCheckFacts PairHS.chain_check.1) hnf), Option.some_inj] at hk
  have hx : xA i = nfElt 3850 hsStrongArrs PairHS.baseArr EA.1[i]! := by
    refine keyElt_inj hH hbs (xA_mem hi) hmem ?_
    rw [hk, key_recA hi, keyL_keyElt (E_rep (inv_recA hi).1)]
  refine isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hx, hce]

noncomputable def recA : Fin 5775 → {x : P3 // IsConj tAK x} := fun i =>
  ⟨mk (xA i) (xA_mem i.2), xA_conj i.2⟩

theorem recA_bij : Function.Bijective recA := by
  have hinj : Function.Injective recA := by
    intro s t h
    have hv : xA s = xA t := congrArg (fun y : {x : P3 // IsConj tAK x} => ((y : P3) :
      Equiv.Perm (Fin 3850))) h
    exact Fin.ext (KA_inj s.2 t.2 (keyA_eq s.2 t.2 hv))
  exact hinj.bijective_of_nat_card_le (by rw [card_clAP, Nat.card_fin])

theorem recA_cover {x : P3} (hx : IsConj tAK x) : ∃ i < 5775, xA i = x := by
  obtain ⟨i, hi⟩ := recA_bij.2 ⟨x, hx⟩
  exact ⟨i, i.2, congrArg (fun y : {x : P3 // IsConj tAK x} => ((y : P3) :
    Equiv.Perm (Fin 3850))) hi⟩

def Qc (x y : P3) : Prop :=
  orderOf y = 5 ∧ orderOf (x * y * x⁻¹ * y⁻¹) = 5 ∧ orderOf (x * y ^ 2) = 10

theorem qc_conj (g x y : P3) : Qc (g * x * g⁻¹) (g * y * g⁻¹) ↔ Qc x y := by
  have e : ∀ u : P3, g * u * g⁻¹ = MulAut.conj g u := fun u => rfl
  unfold Qc
  simp only [e, ← map_inv, ← map_mul, ← map_pow, MulEquiv.orderOf_eq]

theorem qc_iff {x w : P3} (hx : orderOf x = 2) : Qc x (x⁻¹ * w) ↔
    orderOf ((x : Equiv.Perm (Fin 3850)) * w) = 5 ∧
    orderOf ((w : Equiv.Perm (Fin 3850)) * x * (w : Equiv.Perm (Fin 3850))⁻¹ * x) = 5 ∧
    orderOf ((w : Equiv.Perm (Fin 3850)) * x * w) = 10 := by
  have hxi : x⁻¹ = x := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hx, pow_orderOf_eq_one]
  have e1 : x * (x⁻¹ * w) * x⁻¹ * (x⁻¹ * w)⁻¹ = w * x⁻¹ * w⁻¹ * x := by group
  have e2 : x * (x⁻¹ * w) ^ 2 = w * x⁻¹ * w := by
    simp only [pow_two, mul_assoc, mul_inv_cancel_left]
  unfold Qc
  rw [e1, e2, hxi, ← Subgroup.orderOf_coe (x * w), ← Subgroup.orderOf_coe (w * x * w⁻¹ * x),
    ← Subgroup.orderOf_coe (w * x * w)]
  rfl

theorem scanW_card (w : P3) {Z ZI : Nat → Nat} (hZ : RepF 3850 Z w)
    (hZI : RepF 3850 ZI (w : Equiv.Perm (Fin 3850))⁻¹)
    (hV : ∀ g < 3, ∀ r < 4, Nat.beq (PHSW.scAt Z ZI (Nat.add (Nat.mul g 4) r))
      (PHSW.VZ (Nat.add (Nat.mul g 4) r)) = true) :
    Nat.card {x : P3 // IsConj tAK x ∧ Qc x (x⁻¹ * w)} = 11 := by
  classical
  have hs := chunk_sum 12 512 (scanWAt 12 PHST.NR PHST.NR PHST.LT PHST.PT PHSCn.bs PHST.c
    PHSCl.XA Z ZI) PHSW.VZ fun q hq => by
      have := Nat.eq_of_beq_eq_true (hV (q / 4) (by omega) (q % 4) (Nat.mod_lt _ (by norm_num)))
      rw [split] at this
      exact this
  have hv : sumN 12 PHSW.VZ = 11 := by decide
  rw [hv, sumN_finset] at hs
  have hs2 : ∑ i ∈ Finset.range (12 * 512), (if i < 5775 ∧
      orderOf (xA i * (w : Equiv.Perm (Fin 3850))) = 5 ∧
      orderOf ((w : Equiv.Perm (Fin 3850)) * xA i * (w : Equiv.Perm (Fin 3850))⁻¹ * xA i) = 5 ∧
      orderOf ((w : Equiv.Perm (Fin 3850)) * xA i * w) = 10 then 1 else 0) = 11 := by
    rw [← hs]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [scanWAt_eq tc' hH' hbs' hZ hZI w.2 (fun hi => (inv_recA (cSzA ▸ hi)).1)
      (fun hi => xA_mem (cSzA ▸ hi)), cSzA]
  rw [← Finset.card_filter] at hs2
  set FA := Finset.filter (fun i => orderOf (xA i * (w : Equiv.Perm (Fin 3850))) = 5 ∧
      orderOf ((w : Equiv.Perm (Fin 3850)) * xA i * (w : Equiv.Perm (Fin 3850))⁻¹ * xA i) = 5 ∧
      orderOf ((w : Equiv.Perm (Fin 3850)) * xA i * w) = 10) (Finset.range 5775) with hFA
  have hset : FA = Finset.filter (fun i => i < 5775 ∧
      orderOf (xA i * (w : Equiv.Perm (Fin 3850))) = 5 ∧
      orderOf ((w : Equiv.Perm (Fin 3850)) * xA i * (w : Equiv.Perm (Fin 3850))⁻¹ * xA i) = 5 ∧
      orderOf ((w : Equiv.Perm (Fin 3850)) * xA i * w) = 10) (Finset.range (12 * 512)) := by
    refine Finset.ext fun i => ?_
    simp only [hFA, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, h⟩
      exact ⟨by omega, hi, h⟩
    · rintro ⟨-, hi, h⟩
      exact ⟨hi, h⟩
  have hcard : FA.card = 11 := by rw [hset, hs2]
  have hord : ∀ {i : Nat} (hi : i < 5775), orderOf (mk (xA i) (xA_mem hi)) = 2 := fun hi => by
    rw [Subgroup.orderOf_mk]
    exact (inv_recA hi).2
  have hmemFA : ∀ i ∈ FA, ∃ hi : i < 5775, IsConj tAK (mk (xA i) (xA_mem hi)) ∧
      Qc (mk (xA i) (xA_mem hi)) ((mk (xA i) (xA_mem hi))⁻¹ * w) := by
    intro i hiF
    rw [hFA, Finset.mem_filter, Finset.mem_range] at hiF
    exact ⟨hiF.1, xA_conj hiF.1, (qc_iff (hord hiF.1)).2 hiF.2⟩
  let f : FA → {x : P3 // IsConj tAK x ∧ Qc x (x⁻¹ * w)} := fun i =>
    ⟨mk (xA i.1) (xA_mem (hmemFA i.1 i.2).1), (hmemFA i.1 i.2).2⟩
  have hb : Function.Bijective f := by
    refine ⟨fun s t h => ?_, fun x => ?_⟩
    · have hv : xA s.1 = xA t.1 := congrArg (fun y : {x : P3 // IsConj tAK x ∧ Qc x (x⁻¹ * w)} =>
        ((y : P3) : Equiv.Perm (Fin 3850))) h
      have hs' := (hmemFA s.1 s.2).1
      have ht' := (hmemFA t.1 t.2).1
      exact Subtype.ext (KA_inj hs' ht' (keyA_eq hs' ht' hv))
    · obtain ⟨i, hi, he⟩ := recA_cover x.2.1
      have hxe : mk (xA i) (xA_mem hi) = (x : P3) := Subtype.ext he
      have hq := x.2.2
      rw [← hxe, qc_iff (hord hi)] at hq
      have hiF : i ∈ FA := by
        rw [hFA, Finset.mem_filter, Finset.mem_range]
        exact ⟨hi, hq⟩
      exact ⟨⟨i, hiF⟩, Subtype.ext hxe⟩
  rw [← Nat.card_eq_of_bijective f hb, Nat.card_eq_finsetCard, hcard]

theorem ziRepP : RepF 3850 PHSCn.zP (((zK⁻¹ : P3) : Equiv.Perm (Fin 3850)))⁻¹ := by
  rw [Subgroup.coe_inv, inv_inv]
  exact zRep

theorem ziRepZ : RepF 3850 PHSCn.ziP (zK : Equiv.Perm (Fin 3850))⁻¹ := by
  have e : (zK : Equiv.Perm (Fin 3850))⁻¹ = ziE := ziE_eq.symm
  rw [e]
  exact ziRep

theorem card_filt [Fintype P3] (p : P3 → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = Nat.card {x // p x} := by
  rw [← Fintype.card_subtype, Fintype.card_eq_nat_card]

theorem card_wordConds : Nat.card {y : P3 // HSWordConds tAK y} = 15360 := by
  classical
  have : Fintype P3 := Fintype.ofFinite _
  have hdvd : ¬11 ^ 2 ∣ Nat.card P3 := by
    rw [card_P3]
    norm_num
  have h := CFSG.KS.SylowCount.pair_total_eleven tAK Qc qc_conj hdvd zK_ord nuK_eq not_conj_zP
  simp only [card_filt, Fintype.card_eq_nat_card] at h
  have e1 : Nat.card {y : P3 // IsConj tAK y} = 5775 := card_clAP
  have e2 : Nat.card {c : P3 // c * zK = zK * c} = 11 := cent_K zK cent_zP
  have e3 : Nat.card {x : P3 // IsConj tAK x ∧ Qc x (x⁻¹ * zK)} = 11 :=
    scanW_card zK zRep ziRepZ PHSW.scZ_all
  have e4 : Nat.card {x : P3 // IsConj tAK x ∧ Qc x (x⁻¹ * zK⁻¹)} = 11 :=
    scanW_card zK⁻¹ ziRepK ziRepP PHSW.scZI_all
  have e5 : Nat.card {y : P3 // orderOf (tAK * y) = 11 ∧ Qc tAK y} =
      Nat.card {y : P3 // HSWordConds tAK y} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      have hx2 : orderOf tAK = 2 := by
        rw [Subgroup.orderOf_mk]
        exact tAOrd
      have hxi : tAK⁻¹ = tAK := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hx2, pow_orderOf_eq_one]
      rw [← hsWordConds_iff hx2]
      simp only [Qc, hsWConds, List.forall_mem_cons, List.not_mem_nil, false_implies,
        implies_true, and_true, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, Bool.false_eq_true, ite_false, ite_true]
      constructor
      · rintro ⟨h1, hy, h2, h3⟩
        have hy5 : y ^ 5 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
        have hyi : y⁻¹ = y * y * y * y := by
          rw [inv_eq_iff_mul_eq_one, ← hy5]
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        refine ⟨hy, h1, ?_, by rwa [pow_two] at h3⟩
        rw [hxi, hyi] at h2
        simpa only [mul_assoc] using h2
      · rintro ⟨hy, h1, h2, h3⟩
        have hy5 : y ^ 5 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
        have hyi : y⁻¹ = y * y * y * y := by
          rw [inv_eq_iff_mul_eq_one, ← hy5]
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        refine ⟨h1, hy, ?_, by rwa [pow_two]⟩
        rw [hxi, hyi]
        simpa only [mul_assoc] using h2)
  rw [e1, e2, e3, e4, e5, card_P3] at h
  omega

theorem facts : (ordB PairHS.bs (patW PairHS.wA PairHS.wB [false, true, true]) 10 = true) ∧
    (countPair PairHS.bs 5 PairHS.wA hsWConds PairHS.blocks = 15360) := by
  refine ⟨?_, ?_⟩
  · have e : patW PairHS.wA PairHS.wB [false, true, true] =
        [PHSC.S 1, PHSC.S 1, PHSC.S 0].map (unpack 3850 12) := by
      rw [PHSCheck.wA_eq, PHSCheck.wB_eq]
      rfl
    rw [e]
    exact ordWK_sound PHSWO.o10
  · classical
    have ha : orderOf (hsGen 0) = 2 := hs_word_orders.1
    have h := card_eq_countW hsChainArrays (by norm_num) PairHS.chain_check.1 hs_groups
      (f := pairPred PairHS.bs 5 PairHS.wA hsWConds) (Pr := fun g => HSWordConds (hsGen 0) g)
      (fun w g hw hg => by
        rw [pairPred, Bool.and_eq_true,
          CFSG.Sporadic.Schreier.ordB_iff hs_baseFaithful hs_bs_lt hw hg (by norm_num),
          condsOK_iff hs_baseFaithful hs_bs_lt repW_hswA hw (hsGen_mem 0 (by norm_num)) hg
            (by decide)]
        exact hsWordConds_iff ha)
    rw [show blocksOf 3850 (rawLevels 3850 hsStrongArrs PairHS.baseArr) PairHS.groups =
      PairHS.blocks from rfl, ← countPair_eq] at h
    rw [← h, ← card_wordConds]
    have e : tAE = hsGen 0 := Equiv.ext fun x => Fin.ext ((repWA x).symm.trans (repW_hswA x))
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    rw [← hsWordConds_map P3.subtype P3.subtype_injective tAK y]
    change HSWordConds (hsGen 0) (y : Equiv.Perm (Fin 3850)) ↔
      HSWordConds tAE (y : Equiv.Perm (Fin 3850))
    rw [e]

end HS

end CertificateChecks.KernelSporSch.PHS2274

end
