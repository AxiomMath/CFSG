
module

public import Certificates.Kernel.SporSch.PairJ3.Check2238
public import Certificates.Kernel.SporSch.PairJ3.WScanZ
public import Certificates.Kernel.SporSch.PairJ3.WScanZ2
public import Certificates.Kernel.SporSch.PairJ3.WOrd2283
public import CFSG.Certificates.Kernel.SporSch.PairJ3WScanSound
public import CFSG.Certificates.Kernel.SporSch.SylowCount
public import CFSG.Sporadic.SmallOddCore.J3WordBoundBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PJ3W2283

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.PJ3Count CFSG.Sporadic.SmallOddCore

section J3

def Qc (x y : P3) : Prop :=
  orderOf y = 3 ∧ orderOf (x * y * x⁻¹ * y⁻¹) = 9 ∧ orderOf (x * y * x * y * x * y ^ 2) = 17

theorem qc_conj (g x y : P3) : Qc (g * x * g⁻¹) (g * y * g⁻¹) ↔ Qc x y := by
  have e : ∀ u : P3, g * u * g⁻¹ = MulAut.conj g u := fun u => rfl
  unfold Qc
  simp only [e, ← map_inv, ← map_mul, ← map_pow, MulEquiv.orderOf_eq]

theorem qc_iff {x w : P3} (hx : orderOf x = 2) : Qc x (x⁻¹ * w) ↔
    orderOf ((x : Equiv.Perm (Fin 6156)) * w) = 3 ∧
    orderOf ((w : Equiv.Perm (Fin 6156)) * x * (w : Equiv.Perm (Fin 6156))⁻¹ * x) = 9 ∧
    orderOf ((w : Equiv.Perm (Fin 6156)) ^ 3 * x * w) = 17 := by
  have hxi : x⁻¹ = x := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hx, pow_orderOf_eq_one]
  have e1 : x * (x⁻¹ * w) * x⁻¹ * (x⁻¹ * w)⁻¹ = w * x⁻¹ * w⁻¹ * x := by group
  have e2 : x * (x⁻¹ * w) * x * (x⁻¹ * w) * x * (x⁻¹ * w) ^ 2 = w ^ 3 * x⁻¹ * w := by
    rw [pow_two, pow_three]
    group
  unfold Qc
  rw [e1, e2, hxi, ← Subgroup.orderOf_coe (x * w), ← Subgroup.orderOf_coe (w * x * w⁻¹ * x),
    ← Subgroup.orderOf_coe (w ^ 3 * x * w)]
  rfl

theorem scanW_card (w : P3) {Z ZI : Nat → Nat} {V : Nat → Nat} (hZ : RepF 6156 Z w)
    (hZI : RepF 6156 ZI (w : Equiv.Perm (Fin 6156))⁻¹)
    (hV : ∀ g < 13, ∀ r < 4, Nat.beq (PJ3W.scAt Z ZI (Nat.add (Nat.mul g 4) r))
      (V (Nat.add (Nat.mul g 4) r)) = true) (h19 : sumN 52 V = 19) :
    Nat.card {x : P3 // IsConj tK x ∧ Qc x (x⁻¹ * w)} = 19 := by
  classical
  have hs := chunk_sum 52 512 (scanJAt 13 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT PJ3Cn.bs PJ3T.c
    PJ3Cl.X Z ZI) V fun q hq => by
      have := Nat.eq_of_beq_eq_true (hV (q / 4) (by omega) (q % 4) (Nat.mod_lt _ (by norm_num)))
      rw [split44] at this
      exact this
  rw [h19, sumN_finset] at hs
  have hs2 : ∑ i ∈ Finset.range (52 * 512), (if i < 26163 ∧
      orderOf (xE i * (w : Equiv.Perm (Fin 6156))) = 3 ∧
      orderOf ((w : Equiv.Perm (Fin 6156)) * xE i * (w : Equiv.Perm (Fin 6156))⁻¹ * xE i) = 9 ∧
      orderOf ((w : Equiv.Perm (Fin 6156)) ^ 3 * xE i * w) = 17 then 1 else 0) = 19 := by
    rw [← hs]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [scanJAt_eq (bs := PJ3Cn.bs) (c := PJ3T.c) (i := i) (X := PJ3Cl.X) tc hH hbs hZ hZI w.2 (fun hi => (inv_rec (lt_of_lt_of_eq hi cSz)).1)
      (fun hi => xE_mem (lt_of_lt_of_eq hi cSz)), cSz]
  rw [← Finset.card_filter] at hs2
  set FA := Finset.filter (fun i => orderOf (xE i * (w : Equiv.Perm (Fin 6156))) = 3 ∧
      orderOf ((w : Equiv.Perm (Fin 6156)) * xE i * (w : Equiv.Perm (Fin 6156))⁻¹ * xE i) = 9 ∧
      orderOf ((w : Equiv.Perm (Fin 6156)) ^ 3 * xE i * w) = 17) (Finset.range 26163) with hFA
  have hset : FA = Finset.filter (fun i => i < 26163 ∧
      orderOf (xE i * (w : Equiv.Perm (Fin 6156))) = 3 ∧
      orderOf ((w : Equiv.Perm (Fin 6156)) * xE i * (w : Equiv.Perm (Fin 6156))⁻¹ * xE i) = 9 ∧
      orderOf ((w : Equiv.Perm (Fin 6156)) ^ 3 * xE i * w) = 17) (Finset.range (52 * 512)) := by
    refine Finset.ext fun i => ?_
    simp only [hFA, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, h⟩
      exact ⟨by omega, hi, h⟩
    · rintro ⟨-, hi, h⟩
      exact ⟨hi, h⟩
  have hcard : FA.card = 19 := by rw [hset, hs2]
  have hord : ∀ {i : Nat} (hi : i < 26163), orderOf (mk (xE i) (xE_mem hi)) = 2 := fun hi => by
    rw [Subgroup.orderOf_mk]
    exact (inv_rec hi).2
  have hmemFA : ∀ i ∈ FA, ∃ hi : i < 26163, IsConj tK (mk (xE i) (xE_mem hi)) ∧
      Qc (mk (xE i) (xE_mem hi)) ((mk (xE i) (xE_mem hi))⁻¹ * w) := by
    intro i hiF
    rw [hFA, Finset.mem_filter, Finset.mem_range] at hiF
    exact ⟨hiF.1, invol_conj (hord hiF.1), (qc_iff (hord hiF.1)).2 hiF.2⟩
  let f : FA → {x : P3 // IsConj tK x ∧ Qc x (x⁻¹ * w)} := fun i =>
    ⟨mk (xE i.1) (xE_mem (hmemFA i.1 i.2).1), (hmemFA i.1 i.2).2⟩
  have hb : Function.Bijective f := by
    refine ⟨fun s t h => ?_, fun x => ?_⟩
    · have hv : xE s.1 = xE t.1 := congrArg (fun y : {x : P3 // IsConj tK x ∧ Qc x (x⁻¹ * w)} =>
        ((y : P3) : Equiv.Perm (Fin 6156))) h
      exact Subtype.ext (xE_inj (hmemFA s.1 s.2).1 (hmemFA t.1 t.2).1 hv)
    · have hx2 : orderOf (x : P3) = 2 := by
        rw [orderOf_of_isConj x.2.1, Subgroup.orderOf_mk]
        exact tOrd
      obtain ⟨i, hi, he⟩ := rec_cover hx2
      have hxe : mk (xE i) (xE_mem hi) = (x : P3) := Subtype.ext he
      have hq := x.2.2
      rw [← hxe, qc_iff (hord hi)] at hq
      have hiF : i ∈ FA := by
        rw [hFA, Finset.mem_filter, Finset.mem_range]
        exact ⟨hi, hq⟩
      exact ⟨⟨i, hiF⟩, Subtype.ext hxe⟩
  rw [← Nat.card_eq_of_bijective f hb, Nat.card_eq_finsetCard, hcard]

theorem z19 : zE ^ 19 = 1 := by
  rw [← zOrd]
  exact pow_orderOf_eq_one zE

theorem ziRep : RepF 6156 PJ3W.ziP (zK : Equiv.Perm (Fin 6156))⁻¹ := by
  have e : (zK : Equiv.Perm (Fin 6156))⁻¹ = zE ^ 18 :=
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, z19])).symm
  rw [e]
  exact zRep.powF 18

theorem z2Rep : RepF 6156 PJ3Cn.z2P ((zK ^ 2 : P3) : Equiv.Perm (Fin 6156)) :=
  (zRep.comp zRep).congr (by rw [Subgroup.coe_pow, pow_two])

theorem zi2Rep : RepF 6156 PJ3W.zi2P ((zK ^ 2 : P3) : Equiv.Perm (Fin 6156))⁻¹ := by
  have e : ((zK ^ 2 : P3) : Equiv.Perm (Fin 6156))⁻¹ = zE ^ 17 := by
    rw [Subgroup.coe_pow]
    exact (eq_inv_of_mul_eq_one_left (by rw [← pow_add, z19])).symm
  rw [e]
  exact zRep.powF 17

theorem card_filt [Fintype P3] (p : P3 → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = Nat.card {x // p x} := by
  rw [← Fintype.card_subtype, Fintype.card_eq_nat_card]

theorem card_wordConds : Nat.card {y : P3 // WordConds tK y} = 3840 := by
  classical
  have : Fintype P3 := Fintype.ofFinite _
  have hz2 : orderOf (zK ^ 2) = 19 := by
    rw [Nat.Coprime.orderOf_pow (by rw [zK_ord]; norm_num), zK_ord]
  have hZr : ∀ g z : P3, orderOf (g * z * g⁻¹) = 19 ↔ orderOf z = 19 := fun g z => by
    rw [orderOf_conj]
  have hZ : ∀ x : P3, orderOf x = 19 ↔ ∃ j ∈ [zK, zK ^ 2], IsConj j x := fun x => by
    constructor
    · intro hx
      rcases ord19_conj hx with h | h
      · exact ⟨zK, List.mem_cons_self, h⟩
      · exact ⟨zK ^ 2, by simp, h⟩
    · rintro ⟨j, hj, hc⟩
      rw [orderOf_of_isConj hc]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact zK_ord
      · exact hz2
  have hZd : [zK, zK ^ 2].Pairwise fun i j => ¬IsConj i j := by
    simpa using not_conj_z
  have h := CFSG.KS.SylowCount.pair_count tK Qc qc_conj (fun x => orderOf x = 19) hZr
    [zK, zK ^ 2] hZ hZd
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, card_filt] at h
  have e1 : Nat.card {y : P3 // IsConj tK y} = 26163 := card_class tK cent_t (by norm_num)
  have e2 : Nat.card {y : P3 // IsConj zK y} = 2643840 := card_class zK cent_z (by norm_num)
  have e3 : Nat.card {y : P3 // IsConj (zK ^ 2) y} = 2643840 :=
    card_class (zK ^ 2) cent_zz2 (by norm_num)
  have e4 : Nat.card {x : P3 // IsConj tK x ∧ Qc x (x⁻¹ * zK)} = 19 :=
    scanW_card zK zRep ziRep PJ3W.scW_all (by decide)
  have e5 : Nat.card {x : P3 // IsConj tK x ∧ Qc x (x⁻¹ * zK ^ 2)} = 19 :=
    scanW_card (zK ^ 2) z2Rep zi2Rep PJ3W.scW2_all (by decide)
  have hx2 : orderOf tK = 2 := by
    rw [Subgroup.orderOf_mk]
    exact tOrd
  have e6 : Nat.card {y : P3 // orderOf (tK * y) = 19 ∧ Qc tK y} =
      Nat.card {y : P3 // WordConds tK y} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      rw [← wordConds_iff hx2]
      simp only [Qc, j3WConds, List.forall_mem_cons, List.not_mem_nil, false_implies,
        implies_true, and_true, j3WPat_prod, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, Bool.false_eq_true, ite_false, ite_true]
      have hxi : tK⁻¹ = tK := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hx2, pow_orderOf_eq_one]
      constructor
      · rintro ⟨h1, hy, h2, h3⟩
        have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
        have hyi : y⁻¹ = y * y := by
          rw [inv_eq_iff_mul_eq_one, ← pow_three]
          exact hy3
        refine ⟨hy, h1, ?_, h3⟩
        rw [hxi, hyi] at h2
        simpa only [mul_assoc] using h2
      · rintro ⟨hy, h1, h2, h3⟩
        have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
        have hyi : y⁻¹ = y * y := by
          rw [inv_eq_iff_mul_eq_one, ← pow_three]
          exact hy3
        refine ⟨h1, hy, ?_, h3⟩
        rw [hxi, hyi]
        simpa only [mul_assoc] using h2)
  rw [e1, e2, e3, e4, e5, e6] at h
  omega

theorem facts : (ordB PairJ3.bs (patW PairJ3.wA PairJ3.wB j3WPat) 17 = true) ∧
    (PairJ3.parCount (pairPred PairJ3.bs 3 PairJ3.wA j3WConds) PairJ3.blocks = 3840) := by
  refine ⟨?_, ?_⟩
  · have e : patW PairJ3.wA PairJ3.wB j3WPat =
        [PJ3.S 1, PJ3.S 1, PJ3.S 0, PJ3.S 1, PJ3.S 0, PJ3.S 1, PJ3.S 0].map (unpack 6156 13) := by
      rw [PJ3Check.wA_eq, PJ3Check.wB_eq]
      rfl
    rw [e]
    exact ordWK_sound PJ3WO.o17
  · classical
    have ha : orderOf (j3Gen 0) = 2 := j3_word_orders.1
    have h := card_eq_countW j3ChainArrays (by norm_num) PairJ3.chain_check.1 j3_groups
      (f := pairPred PairJ3.bs 3 PairJ3.wA j3WConds) (Pr := fun g => WordConds (j3Gen 0) g)
      (fun w g hw hg => by
        rw [pairPred, Bool.and_eq_true,
          CFSG.Sporadic.Schreier.ordB_iff j3_baseFaithful j3_bs_lt hw hg (by norm_num),
          condsOK_iff j3_baseFaithful j3_bs_lt repW_j3wA hw (j3Gen_mem 0 (by norm_num)) hg
            (by decide)]
        exact wordConds_iff ha)
    rw [show blocksOf 6156 (rawLevels 6156 j3StrongArrs PairJ3.baseArr) PairJ3.groups =
      PairJ3.blocks from rfl, ← PairJ3.parCount_eq] at h
    rw [← h, ← card_wordConds]
    set a : P3 := mk (j3Gen 0) (j3Gen_mem 0 (by norm_num)) with ha'
    have hao : orderOf a = 2 := by
      rw [ha', Subgroup.orderOf_mk]
      exact ha
    obtain ⟨c, hc⟩ := isConj_iff.1 (invol_conj hao)
    have e1 : Nat.card {g : P3 // WordConds (j3Gen 0) (g : Equiv.Perm (Fin 6156))} =
        Nat.card {y : P3 // WordConds a y} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun y =>
        (wordConds_map P3.subtype P3.subtype_injective a y))
    rw [e1, ← hc]
    refine (Nat.card_congr ((MulAut.conj c).toEquiv.subtypeEquiv fun y => ?_)).symm
    change WordConds tK y ↔ WordConds (MulAut.conj c tK) (MulAut.conj c y)
    exact (wordConds_map (MulAut.conj c).toMonoidHom (MulAut.conj c).injective tK y).symm

end J3

end CertificateChecks.KernelSporSch.PJ3W2283

end
