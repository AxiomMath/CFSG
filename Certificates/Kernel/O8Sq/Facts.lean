module

public import Certificates.Kernel.O8Sq.Lets
public import Certificates.Kernel.O8Sq.Count
public import Certificates.Kernel.O8Sq.Cnt4
public import Certificates.Kernel.AE6Q8.Facts
public import Certificates.Kernel.OmegaEight.E4O8CentGlue
public import CFSG.Certificates.Kernel.O8SqSound
public import CFSG.Certificates.Kernel.SporSch.ClsAllSound
public import CFSG.Certificates.Kernel.SporSch.J1CentSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8Sq

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.KC.PCent CFSG.KC.Misc.ArrEnum CertificateChecks.KernelO8 CertificateChecks.KernelO8.E4C
  CFSG.KC.O8Sq CFSG.ClassicalInvolution.O8Data CFSG.Sporadic.Schreier
open CFSG.KC.BfsPin (PP)

theorem ne_of_bIf {a b : Nat} (h : bIf(Nat.beq a b, false, true) = true) : a ≠ b := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem ne_of_not_beq {a b : Nat} (h : (!Nat.beq a b) = true) : a ≠ b := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem ap_pm {k : Nat} (hk : k < 10) : pm (AP.S k) = true := by
  by_cases h8 : k < 8
  · exact (root_facts h8).2.2.1
  · have hs := kStrC
    simp only [bAnd_iff] at hs
    rcases (show k = 8 ∨ k = 9 by omega) with rfl | rfl
    · exact hs.2.1
    · exact hs.2.2.1

theorem ap_pp {k : Nat} (hk : k < 10) : PP 360 9 (AP.S k) := e4c_pp (ap_pm hk)

theorem ap_toPerm {k : Nat} (hk : k < 10) : toPerm 360 9 (AP.S k) = gen k := by
  rw [e4c_toPerm (ap_pm hk), gen, gen_get hk]

theorem ap_inv {k : Nat} (hk : k < 8) : AP.S k = pinvS 360 9 (mask 9) (AP.S k) := by
  have hx := ch550106x
  simp only [bAnd_iff] at hx
  have hu := hx.1
  unfold classK at hu
  rw [Bool.and_eq_true] at hu
  exact Nat.eq_of_beq_eq_true (allN_spec hu.1 k hk)

theorem closure_ap_le_autT : Subgroup.closure (gens 360 9 AP.S 10) ≤ autT :=
  e4c_closure_le fun k hk => by rw [ap_toPerm hk]; exact gen_mem_autT hk

theorem x_pp {t : Nat} (ht : t < 3) : PP 360 9 (mainK t) := e4c_pp (main_ok (by omega)).2.2

theorem x_toPerm {t : Nat} (ht : t < 3) : toPerm 360 9 (mainK t) = mainPerm t := by
  obtain ⟨e, -, p⟩ := main_ok (by omega : t < 5)
  rw [mainPerm, e, e4c_toPerm p]

theorem pc9_eq {a b : Nat} (ha : PP 360 9 a) (hb : PP 360 9 b) :
    toPerm 360 9 (pc9 a b) = toPerm 360 9 a * toPerm 360 9 b := toPerm_mul ha hb

theorem pi9_eq {a : Nat} (ha : PP 360 9 a) : toPerm 360 9 (pi9 a) = (toPerm 360 9 a)⁻¹ :=
  toPerm_inv ha

theorem pc9_pp {a b : Nat} (ha : PP 360 9 a) (hb : PP 360 9 b) : PP 360 9 (pc9 a b) := ha.mul hb

theorem pi9_pp {a : Nat} (ha : PP 360 9 a) : PP 360 9 (pi9 a) := ha.inv

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

@[expose] noncomputable def sQ : Subgroup (Equiv.Perm (Fin 360)) :=
  Subgroup.closure (gens 360 9 sGK 4)

theorem sG_pp {k : Nat} (hk : k < 4) : PP 360 9 (sGK k) := ap_pp (k := 2 * k) (by omega)

theorem sQ_le_omegaT : sQ ≤ omegaT := by
  rw [← e4c_omegaT]
  exact e4c_closure_le fun k hk => gen_mem (G := AP.S) (k := 2 * k) (by omega)

theorem gen_eq_sQ : CFSG.KS.Raw.Orb.Gen 360 CertificateChecks.KernelAE6Q8.SA 4 = sQ := by
  unfold CFSG.KS.Raw.Orb.Gen sQ
  congr 1
  ext g
  constructor
  · rintro ⟨⟨j, hj⟩, rfl⟩
    refine ⟨j, hj, ?_⟩
    change toPerm 360 9 (AP.S (2 * j)) =
      CFSG.Monster.B.Co2.permOfArr 360 CertificateChecks.KernelAE6Q8.SA[j]!
    rw [CertificateChecks.KernelAE6Q8.SA_get (j := j) (by omega),
      CertificateChecks.KernelAE6Q8.gen_eq_AP j hj, e4c_toPerm (ap_pm (by omega))]
  · rintro ⟨j, hj, rfl⟩
    refine ⟨⟨j, hj⟩, ?_⟩
    change CFSG.Monster.B.Co2.permOfArr 360 CertificateChecks.KernelAE6Q8.SA[j]! =
      toPerm 360 9 (AP.S (2 * j))
    rw [CertificateChecks.KernelAE6Q8.SA_get (j := j) (by omega),
      CertificateChecks.KernelAE6Q8.gen_eq_AP j hj, e4c_toPerm (ap_pm (by omega))]

theorem card_sQ : Nat.card sQ = 2 ^ 12 := by
  rw [← gen_eq_sQ, CFSG.KS.SporSch.J1C.card_gen CertificateChecks.KernelAE6Q8.chainCK, ordK_SC]
  norm_num

theorem O8SqN_len : rcnt (CertificateChecks.KernelAE6Q8.SC.LR 0) ≤ O8SqN.CS.length * 64 := by
  decide

theorem O8SqN_sum : O8SqN.CS.sum = 3344 := by decide

theorem card_ord4 :
    Nat.card {g : Equiv.Perm (Fin 360) // g ∈ sQ ∧ orderOf g = 4} = 3344 := by
  rw [← gen_eq_sQ, CFSG.KS.SporSch.CAll.card_ord_eq_sum CertificateChecks.KernelAE6Q8.chainCK
    (by norm_num) O8SqN_len O8SqN.hc, O8SqN_sum]

theorem repW_facts {j : Nat} (hj : j < 57) :
    PP 360 9 (repW j) ∧ toPerm 360 9 (repW j) ∈ sQ ∧ orderOf (toPerm 360 9 (repW j)) = 4 := by
  have hl := ch272020lt
  simp only [bAnd_iff] at hl
  obtain ⟨hp, hm⟩ : PP 360 9 (repW j) ∧ toPerm 360 9 (repW j) ∈ sQ :=
    wordK_sound ch550106sz (fun k hk => sG_pp hk) _ (e4c_lets hl.1 j)
  refine ⟨hp, hm, ?_⟩
  have ho := allN_spec ch272020o j hj
  rw [strictB_eq'] at ho
  simp only [bAnd_iff] at ho
  have e1 := congrArg (toPerm 360 9) (Nat.eq_of_beq_eq_true ho.1)
  have hrr := pc9_pp hp hp
  rw [pc9_eq hrr hrr, pc9_eq hp hp, e4c_pid] at e1
  have hne : toPerm 360 9 (repW j) ^ 2 ≠ 1 := by
    intro e
    refine ne_of_bIf ho.2 (toPerm_injective hrr (CFSG.KC.BfsPin.PP.id ch550106sz) ?_)
    rw [pc9_eq hp hp, e4c_pid, ← pow_two, e]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 := orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hne)
    (by rw [show 2 ^ (1 + 1) = 4 from rfl, show (4 : Nat) = 2 * 2 from rfl, pow_mul, pow_two,
      pow_two]; exact e1)
  simpa using h4

theorem cover4 {c : Equiv.Perm (Fin 360)} (hc : c ∈ sQ) (ho : orderOf c = 4) :
    ∃ j < 57, ∃ s ∈ sQ, s * toPerm 360 9 (repW j) * s⁻¹ = c := by
  classical
  have hf := ch272020fw
  rw [Bool.and_eq_true] at hf
  obtain ⟨hF, hlen⟩ := hf
  obtain ⟨hcard, hmem⟩ := forestK_card (fun k hk => sG_pp hk) (fun j hj => (repW_facts hj).1) hF
  rw [Nat.eq_of_beq_eq_true hlen] at hcard
  set F := ((FW.map Prod.fst).map (toPerm 360 9)).toFinset
  set T := Finset.univ.filter fun g : Equiv.Perm (Fin 360) => g ∈ sQ ∧ orderOf g = 4
  have hT : T.card = 3344 := by
    rw [← card_ord4, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hFT : F ⊆ T := by
    intro s hs
    obtain ⟨j, hj, g, hg, rfl⟩ := hmem s hs
    obtain ⟨-, hr, hro⟩ := repW_facts hj
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, sQ.mul_mem (sQ.mul_mem hg hr) (sQ.inv_mem hg), ?_⟩
    rw [show g * toPerm 360 9 (repW j) * g⁻¹ = MulAut.conj g (toPerm 360 9 (repW j)) from rfl,
      MulEquiv.orderOf_eq, hro]
  have hEq : F = T := Finset.eq_of_subset_of_card_le hFT (by rw [hT, hcard])
  have hcT : c ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ _, hc, ho⟩
  rw [← hEq] at hcT
  obtain ⟨j, hj, s, hs, e⟩ := hmem c hcT
  exact ⟨j, hj, s, hs, e⟩

theorem wit_rep {j : Nat} (hj : j < 57) :
    ∃ g ∈ omegaT, WitP (toPerm 360 9 (repW j)) g := by
  have hl := ch272020lt
  simp only [bAnd_iff] at hl
  have hw0 := ch272020w
  rw [Bool.and_eq_true] at hw0
  have hw := allN_spec hw0.2 j hj
  have hW := allN_spec ch272020ww j hj
  simp only [bAnd_iff] at hW
  obtain ⟨hk, ho, hpv⟩ := hW
  obtain ⟨hpr, -, -⟩ := repW_facts hj
  set h := wordK 360 9 AP.S (HW.getD j []).reverse with hhdef
  have hlet : ∀ c ∈ (HW.getD j []).reverse, c < 10 := fun c hc =>
    e4c_lets hl.2.1 j c (List.mem_reverse.1 hc)
  obtain ⟨hph, hhm⟩ := wordK_sound ch550106sz (fun k hk => ap_pp hk) _ hlet
  have hhA : toPerm 360 9 h ∈ autT := closure_ap_le_autT hhm
  have hpv' : PP 360 9 (wO (wdJ j)) := e4c_pp hpv
  have hv : toPerm 360 9 (wO (wdJ j)) ∈ omegaT := e4c_word_mem hk ho hpv
  unfold witJ at hw
  rw [strictB_eq', strictB_eq', Bool.and_eq_true] at hw
  have hwo := hw.2
  change witOneK (repW j) h (wO (wdJ j)) = true at hwo
  unfold witOneK at hwo
  rw [strictB_eq', strictB_eq', strictB_eq'] at hwo
  simp only [Bool.and_eq_true] at hwo
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hwo
  set r := repW j
  set v := wO (wdJ j)
  have hpg : PP 360 9 (pc9 h (pc9 v (pi9 h))) := pc9_pp hph (pc9_pp hpv' (pi9_pp hph))
  have hpz : PP 360 9 (pc9 r r) := pc9_pp hpr hpr
  set g := pc9 h (pc9 v (pi9 h))
  have hpy : PP 360 9 (pc9 r (pc9 g (pc9 r (pi9 g)))) :=
    pc9_pp hpr (pc9_pp hpg (pc9_pp hpr (pi9_pp hpg)))
  have eg : toPerm 360 9 g = toPerm 360 9 h * toPerm 360 9 v * (toPerm 360 9 h)⁻¹ := by
    rw [pc9_eq hph (pc9_pp hpv' (pi9_pp hph)), pc9_eq hpv' (pi9_pp hph), pi9_eq hph, mul_assoc]
  have ey : toPerm 360 9 (pc9 r (pc9 g (pc9 r (pi9 g)))) =
      toPerm 360 9 r * (toPerm 360 9 g * toPerm 360 9 r * (toPerm 360 9 g)⁻¹) := by
    rw [pc9_eq hpr (pc9_pp hpg (pc9_pp hpr (pi9_pp hpg))), pc9_eq hpg (pc9_pp hpr (pi9_pp hpg)),
      pc9_eq hpr (pi9_pp hpg), pi9_eq hpg, mul_assoc (toPerm 360 9 g)]
  have ez : toPerm 360 9 (pc9 r r) = toPerm 360 9 r * toPerm 360 9 r := pc9_eq hpr hpr
  have hid : PP 360 9 (pidn 360 9) := CFSG.KC.BfsPin.PP.id ch550106sz
  refine ⟨toPerm 360 9 g, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eg]
    exact (conj_mem_omegaT hhA).1 hv
  · have e := congrArg (toPerm 360 9) (Nat.eq_of_beq_eq_true h1)
    rwa [pc9_eq hpg hpz, pc9_eq hpz hpg, ez] at e
  · have e := congrArg (toPerm 360 9) (Nat.eq_of_beq_eq_true h2)
    rwa [pc9_eq hpy hpy, ey, toPerm_pidn ch550106sz] at e
  · intro e
    refine ne_of_not_beq h3 (toPerm_injective hpy hid ?_)
    rw [ey, e, toPerm_pidn ch550106sz]
  · intro e
    refine ne_of_not_beq h4 (toPerm_injective hpy hpz ?_)
    rw [ey, e, ez]

theorem o8sq_wit :
    ∀ c ∈ omegaT, orderOf c = 4 → ∃ g ∈ omegaT, WitP c g := by
  intro c hc ho
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hkc⟩ := exists_conj_mem_of_card sQ_le_omegaT (p := 2) (k := 12) (m := 42525)
    (e := 2) card_sQ (by rw [card_omegaT]; norm_num) (by norm_num) hc (by rw [ho]; norm_num)
  have ho' : orderOf (k * c * k⁻¹) = 4 := by
    rw [show k * c * k⁻¹ = MulAut.conj k c from rfl, MulEquiv.orderOf_eq, ho]
  obtain ⟨j, hj, s, hs, hsr⟩ := cover4 hkc ho'
  obtain ⟨g, hg, hW⟩ := wit_rep hj
  have hq : k⁻¹ * s ∈ omegaT := omegaT.mul_mem (omegaT.inv_mem hk) (sQ_le_omegaT hs)
  refine ⟨(k⁻¹ * s) * g * (k⁻¹ * s)⁻¹, omegaT.mul_mem (omegaT.mul_mem hq hg) (omegaT.inv_mem hq),
    ?_⟩
  have e : c = (k⁻¹ * s) * toPerm 360 9 (repW j) * (k⁻¹ * s)⁻¹ := by
    calc c = k⁻¹ * (k * c * k⁻¹) * k := by group
      _ = k⁻¹ * (s * toPerm 360 9 (repW j) * s⁻¹) * k := by rw [hsr]
      _ = _ := by group
  rw [e]
  exact hW.conj _

theorem conjClass_eq_clsF (H : Subgroup (Equiv.Perm (Fin 360))) (a : Equiv.Perm (Fin 360)) :
    (conjClass H a).ncard = (clsF H a).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  rw [Finset.mem_coe, mem_clsF]
  rfl

theorem card_clsF_mul (a : Equiv.Perm (Fin 360)) :
    (clsF omegaT a).card * Nat.card (omegaT ⊓ Subgroup.centralizer {a} :
      Subgroup (Equiv.Perm (Fin 360))) = 174182400 := by
  rw [← conjClass_eq_clsF, ← card_omegaT]
  exact ncard_conjClass_mul_card omegaT a

theorem rx_facts : (∀ r ∈ RX, PP 360 9 r.1) ∧
    (RX.map Prod.fst).Nodup ∧ ∀ r ∈ RX, toPerm 360 9 r.1 ∈ clsF omegaT (mainPerm 0) := by
  have hx := ch550106x
  simp only [bAnd_iff] at hx
  have hu := hx.1
  unfold classK at hu
  rw [Bool.and_eq_true] at hu
  obtain ⟨hI, ho⟩ := hu
  have hA : ∀ k < 8, ∀ y, conjI 360 9 AP.S AP.S k y = conjAct 360 9 AP.S k y := by
    intro k hk y
    have e := Nat.eq_of_beq_eq_true (allN_spec hI k hk)
    unfold conjI conjAct
    rw [← e]
  obtain ⟨hs, hr⟩ := orbRecK_sound ho
  have hreach := fun {y} (h : Reach (conjI 360 9 AP.S AP.S) 8 (mainK 0) y) =>
    reach_conj (fun k hk => ap_pp (by omega)) hA (x_pp (by norm_num)) h
  refine ⟨fun r hr' => (hreach (hr r hr')).1, hs.imp (fun h => Nat.ne_of_lt h), fun r hr' => ?_⟩
  obtain ⟨-, g, hg, he⟩ := hreach (hr r hr')
  rw [e4c_omegaT] at hg
  rw [x_toPerm (by norm_num)] at he
  exact mem_clsF.2 ⟨g, hg, he.symm⟩

theorem card_cls0 : (clsF omegaT (mainPerm 0)).card = 1575 := by
  have h := card_clsF_mul (mainPerm 0)
  rw [← e4c_H0.1, e4c_H0.2] at h
  omega

theorem rx_eq :
    ((RX.map Prod.fst).map (toPerm 360 9)).toFinset = clsF omegaT (mainPerm 0) := by
  obtain ⟨hp, hnd, hm⟩ := rx_facts
  refine Finset.eq_of_subset_of_card_le (fun s hs => ?_) ?_
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs)
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact hm r hr
  · rw [card_cls0, List.toFinset_card_of_nodup, List.length_map, List.length_map]
    · have hx := ch550106x
      simp only [bAnd_iff] at hx
      rw [Nat.eq_of_beq_eq_true hx.2]
    · refine List.Nodup.map_on (fun x hx y hy e => ?_) hnd
      obtain ⟨rx, hrx, rfl⟩ := List.mem_map.1 hx
      obtain ⟨ry, hry, rfl⟩ := List.mem_map.1 hy
      exact toPerm_injective (hp rx hrx) (hp ry hry) e

theorem card_cls0_comm {t : Nat} (ht : t < 3) :
    ((clsF omegaT (mainPerm 0)).filter fun x => x * mainPerm t = mainPerm t * x).card =
      cntCommK 360 9 (mainK t) RX := by
  obtain ⟨hp, hnd, -⟩ := rx_facts
  rw [← rx_eq, ← x_toPerm ht]
  exact card_filter_comm_of_cntCommK (x_pp ht) hp hnd

theorem le_card_clst_comm {t : Nat} (ht : t < 3) {nr : Nat}
    {RT : List Nat} {P : List (List Nat)} {F : List Rec}
    (hlet : e4Lets 8 P = true)
    (hroot : ∀ j < nr, RT.getD j 0 = cpathK 360 9 AP.S (mainK t) (P.getD j []) ∧
      Nat.beq (pcomp 360 9 (mask 9) (RT.getD j 0) (mainK 0))
        (pcomp 360 9 (mask 9) (mainK 0) (RT.getD j 0)) = true)
    (hF : forestK 360 9 g0K gi0K 6 (fun j => RT.getD j 0) nr F = true) :
    F.length ≤ ((clsF omegaT (mainPerm t)).filter fun y => y * mainPerm 0 = mainPerm 0 * y).card := by
  classical
  have hpm := e4c_pm.1
  have hRT : ∀ j < nr, PP 360 9 (RT.getD j 0) ∧ toPerm 360 9 (RT.getD j 0) ∈
      clsF omegaT (mainPerm t) ∧
      toPerm 360 9 (RT.getD j 0) * mainPerm 0 = mainPerm 0 * toPerm 360 9 (RT.getD j 0) := by
    intro j hj
    obtain ⟨e, hc⟩ := hroot j hj
    obtain ⟨hp, g, hg, hge⟩ := cpathK_sound (fun k hk => ap_pp (by omega)) (fun k hk => ap_inv hk)
      (P.getD j []) (e4c_lets hlet j) (x_pp ht)
    rw [← e] at hp hge
    have hx0 := x_pp (t := 0) (by norm_num)
    refine ⟨hp, ?_, ?_⟩
    · rw [e4c_omegaT] at hg
      rw [x_toPerm ht] at hge
      exact mem_clsF.2 ⟨g, hg, hge.symm⟩
    · rw [← x_toPerm (t := 0) (by norm_num)]
      exact (toPerm_comm_iff hp hx0).1 hc
  obtain ⟨hcard, hmem⟩ := forestK_card hpm (fun j hj => (hRT j hj).1) hF
  rw [← hcard]
  refine Finset.card_le_card fun s hs => ?_
  obtain ⟨j, hj, g, hg, rfl⟩ := hmem s hs
  obtain ⟨-, hcl, hcm⟩ := hRT j hj
  have hgH : g ∈ e4H0 := hg
  rw [e4c_H0.1] at hgH
  obtain ⟨hgO, hgc⟩ := Subgroup.mem_inf.1 hgH
  have hgc' := Subgroup.mem_centralizer_singleton_iff.1 hgc
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · obtain ⟨d, hd, hde⟩ := mem_clsF.1 hcl
    exact mem_clsF.2 ⟨g * d, omegaT.mul_mem hgO hd, by rw [hde]; group⟩
  · have hgi : g⁻¹ * mainPerm 0 = mainPerm 0 * g⁻¹ :=
      calc g⁻¹ * mainPerm 0 = g⁻¹ * (mainPerm 0 * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * mainPerm 0) * g⁻¹ := by rw [hgc']
        _ = mainPerm 0 * g⁻¹ := by group
    calc g * toPerm 360 9 (RT.getD j 0) * g⁻¹ * mainPerm 0
        = g * toPerm 360 9 (RT.getD j 0) * (g⁻¹ * mainPerm 0) := by group
      _ = g * toPerm 360 9 (RT.getD j 0) * (mainPerm 0 * g⁻¹) := by rw [hgi]
      _ = g * (toPerm 360 9 (RT.getD j 0) * mainPerm 0) * g⁻¹ := by group
      _ = g * (mainPerm 0 * toPerm 360 9 (RT.getD j 0)) * g⁻¹ := by rw [hcm]
      _ = g * mainPerm 0 * toPerm 360 9 (RT.getD j 0) * g⁻¹ := by group
      _ = mainPerm 0 * g * toPerm 360 9 (RT.getD j 0) * g⁻¹ := by rw [hgc']
      _ = mainPerm 0 * (g * toPerm 360 9 (RT.getD j 0) * g⁻¹) := by group

theorem card_cent_le {t : Nat} (ht : t < 3) {a b M : Nat}
    (hb : b ≤ ((clsF omegaT (mainPerm t)).filter fun y => y * mainPerm 0 = mainPerm 0 * y).card)
    (ha : cntCommK 360 9 (mainK t) RX = a) (ha0 : 0 < a)
    (hM : 174182400 * a ≤ M * (1575 * b)) :
    Nat.card (omegaT ⊓ Subgroup.centralizer {mainPerm t} : Subgroup (Equiv.Perm (Fin 360))) ≤ M := by
  have hd := card_mul_card_filter_comm omegaT (mainPerm 0) (mainPerm t)
  rw [card_cls0, card_cls0_comm ht, ha] at hd
  have hc := card_clsF_mul (mainPerm t)
  set C := Nat.card (omegaT ⊓ Subgroup.centralizer {mainPerm t} : Subgroup (Equiv.Perm (Fin 360)))
  set B := (clsF omegaT (mainPerm t)).card
  set BC := ((clsF omegaT (mainPerm t)).filter fun y => y * mainPerm 0 = mainPerm 0 * y).card
  have hpos : 0 < 1575 * b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h
      have : 0 < 174182400 * a := by positivity
      omega
    · positivity
  have key : C * (1575 * b) ≤ M * (1575 * b) :=
    calc C * (1575 * b) ≤ C * (1575 * BC) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)
      _ = C * (B * a) := by rw [hd]
      _ = (B * C) * a := by ring
      _ = 174182400 * a := by rw [hc]
      _ ≤ M * (1575 * b) := hM
  exact Nat.le_of_mul_le_mul_right key hpos

theorem le_card_cent {t : Nat} (ht : t < 3) {G : List Nat}
    {L : List (Nat × List Nat × List (List Nat) × List Rec)}
    (hg : (Nat.beq G.length 6 && allN 3 (fun j =>
      Nat.beq (G.getD j 0) (wO ((centGens.getD t []).getD j [])) &&
        Nat.beq (G.getD (Nat.add j 3) 0) (pinvS 360 9 (mask 9) (G.getD j 0))) &&
      allN 6 (fun k => Nat.beq (pcomp 360 9 (mask 9) (G.getD k 0) (mainK t))
        (pcomp 360 9 (mask 9) (mainK t) (G.getD k 0)))) = true)
    (hw : allN 3 (fun j => bAnd(lettersK 17 ((centGens.getD t []).getD j []),
      CFSG.Monster.B.Co2.Native.lettersOK 17 ((centGens.getD t []).getD j []))) = true)
    (hp : allN 6 (fun k => permB 360 9 (G.getD k 0)) = true)
    (hl : stabLowK 360 9 (fun k => G.getD k 0) 6 L = true) :
    (L.map fun lv => lv.2.2.2.length).prod ≤
      Nat.card (omegaT ⊓ Subgroup.centralizer {mainPerm t} : Subgroup (Equiv.Perm (Fin 360))) := by
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨-, hgw⟩, hgc⟩ := hg
  have hpp : ∀ k < 6, PP 360 9 (G.getD k 0) := fun k hk => e4c_pp (allN_spec hp k hk)
  refine (prod_le_card_of_stabLowK ch550106sz hpp hl).trans (Subgroup.card_le_of_le ?_)
  refine e4c_closure_le fun k hk => Subgroup.mem_inf.2 ⟨?_, e4c_mem_cent ?_⟩
  · have h3 : ∀ j < 3, toPerm 360 9 (G.getD j 0) ∈ omegaT := by
      intro j hj
      have e := allN_spec hgw j hj
      rw [Bool.and_eq_true] at e
      have ew := allN_spec hw j hj
      simp only [bAnd_iff] at ew
      have hpj := allN_spec hp j (by omega)
      rw [Nat.eq_of_beq_eq_true e.1] at hpj ⊢
      exact e4c_word_mem ew.1 ew.2 hpj
    by_cases hk3 : k < 3
    · exact h3 k hk3
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      have e := allN_spec hgw j (by omega)
      rw [Bool.and_eq_true] at e
      have e2 : G.getD (j + 3) 0 = pinvS 360 9 (mask 9) (G.getD j 0) := Nat.eq_of_beq_eq_true e.2
      rw [e2, toPerm_inv (hpp j (by omega))]
      exact omegaT.inv_mem (h3 j (by omega))
  · rw [← x_toPerm ht]
    exact (toPerm_comm_iff (hpp k hk) (x_pp ht)).1 (allN_spec hgc k hk)

theorem o8sq_card1 :
    Nat.card (omegaT ⊓ Subgroup.centralizer {mainPerm 1} : Subgroup (Equiv.Perm (Fin 360))) =
      46080 := by
  have hgw := ch272020gw
  simp only [bAnd_iff] at hgw
  have hl := ch272020l1
  rw [Bool.and_eq_true] at hl
  have hlow := le_card_cent (t := 1) (by norm_num) ch272020g1 hgw.1 hgw.2.2.1 hl.1
  rw [Nat.eq_of_beq_eq_true hl.2] at hlow
  have hlt := ch272020lt
  simp only [bAnd_iff] at hlt
  have hf := ch272020f1
  rw [Bool.and_eq_true] at hf
  have hb := le_card_clst_comm (t := 1) (by norm_num) (nr := 3) hlt.2.2.1 (fun j hj => by
    have e := allN_spec ch272020r1 j hj
    rw [Bool.and_eq_true] at e
    exact ⟨Nat.eq_of_beq_eq_true e.1, e.2⟩) hf.1
  rw [Nat.eq_of_beq_eq_true hf.2] at hb
  have hup := card_cent_le (t := 1) (by norm_num) (M := 46080) hb
    (Nat.eq_of_beq_eq_true ch272020k1) (by norm_num) (by norm_num)
  omega

theorem o8sq_card2 :
    Nat.card (omegaT ⊓ Subgroup.centralizer {mainPerm 2} : Subgroup (Equiv.Perm (Fin 360))) =
      3072 := by
  have hgw := ch272020gw
  simp only [bAnd_iff] at hgw
  have hl := ch272020l2
  rw [Bool.and_eq_true] at hl
  have hlow := le_card_cent (t := 2) (by norm_num) ch272020g2 hgw.2.1 hgw.2.2.2 hl.1
  rw [Nat.eq_of_beq_eq_true hl.2] at hlow
  have hlt := ch272020lt
  simp only [bAnd_iff] at hlt
  have hf := ch272020f2
  rw [Bool.and_eq_true] at hf
  have hb := le_card_clst_comm (t := 2) (by norm_num) (nr := 5) hlt.2.2.2 (fun j hj => by
    have e := allN_spec ch272020r2 j hj
    rw [Bool.and_eq_true] at e
    exact ⟨Nat.eq_of_beq_eq_true e.1, e.2⟩) hf.1
  rw [Nat.eq_of_beq_eq_true hf.2] at hb
  have hup := card_cent_le (t := 2) (by norm_num) (M := 3072) hb
    (Nat.eq_of_beq_eq_true ch272020k2) (by norm_num) (by norm_num)
  omega

theorem o8sq_card0 :
    Nat.card (omegaT ⊓ Subgroup.centralizer {mainPerm 0} : Subgroup (Equiv.Perm (Fin 360))) =
      110592 := by
  rw [← e4c_H0.1, e4c_H0.2]

end CertificateChecks.KernelO8Sq

end
