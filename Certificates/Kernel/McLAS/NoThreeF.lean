module

public import Certificates.Kernel.McLAS.NoThreeData
public import Certificates.Kernel.Sporadic.OddCore.MNF
public import Certificates.Kernel.Sporadic.OddCore.McLTwoF
public import CFSG.Sporadic.SmallOddCore.CentQueue
public import CFSG.Sporadic.SmallOddCore.McLLocal
public import CFSG.Sporadic.Recognition.McLASEnum
public import CFSG.Sporadic.Recognition.McLNoThreeKlein
import Certificates.Kernel.McLAS.NoThreeBase
import Certificates.Kernel.McLAS.NoThreeChk0
import Certificates.Kernel.McLAS.NoThreeChk1
import Certificates.Kernel.McLAS.NoThreeChk2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLAS.NoThr

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.KS.McLNT CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Recognition.McLAS
open CertificateChecks.KernelSpor CFSG.KC.BfsPin

abbrev Cn (p : Nat) : Prop := canonK 275 9 (mask 9) (275 * 9) p = true

abbrev RP (p : Nat) (g : Equiv.Perm (Fin 275)) : Prop := Rep 275 (tabT (unpack 275 9 p)) g

theorem cn_pc {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) := canonK_pcomp hp hq

theorem rp_pc {p q : Nat} {g h : Equiv.Perm (Fin 275)} (hp : Cn p) (hq : Cn q) (hg : RP p g)
    (hh : RP q h) : RP (pc p q) (g * h) := by
  unfold RP pc
  rw [← compT_unpack hp hq]
  exact Rep.compT hg hh

theorem cn_id : Cn idP := MNd.hidc

theorem rp_id : RP idP 1 := by
  unfold RP idP
  rw [← MNd.hid]
  exact Rep.idT (by norm_num)

theorem beq_iff {p q : Nat} {g h : Equiv.Perm (Fin 275)} (hp : Cn p) (hq : Cn q) (hg : RP p g)
    (hh : RP q h) : Nat.beq p q = true ↔ g = h := by
  rw [← tblEq_unpack hp hq]
  exact CFSG.Sporadic.SmallOddCore.tblEq_iff_eq hg hh

theorem rp_perm {p r : Nat} (hp : Cn p) (hr : Cn r) (h : invEqK 275 9 (mask 9) (275 * 9) p r = true) :
    RP p (tp 275 (tabT (unpack 275 9 p))) ∧ RP r (tp 275 (tabT (unpack 275 9 p)))⁻¹ := by
  have h1 := rep_tp (permOK_unpack hp h)
  refine ⟨h1, ?_⟩
  have h2 := rep_invT h1 (by rw [invT_unpack (by norm_num) h]; exact invOK_unpack hp hr h)
  rwa [invT_unpack (by norm_num) h] at h2

theorem blt_lt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem lt_blt {a b : Nat} (h : a < b) : Nat.blt a b = true := Nat.ble_eq_true_of_le h

theorem pwK_succ (e x : Nat) : pwK (e + 1) x = pc x (pwK e x) := by
  change strictN (pwK e x) (fun a => pc x a) = _
  rw [strictN_app']

theorem rp_pwK {x : Nat} {g : Equiv.Perm (Fin 275)} (hx : Cn x) (hg : RP x g) :
    ∀ e, Cn (pwK e x) ∧ RP (pwK e x) (g ^ e)
  | 0 => ⟨cn_id, by rw [pow_zero]; exact rp_id⟩
  | e + 1 => by
    obtain ⟨h1, h2⟩ := rp_pwK hx hg e
    rw [pwK_succ, pow_succ']
    exact ⟨cn_pc hx h1, rp_pc hx h1 hg h2⟩

theorem bool_three {a b c : Bool}
    (h : bAnd(bIf(a, false, true), bAnd(b, bIf(c, false, true))) = true) :
    a = false ∧ b = true ∧ c = false := by
  cases a <;> cases b <;> cases c <;> first | exact ⟨rfl, rfl, rfl⟩ | exact absurd h (by decide)

theorem witK_sound {G GI X A AI e m : Nat} {g x a : Equiv.Perm (Fin 275)} (hG : Cn G)
    (hGI : Cn GI) (hX : Cn X) (hA : Cn A) (hAI : Cn AI) (rG : RP G g) (rGI : RP GI g⁻¹)
    (rX : RP X x) (rA : RP A a) (rAI : RP AI a⁻¹) (h : witK G GI X A AI e m = true) :
    ¬ (g * x * g⁻¹ * (a * (g * x * g⁻¹) * a⁻¹)) ^ 729 = 1 := by
  unfold witK at h
  simp only [strictB_eq''] at h
  have cY := cn_pc hG (cn_pc hX hGI)
  have rY := rp_pc hG (cn_pc hX hGI) rG (rp_pc hX hGI rX rGI)
  have cZ := cn_pc cY (cn_pc hA (cn_pc cY hAI))
  have rZ := rp_pc cY (cn_pc hA (cn_pc cY hAI)) rY (rp_pc hA (cn_pc cY hAI) rA (rp_pc cY hAI rY rAI))
  obtain ⟨cV, rV⟩ := rp_pwK cZ rZ e
  obtain ⟨-, rVm⟩ := rp_pwK cV rV m
  obtain ⟨h1, h2, h3⟩ := bool_three h
  have hv1 : ¬ (g * (x * g⁻¹) * (a * (g * (x * g⁻¹) * a⁻¹))) ^ e = 1 := fun hv =>
    Bool.false_ne_true (h1.symm.trans ((beq_iff cV cn_id rV rp_id).2 hv))
  have hvm := (beq_iff (rp_pwK cV rV m).1 cn_id rVm rp_id).1 h2
  have h3' : ¬ 3 ∣ m := fun hd => Nat.ne_of_beq_eq_false h3 (Nat.mod_eq_zero_of_dvd hd)
  intro h729
  apply hv1
  have hcop : Nat.Coprime 729 m := by
    have h3c : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3'
    have := Nat.Coprime.pow_left 6 h3c
    norm_num at this
    exact this
  have hz : (g * (x * g⁻¹) * (a * (g * (x * g⁻¹) * a⁻¹))) ^ 729 = 1 := by
    simpa only [mul_assoc] using h729
  set v := (g * (x * g⁻¹) * (a * (g * (x * g⁻¹) * a⁻¹))) ^ e
  have hv729 : v ^ 729 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  rw [← orderOf_eq_one_iff]
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hv729) (orderOf_dvd_of_pow_eq_one hvm)
  rw [Nat.Coprime.gcd_eq_one hcop] at hd
  exact Nat.dvd_one.1 hd

@[expose] noncomputable def xi (i : Nat) : Nat :=
  nIf(Nat.blt i (nat_lit 112), MN.Q1a.T i, MN.Q1e.T (Nat.sub i (nat_lit 112)))

theorem noThrK_spec {j i : Nat} (h : noThrK j i = true) :
    ∃ a e m : Nat, a < 128 ∧
      witK (NoThrG j) (NoThrGI j) (xi i) (McLTwoS.T a) (McLTwoEI a) e m = true := by
  unfold noThrK ntItemK at h
  simp only [strictB_eq''] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨_, _, _, blt_lt h1, h2⟩

theorem base_facts : r32 NoThrJ 0 < 128 ∧ r32 NoThrJ 1 < 128 ∧ MN.Q1a.cnt = 112 ∧
    MN.Q1e.cnt = 1120 ∧ ∀ j < 3, Cn (NoThrG j) ∧ Cn (NoThrGI j) ∧
      invEqK 275 9 (mask 9) (275 * 9) (NoThrG j) (NoThrGI j) = true ∧
      siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) CertificateChecks.KernelCensus.McLC.LR
        CertificateChecks.KernelCensus.McLC.TRI CertificateChecks.KernelCensus.McLC.BP 5 0
        (NoThrG j) = true ∧
      Nat.beq (pc (NoThrG j) (pc (McLCT.F 4) (NoThrGI j))) (noThrU j) = true := by
  have h := noThr_base
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨blt_lt h1, blt_lt h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, fun j hj => ?_⟩
  have := allN_spec h5 j hj
  simp only [bAnd_iff] at this
  exact this

theorem xi_lo {i : Nat} (hi : i < 112) : xi i = MN.Q1a.T i := by
  unfold xi
  rw [show Nat.blt i 112 = true from lt_blt hi]

theorem xi_hi (k : Nat) : xi (112 + k) = MN.Q1e.T k := by
  unfold xi
  have h : Nat.blt (112 + k) 112 = false := by
    cases hb : Nat.blt (112 + k) 112
    · rfl
    · exact absurd (blt_lt hb) (by omega)
  rw [h]
  change MN.Q1e.T (112 + k - 112) = _
  rw [Nat.add_sub_cancel_left]

theorem hRec_get {cnt k : Nat} {T PL : Nat → Nat} (hk : k < cnt) :
    (hRec 275 9 cnt T PL).1[k]! = tabT (unpack 275 9 (T k)) := by
  rw [getElem!_pos _ k (by rw [hRec_size]; exact hk)]
  simp only [hRec, Array.getElem_ofFn]

theorem cg_eq : (MNd.cgL 5 2).toArray = [mclCentTbl 5, mclCentTbl 6].toArray := by
  simp [MNd.cgL, List.range_succ]

theorem orderOf_conj' (c x : Equiv.Perm (Fin 275)) : orderOf (c * x * c⁻¹) = orderOf x := by
  have h := MulEquiv.orderOf_eq (MulAut.conj c) x
  rwa [MulAut.conj_apply] at h

theorem cent_three
    {x : Equiv.Perm (Fin 275)} (hx : x ∈ mclCt)
    (h3 : orderOf x = 3) : ∃ i < 1232, RP (xi i) x := by
  obtain ⟨-, -, ha, he, -⟩ := base_facts
  obtain ⟨r, hr, hrep0, hcen0, hpr0, hcg0, hodd0⟩ : ∃ r ∈ mclRows, r.rep = mclCentTbl 4 ∧
      r.centOrder = 40320 ∧ r.oddPrimes = [3, 5, 7] ∧ r.centGens = [mclCentTbl 5, mclCentTbl 6] ∧
      r.odd.map (fun s => (s.rep, s.prime)) = [(mclCentTbl 7, 3), (mclCentTbl 9, 7),
        (mclCentTbl 11, 7), (mclCentTbl 13, 5), (mclCentTbl 15, 3)] := by
    rw [mclRows]
    exact ⟨_, List.mem_cons_self, rfl, rfl, rfl, rfl, rfl⟩
  have hcd := mcl_centDataOK
  unfold centDataOK at hcd
  simp only [Bool.and_eq_true, List.all_eq_true] at hcd
  obtain ⟨⟨-, hcl⟩, -⟩ := hcd
  have h0 := hcl (r, conjClosureH 275 mclPGTbls mclPGInvTbls r.rep 120000)
    (List.mem_map.2 ⟨r, hr, rfl⟩)
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at h3; omega
  obtain ⟨s, hs, hord, ⟨c, -, hyc⟩, k, hk, hrep⟩ := classOK_queue_cover mcl_groupData h0
    (by rw [hrep0, hcen0]; exact mclT0_facts.2.2.2.1) (by rw [hrep0]; exact hx) hx1
    ⟨3, by rw [hpr0]; simp, by rw [← h3]; exact pow_orderOf_eq_one x⟩
  have hsm := List.mem_map_of_mem (f := fun s : OddRow => (s.rep, s.prime)) hs
  rw [hodd0] at hsm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hsm
  rw [hcg0] at hk hrep
  have hpr : ∀ (q p : Nat), q < 30 → 0 < p → s.rep = mclCentTbl q → s.prime = p → p = 3 := by
    intro q p hq hp hsq hsp
    rw [hsq, hsp] at hord
    rw [hsq] at hyc
    have := (ordTest_iff_perm (rep_tp (MNd.permF hq)) hp).1 hord
    rw [← this, ← orderOf_conj' c, ← hyc, h3]
  rcases hsm with ⟨h1, -⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, -⟩
  · rw [h1, ← cg_eq, (MNd.recQ1a).1] at hk hrep
    rw [hRec_size, ha] at hk
    rw [hRec_get (by rw [ha]; exact hk)] at hrep
    exact ⟨k, by omega, by rw [xi_lo hk]; exact hrep⟩
  · exact absurd (hpr 9 7 (by norm_num) (by norm_num) h1 h2) (by norm_num)
  · exact absurd (hpr 11 7 (by norm_num) (by norm_num) h1 h2) (by norm_num)
  · exact absurd (hpr 13 5 (by norm_num) (by norm_num) h1 h2) (by norm_num)
  · rw [h1, ← cg_eq, (MNd.recQ1e).1] at hk hrep
    rw [hRec_size, he] at hk
    rw [hRec_get (by rw [he]; exact hk)] at hrep
    exact ⟨112 + k, by omega, by rw [xi_hi]; exact hrep⟩

theorem xi_cn {i : Nat} (hi : i < 1232) : Cn (xi i) := by
  obtain ⟨-, -, ha, he, -⟩ := base_facts
  rcases Nat.lt_or_ge i 112 with h | h
  · rw [xi_lo h]
    exact penumPt_canon (MNd.q1a_pe i (by rw [ha]; exact h))
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [xi_hi]
    exact penumPt_canon (MNd.q1e_pe k (by rw [he]; omega))

noncomputable abbrev sa (a : Nat) : Equiv.Perm (Fin 275) :=
  tp 275 (tabT (unpack 275 9 (McLTwoS.T a)))

theorem sa_facts {a : Nat}
    (ha : a < 128) : Cn (McLTwoS.T a) ∧ Cn (McLTwoEI a) ∧ RP (McLTwoS.T a) (sa a) ∧
      RP (McLTwoEI a) (sa a)⁻¹ ∧ sa a ∈ closure (tp 275 '' {x | x ∈ sylTwoGens}) := by
  have hc : Cn (McLTwoS.T a) := McLTwo.hT a (by rw [McLTwo.base.2.2.2.2.1]; exact ha)
  have hi := allN_spec McLTwo.sInv a ha
  simp only [bAnd_iff] at hi
  obtain ⟨r1, r2⟩ := rp_perm hc hi.1 hi.2
  refine ⟨hc, hi.1, r1, r2, ?_⟩
  have F := subEnumOK_spec mcl_groupData McLTwo.sub_ok
  have e := McLTwo.closure_eq.1
  have hk : a < (mulClosureH 275 sylTwoGens 200).1.size := by
    rw [e, hRec_size, McLTwo.base.2.2.2.2.1]
    exact ha
  have hm := F.enum.mem a hk
  rw [e, hRec_get (by rw [McLTwo.base.2.2.2.2.1]; exact ha), tablePerm_eq r1] at hm
  exact hm

noncomputable abbrev gj (j : Nat) : Equiv.Perm (Fin 275) := tp 275 (tabT (unpack 275 9 (NoThrG j)))

noncomputable abbrev uj (j : Nat) : Equiv.Perm (Fin 275) :=
  if j = 0 then sa (r32 NoThrJ 0) else if j = 1 then sa (r32 NoThrJ 1)
    else sa (r32 NoThrJ 0) * sa (r32 NoThrJ 1)

theorem gj_facts
    {j : Nat} (hj : j < 3) :
    Cn (NoThrG j) ∧ Cn (NoThrGI j) ∧ RP (NoThrG j) (gj j) ∧ RP (NoThrGI j) (gj j)⁻¹ ∧
      gj j ∈ mclP ∧ gj j * mclT0 * (gj j)⁻¹ = uj j := by
  obtain ⟨hz, hv, -, -, hg⟩ := base_facts
  obtain ⟨c1, c2, hinv, hsift, hconj⟩ := hg j hj
  obtain ⟨r1, r2⟩ := rp_perm c1 c2 hinv
  have hP : gj j ∈ mclP := by
    rw [← mcl_groupData.sift _ _ r1, McLTwo.sift_eq c1]
    exact hsift
  refine ⟨c1, c2, r1, r2, hP, ?_⟩
  have cT : Cn (McLCT.F 4) := MNd.Fc (by norm_num)
  have rT : RP (McLCT.F 4) mclT0 := by
    have h := rep_tp (MNd.permF (k := 4) (by norm_num))
    have e : mclCentTbl 4 = tabT (unpack 275 9 (McLCT.F 4)) := MNd.tabF (by norm_num)
    unfold RP
    rw [← e]
    exact h
  obtain ⟨cz, -, rz, -, -⟩ := sa_facts hz
  obtain ⟨cv, -, rv, -, -⟩ := sa_facts hv
  have hU : Cn (noThrU j) ∧ RP (noThrU j) (uj j) := by
    unfold noThrU uj
    interval_cases j
    · exact ⟨cz, rz⟩
    · exact ⟨cv, rv⟩
    · exact ⟨cn_pc cz cv, rp_pc cz cv rz rv⟩
  have h := (beq_iff (cn_pc c1 (cn_pc cT c2)) hU.1 (rp_pc c1 (cn_pc cT c2) r1 (rp_pc cT c2 rT r2))
    hU.2).1 hconj
  rw [← h]
  group

theorem chk_all {j i : Nat} (hj : j < 3) (hi : i < 1232) : noThrK j i = true := by
  interval_cases j
  · exact allN_spec noThr_chk0 i hi
  · exact allN_spec noThr_chk1 i hi
  · exact allN_spec noThr_chk2 i hi

theorem witness_uj
    {j : Nat} (hj : j < 3) {y : Equiv.Perm (Fin 275)}
    (hy : y ∈ mclP) (hy3 : orderOf y = 3) (hyu : y * uj j = uj j * y) :
    ∃ a ∈ closure (tp 275 '' {x | x ∈ sylTwoGens}), ¬ (y * (a * y * a⁻¹)) ^ 729 = 1 := by
  obtain ⟨c1, c2, r1, r2, hP, hconj⟩ := gj_facts hj
  set g := gj j
  have hx : g⁻¹ * y * g ∈ mclCt := by
    refine mem_inf.2 ⟨mclP.mul_mem (mclP.mul_mem (mclP.inv_mem hP) hy) hP,
      mem_centralizer_singleton_iff.2 ?_⟩
    have e : mclT0 = g⁻¹ * uj j * g := by rw [← hconj]; group
    rw [e]
    calc g⁻¹ * y * g * (g⁻¹ * uj j * g) = g⁻¹ * (y * uj j) * g := by group
      _ = g⁻¹ * (uj j * y) * g := by rw [hyu]
      _ = g⁻¹ * uj j * g * (g⁻¹ * y * g) := by group
  have hx3 : orderOf (g⁻¹ * y * g) = 3 := by
    have := orderOf_conj' g⁻¹ y
    rwa [inv_inv, hy3] at this
  obtain ⟨i, hi, hrep⟩ := cent_three hx hx3
  obtain ⟨a, e, m, ha, hw⟩ := noThrK_spec (chk_all hj hi)
  obtain ⟨ca, cai, ra, rai, haS⟩ := sa_facts ha
  refine ⟨_, haS, ?_⟩
  have h := witK_sound c1 c2 (xi_cn hi) ca cai r1 r2 hrep ra rai hw
  rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h

theorem pow_729_of_le {W : Subgroup (Equiv.Perm (Fin 275))}
    (hWP : W ≤ mclP) (hW : IsPGroup 3 ↥W) {x : Equiv.Perm (Fin 275)} (hx : x ∈ W) :
    x ^ 729 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hW.exists_card_eq
  have hdvd : 3 ^ k ∣ 898128000 := by
    rw [← hk, ← card_mclP]
    exact Subgroup.card_dvd_of_le hWP
  have hk6 : k ≤ 6 := by
    by_contra h
    have h7 : 3 ^ 7 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    have := h7.trans hdvd
    norm_num at this
  have h1 : x ^ (3 ^ k) = 1 := by
    have h := pow_card_eq_one' (x := (⟨x, hx⟩ : W))
    rw [hk] at h
    simpa using congrArg Subtype.val h
  calc x ^ 729 = (x ^ (3 ^ k)) ^ (3 ^ (6 - k)) := by
        rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hk6]
        norm_num
    _ = 1 := by rw [h1, one_pow]

theorem noThree_sylTwo
    (W : Subgroup (Equiv.Perm (Fin 275))) (hWP : W ≤ mclP)
    (hW : IsPGroup 3 ↥W)
    (hn : closure (tp 275 '' {x | x ∈ sylTwoGens}) ≤ normalizer (W : Set (Equiv.Perm (Fin 275)))) :
    W = ⊥ := by
  obtain ⟨hz, hv, -, -, -⟩ := base_facts
  obtain ⟨-, -, -, -, hzS⟩ := sa_facts hz
  obtain ⟨-, -, -, -, hvS⟩ := sa_facts hv
  have ht2 : mclT0 ^ 2 = 1 := by
    rw [← mclT0_facts.2.1]
    exact pow_orderOf_eq_one _
  have hu2 : ∀ j < 3, uj j ^ 2 = 1 := by
    intro j hj
    rw [← (gj_facts hj).2.2.2.2.2, conj_pow, ht2, mul_one, mul_inv_cancel]
  refine eq_bot_of_witness_klein hWP hW (fun x hx => pow_729_of_le hWP hW hx) hn hzS hvS
    (hu2 0 (by norm_num)) (hu2 1 (by norm_num)) ?_
  intro y hy hy3 hyu
  rcases hyu with h | h | h
  · exact witness_uj (j := 0) (by norm_num) hy hy3 h
  · exact witness_uj (j := 1) (by norm_num) hy hy3 h
  · exact witness_uj (j := 2) (by norm_num) hy hy3 h

end CertificateChecks.KernelMcLAS.NoThr

end
