module

public import Certificates.Kernel.SporSch.Pair.J2Check
public import CFSG.Certificates.Kernel.SporSch.Cnt3Proof
public import CFSG.Certificates.Kernel.SporSch.FibChainProof
public import CFSG.Certificates.Kernel.SporSch.FibOrbProof
public import CFSG.Sporadic.Schreier.PairJ2CertBase
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.PJ2Fib

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairJ2
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.PJ2Check
open CFSG.KS.SporSch.FibOrb Finset

theorem arrs :
    ChainArrays j2Chain ((j2StrongArrs ()).extract 0 2) (j2StrongArrs ()) baseArr (j2Words ()) :=
  chainArrays_ofArrays fun j hj => (chainCheckFacts PJ2.chain).strong_inv j hj

theorem valid : ValidSchreier j2Chain := (validSchreier_of_chainOK arrs (by norm_num) PJ2.chain).1

theorem faithful : BaseFaithful j2Chain.originalSubgroup bs := baseFaithful_of_valid valid

theorem bs_lt : ∀ b ∈ bs, b < 315 := by decide

theorem strong_size : (j2StrongArrs ()).size = 7 := by simp [j2StrongArrs]

theorem strong_mem (j : Nat) (hj : j < 7) :
    permOfArr 315 (j2StrongArrs ())[j]! ∈ j2Chain.originalSubgroup := by
  have h := RawSchreierDatum.strong_get_mem_originalSubgroup j2Chain valid
    ⟨j, by change j < (j2StrongArrs ()).size; rw [strong_size]; exact hj⟩
  convert h using 1
  simp only [j2Chain, RawSchreierDatum.ofArrays, Vector.get, Vector.toArray_ofFn,
    Array.getElem_ofFn]
  rfl

theorem strong_rep (j : Nat) (hj : j < 7) :
    RepW 315 [(j2StrongArrs ())[j]!] (permOfArr 315 (j2StrongArrs ())[j]!) :=
  RepW.single (rep_permOfArr ((chainCheckFacts PJ2.chain).strong_inv j (strong_size ▸ hj))).1

theorem img0 : allN 315 (fun k => Nat.beq (rpos 9 (mask 9) (Nat.mul 315 9) (PJ2.LR 0)
    (pg 9 (mask 9) (trK 315 (Nat.mul 315 9) PJ2.LR PJ2.TR 0 k) 1)) k) = true := by
  quickRfl

@[expose] def wd (k0 k1 k2 : Nat) : List (Array Nat) :=
  [compA 315 (rawLevels 315 (j2StrongArrs ()) baseArr)[1]!.tr[k1]!
      (compA 315 (rawLevels 315 (j2StrongArrs ()) baseArr)[2]!.tr[k2]! (idA 315)),
    compA 315 (rawLevels 315 (j2StrongArrs ()) baseArr)[0]!.tr[k0]! (idA 315)]

@[expose] def img (k0 : Nat) : Nat := ((rawLevels 315 (j2StrongArrs ()) baseArr)[0]!.tr[k0]!)[1]!

theorem img_eq (k : Nat) (hk : k < 315) :
    img k = pg 9 (mask 9) (trK 315 (Nat.mul 315 9) PJ2.LR PJ2.TR 0 k) 1 := by
  have h0 := Nat.eq_of_beq_eq_true hr0
  exact ((Cnt3P.lev_agree PJ2.binds PJ2.perm PJ2.hl (i := 0) (by norm_num)).2 k (h0 ▸ hk) 1
    (by norm_num)).1

theorem img_inj (k k' : Nat) (hk : k < 315) (hk' : k' < 315) (e : img k = img k') : k = k' := by
  have a := Nat.eq_of_beq_eq_true (allN_spec img0 k hk)
  have b := Nat.eq_of_beq_eq_true (allN_spec img0 k' hk')
  rw [← img_eq k hk, e, img_eq k' hk'] at a
  exact a.symm.trans b

theorem img_range (k : Nat) (hk : k < 315) : img k < 315 := by
  have h0 := Nat.eq_of_beq_eq_true hr0
  rw [img_eq k hk]
  exact ((Cnt3P.lev_agree PJ2.binds PJ2.perm PJ2.hl (i := 0) (by norm_num)).2 k (h0 ▸ hk) 1
    (by norm_num)).2

theorem sum_img0 (F : Nat → Nat) : ∑ k ∈ range 315, F (img k) = ∑ a ∈ range 315, F a :=
  sum_range_reindex F img img_range fun k hk k' hk' e => img_inj k k' hk hk' e

theorem evR_wd3 {n : Nat} {t0 t1 t2 : Array Nat} (p1 : 1 < n) (e1 : t1[1]! = 1)
    (e2 : t2[1]! = 1) :
    evR [compA n t1 (compA n t2 (idA n)), compA n t0 (idA n)] 1 = t0[1]! := by
  change (compA n t0 (idA n))[(compA n t1 (compA n t2 (idA n)))[1]!]! = _
  rw [compA_get p1, compA_get p1, idA_get p1, e2, e1, compA_get p1, idA_get p1]

theorem ev_wd {k0 k1 k2 : Nat} (h1 : k1 < rcnt (PJ2.LR 1))
    (h2 : k2 < rcnt (PJ2.LR 2)) : evR (wd k0 k1 k2) 1 = img k0 := by
  have hb : List.headD bs 0 = 1 := rfl
  have p1 : List.headD bs 0 < 315 := by rw [hb]; norm_num
  have e1 := (((Cnt3P.lev_agree PJ2.binds PJ2.perm PJ2.hl (i := 1) (by norm_num)).2 k1 h1 _
    p1).1).trans (Nat.eq_of_beq_eq_true (allN_spec fixL1 k1 h1))
  have e2 := (((Cnt3P.lev_agree PJ2.binds PJ2.perm PJ2.hl (i := 2) (by norm_num)).2 k2 h2 _
    p1).1).trans (Nat.eq_of_beq_eq_true (allN_spec fixL2 k2 h2))
  rw [hb] at e1 e2
  rw [wd]
  exact evR_wd3 (by norm_num) e1 e2

open scoped Classical in
theorem card_fib {f : List (Array ℕ) → Bool} {Pr : Equiv.Perm (Fin 315) → Prop}
    (hfP : ∀ w g, RepW 315 w g → g ∈ j2Chain.originalSubgroup → (f w = true ↔ Pr g))
    {k0 : Nat} (hk0 : k0 < 315) (a : Fin 315) (ha : (a : Nat) = img k0) :
    Nat.card {x : j2Chain.originalSubgroup // (x : Equiv.Perm (Fin 315)) 1 = a ∧ Pr x} =
      ∑ k1 ∈ range (rcnt (PJ2.LR 1)), ∑ k2 ∈ range (rcnt (PJ2.LR 2)),
        if f (wd k0 k1 k2) = true then 1 else 0 := by
  have s0 := (Cnt3P.lev_agree PJ2.binds PJ2.perm PJ2.hl (i := 0) (by norm_num)).1
  have s1 := (Cnt3P.lev_agree PJ2.binds PJ2.perm PJ2.hl (i := 1) (by norm_num)).1
  have s2 := (Cnt3P.lev_agree PJ2.binds PJ2.perm PJ2.hl (i := 2) (by norm_num)).1
  have hh0 := Nat.eq_of_beq_eq_true hr0
  refine card_fib_countW (r0 := 315) arrs (by norm_num) PJ2.chain (groups := [[0], [1, 2]]) rfl
    hfP wd img (fun F => ?_) 1 (fun _ _ _ h1 _ h2 => ev_wd h1 h2) hk0
    (fun k hk e => img_inj k k0 hk hk0 e) a ha
  rw [Cnt3P.countW_blocks, s0, s1, s2, hh0]
  rfl

theorem cnt3_split (m : Nat) {XP : List Nat} (hX : canonL 315 9 XP = true)
    (conds : List (List Bool × Nat)) {k0 : Nat} (hk0 : k0 < 315) :
    cnt3 315 9 PJ2.LR PJ2.TR bs m XP conds k0 =
      (∑ k1 ∈ range (rcnt (PJ2.LR 1)), ∑ k2 ∈ range (rcnt (PJ2.LR 2)),
        if ordB bs (wd k0 k1 k2) m = true then 1 else 0) +
      1048576 * ∑ k1 ∈ range (rcnt (PJ2.LR 1)), ∑ k2 ∈ range (rcnt (PJ2.LR 2)),
        if (ordB bs (wd k0 k1 k2) m && condsOK bs (XP.map (unpack 315 9)) (wd k0 k1 k2) conds) =
          true then 1 else 0 := by
  have hh0 := Nat.eq_of_beq_eq_true hr0
  have h0 : k0 < rcnt (PJ2.LR 0) := hh0 ▸ hk0
  have hbsl : ∀ b ∈ bs, b < 315 := bs_lt
  have hXr := Cnt3P.rangeL_of_canonL hX
  rw [Cnt3P.cnt3_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k1 hk1 => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k2 hk2 => ?_
  rw [Finset.mem_range] at hk1 hk2
  have hK : Cnt3P.RangeL 315 9 [trK 315 (Nat.mul 315 9) PJ2.LR PJ2.TR 2 k2,
      trK 315 (Nat.mul 315 9) PJ2.LR PJ2.TR 1 k1, trK 315 (Nat.mul 315 9) PJ2.LR PJ2.TR 0 k0] := by
    intro W hW q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl | rfl
    · exact ((Cnt3P.lev_agree PJ2.binds PJ2.perm PJ2.hl (i := 2) (by norm_num)).2 k2 hk2 q hq).2
    · exact ((Cnt3P.lev_agree PJ2.binds PJ2.perm PJ2.hl (i := 1) (by norm_num)).2 k1 hk1 q hq).2
    · exact ((Cnt3P.lev_agree PJ2.binds PJ2.perm PJ2.hl (i := 0) (by norm_num)).2 k0 h0 q hq).2
  have hw := Cnt3P.word_ag PJ2.binds PJ2.perm PJ2.hl h0 hk1 hk2
  rw [Cnt3P.vv_split]
  change _ = (if ordB bs (wd k0 k1 k2) m = true then 1 else 0) + 1048576 *
    (if (ordB bs (wd k0 k1 k2) m && condsOK bs (XP.map (unpack 315 9)) (wd k0 k1 k2) conds) = true
      then 1 else 0)
  rw [wd, Cnt3P.ordB_ag hw hbsl, ← Cnt3P.ordB0_eq hK hbsl,
    Cnt3P.condsOK_ag (Cnt3P.rangeL_ag hXr) hw hbsl, ← Cnt3P.condsK_eq hXr hK hbsl]

theorem cnt3_card {m : Nat} (hm : 0 < m) {XP : List Nat} (hX : canonL 315 9 XP = true)
    {xg : Equiv.Perm (Fin 315)} (hx : RepW 315 (XP.map (unpack 315 9)) xg)
    (hxG : xg ∈ j2Chain.originalSubgroup) {conds : List (List Bool × Nat)}
    (hc : ∀ c ∈ conds, 0 < c.2) {k0 : Nat} (hk0 : k0 < 315) (a : Fin 315)
    (ha : (a : Nat) = img k0) :
    cnt3 315 9 PJ2.LR PJ2.TR bs m XP conds k0 =
      Nat.card {x : j2Chain.originalSubgroup // (x : Equiv.Perm (Fin 315)) 1 = a ∧
        orderOf (x : Equiv.Perm (Fin 315)) = m} +
      1048576 * Nat.card {x : j2Chain.originalSubgroup // (x : Equiv.Perm (Fin 315)) 1 = a ∧
        (orderOf (x : Equiv.Perm (Fin 315)) = m ∧ ∀ c ∈ conds,
          orderOf (c.1.map fun b => if b then (x : Equiv.Perm (Fin 315)) else xg).prod = c.2)} := by
  rw [cnt3_split m hX conds hk0,
    card_fib (f := fun w => ordB bs w m) (Pr := fun g => orderOf g = m) (fun w g hw hg => ordB_iff faithful bs_lt hw hg hm) hk0
      a ha,
    card_fib (f := fun w => ordB bs w m && condsOK bs (XP.map (unpack 315 9)) w conds)
      (Pr := fun g => orderOf g = m ∧ ∀ c ∈ conds,
        orderOf (c.1.map fun b => if b then g else xg).prod = c.2)
      (fun w g hw hg => by
        rw [Bool.and_eq_true, ordB_iff faithful bs_lt hw hg hm,
          condsOK_iff faithful bs_lt hx hw hxG hg hc]) hk0 a ha]

@[expose] def pt (a : Nat) : Fin 315 := ⟨a % 315, Nat.mod_lt _ (by norm_num)⟩

theorem pt_val (a : Nat) (ha : a < 315) : (pt a : Nat) = a := Nat.mod_eq_of_lt ha

theorem cnt3_div {m : Nat} (hm : 0 < m) {XP : List Nat} (hX : canonL 315 9 XP = true)
    {xg : Equiv.Perm (Fin 315)} (hx : RepW 315 (XP.map (unpack 315 9)) xg)
    (hxG : xg ∈ j2Chain.originalSubgroup) {conds : List (List Bool × Nat)}
    (hc : ∀ c ∈ conds, 0 < c.2) {k0 : Nat} (hk0 : k0 < 315) :
    Nat.div (cnt3 315 9 PJ2.LR PJ2.TR bs m XP conds k0) 1048576 =
      Nat.card {x : j2Chain.originalSubgroup // (x : Equiv.Perm (Fin 315)) 1 = pt (img k0) ∧
        (orderOf (x : Equiv.Perm (Fin 315)) = m ∧ ∀ c ∈ conds,
          orderOf (c.1.map fun b => if b then (x : Equiv.Perm (Fin 315)) else xg).prod = c.2)} := by
  have hA : (∑ k1 ∈ range (rcnt (PJ2.LR 1)), ∑ k2 ∈ range (rcnt (PJ2.LR 2)),
      if ordB bs (wd k0 k1 k2) m = true then 1 else 0) < 1048576 := by
    have hle : (∑ k1 ∈ range (rcnt (PJ2.LR 1)), ∑ k2 ∈ range (rcnt (PJ2.LR 2)),
        if ordB bs (wd k0 k1 k2) m = true then 1 else 0) ≤ rcnt (PJ2.LR 1) * rcnt (PJ2.LR 2) :=
      (Finset.sum_le_sum fun k1 _ => Finset.sum_le_sum fun k2 _ =>
        (by split <;> omega : (if ordB bs (wd k0 k1 k2) m = true then 1 else 0) ≤ 1)).trans
        (by simp)
    have := Nat.eq_of_beq_eq_true hr12
    omega
  rw [card_fib (f := fun w => ordB bs w m && condsOK bs (XP.map (unpack 315 9)) w conds)
      (Pr := fun g => orderOf g = m ∧ ∀ c ∈ conds,
        orderOf (c.1.map fun b => if b then g else xg).prod = c.2)
      (fun w g hw hg => by
        rw [Bool.and_eq_true, ordB_iff faithful bs_lt hw hg hm,
          condsOK_iff faithful bs_lt hx hw hxG hg hc]) hk0 _ (pt_val _ (img_range k0 hk0)),
    cnt3_split m hX conds hk0]
  change (_ + 1048576 * _) / 1048576 = _
  omega

theorem cnt3_mod {m : Nat} (hm : 0 < m) {XP : List Nat} (hX : canonL 315 9 XP = true)
    (conds : List (List Bool × Nat)) {k0 : Nat} (hk0 : k0 < 315) :
    Nat.mod (cnt3 315 9 PJ2.LR PJ2.TR bs m XP conds k0) 1048576 =
      Nat.card {x : j2Chain.originalSubgroup // (x : Equiv.Perm (Fin 315)) 1 = pt (img k0) ∧
        (orderOf (x : Equiv.Perm (Fin 315)) = m ∧ ∀ c ∈ ([] : List (List Bool × Nat)),
          orderOf (c.1.map fun b => if b then (x : Equiv.Perm (Fin 315)) else 1).prod = c.2)} := by
  have hA : (∑ k1 ∈ range (rcnt (PJ2.LR 1)), ∑ k2 ∈ range (rcnt (PJ2.LR 2)),
      if ordB bs (wd k0 k1 k2) m = true then 1 else 0) < 1048576 := by
    have hle : (∑ k1 ∈ range (rcnt (PJ2.LR 1)), ∑ k2 ∈ range (rcnt (PJ2.LR 2)),
        if ordB bs (wd k0 k1 k2) m = true then 1 else 0) ≤ rcnt (PJ2.LR 1) * rcnt (PJ2.LR 2) :=
      (Finset.sum_le_sum fun k1 _ => Finset.sum_le_sum fun k2 _ =>
        (by split <;> omega : (if ordB bs (wd k0 k1 k2) m = true then 1 else 0) ≤ 1)).trans
        (by simp)
    have := Nat.eq_of_beq_eq_true hr12
    omega
  rw [card_fib (f := fun w => ordB bs w m)
      (Pr := fun g => orderOf g = m ∧ ∀ c ∈ ([] : List (List Bool × Nat)),
        orderOf (c.1.map fun b => if b then g else 1).prod = c.2)
      (fun w g hw hg => by
        rw [ordB_iff faithful bs_lt hw hg hm]
        simp) hk0 _ (pt_val _ (img_range k0 hk0)),
    cnt3_split m hX conds hk0]
  exact (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt hA)

theorem sum_div_card {m : Nat} (hm : 0 < m) {XP : List Nat} (hX : canonL 315 9 XP = true)
    {xg : Equiv.Perm (Fin 315)} (hx : RepW 315 (XP.map (unpack 315 9)) xg)
    (hxG : xg ∈ j2Chain.originalSubgroup) {conds : List (List Bool × Nat)}
    (hc : ∀ c ∈ conds, 0 < c.2) :
    ∑ k ∈ range 315, Nat.div (cnt3 315 9 PJ2.LR PJ2.TR bs m XP conds k) 1048576 =
      Nat.card {x : j2Chain.originalSubgroup // orderOf (x : Equiv.Perm (Fin 315)) = m ∧
        ∀ c ∈ conds,
          orderOf (c.1.map fun b => if b then (x : Equiv.Perm (Fin 315)) else xg).prod = c.2} := by
  rw [Finset.sum_congr rfl fun k hk => cnt3_div hm hX hx hxG hc (mem_range.1 hk),
    sum_img0 (fun a => Nat.card {x : j2Chain.originalSubgroup //
      (x : Equiv.Perm (Fin 315)) 1 = pt a ∧ (orderOf (x : Equiv.Perm (Fin 315)) = m ∧
        ∀ c ∈ conds, orderOf (c.1.map fun b => if b then (x : Equiv.Perm (Fin 315)) else xg).prod =
          c.2)})]
  exact (card_eq_sum_fibB j2Chain.originalSubgroup 1 (fun x => orderOf x = m ∧ ∀ c ∈ conds,
    orderOf (c.1.map fun b => if b then x else xg).prod = c.2) pt pt_val).symm

theorem sum_div_conj {m : Nat} (hm : 0 < m) {XP XP' : List Nat} (hX : canonL 315 9 XP = true)
    (hX' : canonL 315 9 XP' = true) {xg cg : Equiv.Perm (Fin 315)}
    (hx : RepW 315 (XP.map (unpack 315 9)) xg) (hx' : RepW 315 (XP'.map (unpack 315 9))
      (cg * xg * cg⁻¹))
    (hxG : xg ∈ j2Chain.originalSubgroup) (hcG : cg ∈ j2Chain.originalSubgroup)
    {conds : List (List Bool × Nat)} (hc : ∀ c ∈ conds, 0 < c.2) :
    ∑ k ∈ range 315, Nat.div (cnt3 315 9 PJ2.LR PJ2.TR bs m XP conds k) 1048576 =
      ∑ k ∈ range 315, Nat.div (cnt3 315 9 PJ2.LR PJ2.TR bs m XP' conds k) 1048576 := by
  have hx'G : cg * xg * cg⁻¹ ∈ j2Chain.originalSubgroup :=
    j2Chain.originalSubgroup.mul_mem (j2Chain.originalSubgroup.mul_mem hcG hxG)
      (j2Chain.originalSubgroup.inv_mem hcG)
  rw [sum_div_card hm hX hx hxG hc, sum_div_card hm hX' hx' hx'G hc,
    card_conds_conj j2Chain.originalSubgroup hcG xg m conds]

theorem sum_mod_forest {m : Nat} (hm : 0 < m) {XP : List Nat} (hX : canonL 315 9 XP = true)
    (conds : List (List Bool × Nat)) (hs : Nat → Equiv.Perm (Fin 315))
    (hsG : ∀ i, hs i ∈ j2Chain.originalSubgroup) (hsb : ∀ i, hs i 1 = 1)
    (OJ RP par gi dep K : Nat → Nat) {nr : Nat}
    (hJ : ∀ a < 315, OJ a < nr) (h0 : ∀ a < 315, dep a = 0 → RP (OJ a) = a)
    (hst : ∀ a < 315, dep a ≠ 0 → par a < 315 ∧ OJ (par a) = OJ a ∧ dep (par a) + 1 = dep a ∧
      hs (gi a) (pt (par a)) = pt a)
    (hK : ∀ j < nr, K j < 315 ∧ img (K j) = RP j) :
    ∑ k ∈ range 315, Nat.mod (cnt3 315 9 PJ2.LR PJ2.TR bs m XP conds k) 1048576 =
      ∑ j ∈ range nr, #((range 315).filter fun a => OJ a = j) *
        Nat.mod (cnt3 315 9 PJ2.LR PJ2.TR bs m XP conds (K j)) 1048576 := by
  rw [Finset.sum_congr rfl fun k hk => cnt3_mod hm hX conds (mem_range.1 hk),
    sum_img0 (fun a => Nat.card {x : j2Chain.originalSubgroup //
      (x : Equiv.Perm (Fin 315)) 1 = pt a ∧ (orderOf (x : Equiv.Perm (Fin 315)) = m ∧
        ∀ c ∈ ([] : List (List Bool × Nat)),
          orderOf (c.1.map fun b => if b then (x : Equiv.Perm (Fin 315)) else 1).prod = c.2)}),
    forest_sum j2Chain.originalSubgroup hs hsG hsb (fun i => by group) pt m [] OJ RP par gi dep hJ
      h0 hst]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hKl, hKe⟩ := hK j (mem_range.1 hj)
  rw [cnt3_mod hm hX conds hKl, hKe]

theorem sum_div_forest {m : Nat} (hm : 0 < m) {XP : List Nat} (hX : canonL 315 9 XP = true)
    {xg : Equiv.Perm (Fin 315)} (hx : RepW 315 (XP.map (unpack 315 9)) xg)
    (hxG : xg ∈ j2Chain.originalSubgroup) {conds : List (List Bool × Nat)}
    (hc : ∀ c ∈ conds, 0 < c.2) (hs : Nat → Equiv.Perm (Fin 315))
    (hsG : ∀ i, hs i ∈ j2Chain.originalSubgroup) (hsb : ∀ i, hs i 1 = 1)
    (hsx : ∀ i, hs i * xg * (hs i)⁻¹ = xg) (OJ RP par gi dep K : Nat → Nat) {nr : Nat}
    (hJ : ∀ a < 315, OJ a < nr) (h0 : ∀ a < 315, dep a = 0 → RP (OJ a) = a)
    (hst : ∀ a < 315, dep a ≠ 0 → par a < 315 ∧ OJ (par a) = OJ a ∧ dep (par a) + 1 = dep a ∧
      hs (gi a) (pt (par a)) = pt a)
    (hK : ∀ j < nr, K j < 315 ∧ img (K j) = RP j) :
    ∑ k ∈ range 315, Nat.div (cnt3 315 9 PJ2.LR PJ2.TR bs m XP conds k) 1048576 =
      ∑ j ∈ range nr, #((range 315).filter fun a => OJ a = j) *
        Nat.div (cnt3 315 9 PJ2.LR PJ2.TR bs m XP conds (K j)) 1048576 := by
  rw [Finset.sum_congr rfl fun k hk => cnt3_div hm hX hx hxG hc (mem_range.1 hk),
    sum_img0 (fun a => Nat.card {x : j2Chain.originalSubgroup //
      (x : Equiv.Perm (Fin 315)) 1 = pt a ∧ (orderOf (x : Equiv.Perm (Fin 315)) = m ∧
        ∀ c ∈ conds, orderOf (c.1.map fun b => if b then (x : Equiv.Perm (Fin 315)) else xg).prod =
          c.2)}),
    forest_sum j2Chain.originalSubgroup hs hsG hsb hsx pt m conds OJ RP par gi dep hJ h0 hst]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hKl, hKe⟩ := hK j (mem_range.1 hj)
  rw [cnt3_div hm hX hx hxG hc hKl, hKe]

end CertificateChecks.KernelSporSch.PJ2Fib

end
