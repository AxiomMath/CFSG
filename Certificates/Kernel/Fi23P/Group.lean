module

public import Certificates.Kernel.Fi23P.Search
public import Certificates.Kernel.Fi23P.Words
public import CFSG.Certificates.Kernel.Fi23P.Tau
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23P

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23P CFSG.KD.Fi23K CFSG.KD.Fi23P CFSG.KS.TW
  CFSG.Sporadic.Th.Native CFSG.Monster.Existence.Fi23Sp8.Native CFSG.KS.Raw.Orb
  CertificateChecks.KernelFi23M CertificateChecks.KernelFi23C

theorem rootsA_get {c : Nat} (hc : c < 3) : rootsA[c]! = rtP c := by
  interval_cases c <;> rfl

theorem zIdx_pos (g : Nat) : zIdx ((g + 1 : Nat) : Int) = g := by
  unfold zIdx
  rw [if_pos (by omega)]
  omega

theorem labG_eq {x : Nat} (hx : x < 31671) : labG x = labP x := by
  unfold labG
  rw [if_pos hx]

theorem TG_lt {k x : Nat} (hk : gOK k = true) (hx : x < 31671) : TG k x < 31671 :=
  rng k (by have := ((gOK_iff k).1 hk).1; omega) x hx

theorem pathF_succ (r f p : Nat) : pathF r (f + 1) p =
    if p == r then [] else ((genG p + 1 : Nat) : Int) :: pathF r f (parG p) := rfl

theorem path_spec : ∀ f p, p < 31671 → depP p < f →
    wK (pathF (rtP (labP p)) f p) (rtP (labP p)) = p ∧
    (∀ z ∈ pathF (rtP (labP p)) f p, ∃ g, gOK g = true ∧ z = ((g + 1 : Nat) : Int))
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, p, hp, hd => by
    by_cases hr : p = rtP (labP p)
    · have e : pathF (rtP (labP p)) (f + 1) p = [] := by
        have hb : (p == rtP (labP p)) = true := by rw [← hr]; exact beq_self_eq_true p
        rw [pathF_succ, if_pos hb]
      rw [e]
      exact ⟨hr.symm, fun z hz => absurd hz (List.not_mem_nil)⟩
    · obtain ⟨g1, g2, g3, g4, g5⟩ := nonroot hp hr
      have ih := path_spec f (parP p) g2 (by omega)
      rw [g3] at ih
      have e : pathF (rtP (labP p)) (f + 1) p =
          ((genP p + 1 : Nat) : Int) :: pathF (rtP (labP p)) f (parP p) := by
        have hb : ¬ (p == rtP (labP p)) = true := by rw [beq_iff_eq]; exact hr
        rw [pathF_succ, if_neg hb]
        unfold genG parG
        rw [if_pos hp, if_pos hp]
      rw [e]
      refine ⟨?_, fun z hz => ?_⟩
      · change XK (zIdx ((genP p + 1 : Nat) : Int)) (wK (pathF (rtP (labP p)) f (parP p))
          (rtP (labP p))) = p
        rw [ih.1, zIdx_pos, XK_eq ((gOK_iff _).1 g1).1 g2]
        exact g4
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact ⟨genP p, g1, rfl⟩
        · exact ih.2 z hz

@[expose] def VL (z : Int) : Prop := z ≠ 0 ∧ zIdx z < 10

theorem VL_pos {g : Nat} (hg : gOK g = true) : VL ((g + 1 : Nat) : Int) :=
  ⟨by omega, by rw [zIdx_pos]; exact ((gOK_iff g).1 hg).1⟩

theorem zIdx_neg {z : Int} (hz : z ≠ 0) : zIdx (-z) = zIdx z := by
  unfold zIdx
  split_ifs <;> omega

theorem VL_neg {z : Int} (hz : VL z) : VL (-z) := by
  obtain ⟨h1, h2⟩ := hz
  refine ⟨by omega, ?_⟩
  rw [zIdx_neg h1]
  exact h2

section


noncomputable def gz (z : Int) : PG := if 0 < z then gen (zIdx z) else (gen (zIdx z))⁻¹

noncomputable def wPG (w : List Int) : PG := (w.map gz).prod

theorem acts_gz {z : Int} (hz : VL z) : ActsAs (phiX (gz z)) (tb G (zIdx z)) := by
  unfold gz
  split_ifs
  · rw [phiX_gen hz.2]
    exact xS_acts hz.2
  · rw [map_inv, phiX_gen hz.2]
    exact xS_inv_acts hz.2

theorem acts_wK : ∀ w : List Int, (∀ z ∈ w, VL z) → ActsAs (phiX (wPG w)) (wK w)
  | [], _ => fun _ _ => rfl
  | z :: w, hw => by
    have ih := acts_wK w fun y hy => hw y (List.mem_cons_of_mem z hy)
    have hz := hw z List.mem_cons_self
    unfold wPG
    rw [List.map_cons, List.prod_cons, map_mul]
    refine acts_congr ((acts_gz hz).mul ih) fun x hx => ?_
    have hlt : wK w x < 31671 := by rw [← ih x hx]; exact Fin.isLt _
    change tb G (zIdx z) (wK w x) = XK (zIdx z) (wK w x)
    rw [XK_eq hz.2 hlt]

theorem gz_neg {z : Int} (hz : VL z) : gz (-z) = (gz z)⁻¹ := by
  unfold gz
  rw [zIdx_neg hz.1]
  by_cases h : 0 < z
  · have h' : ¬ (0 : Int) < -z := by omega
    rw [if_neg h', if_pos h]
  · have h' : (0 : Int) < -z := by have := hz.1; omega
    rw [if_pos h', if_neg h, inv_inv]

theorem wPG_invWord : ∀ {u : List Int}, (∀ z ∈ u, VL z) → wPG (invWord u) = (wPG u)⁻¹
  | [], _ => by simp [wPG, invWord]
  | z :: u, hu => by
    have ih := wPG_invWord fun y hy => hu y (List.mem_cons_of_mem z hy)
    unfold wPG at ih ⊢
    rw [invWord_cons, List.map_append, List.prod_append, ih]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [gz_neg (hu z List.mem_cons_self), mul_inv_rev]

theorem invWord_VL {u : List Int} (hu : ∀ z ∈ u, VL z) : ∀ z ∈ invWord u, VL z := by
  intro z hz
  unfold invWord at hz
  rw [List.mem_map] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  exact VL_neg (hu x (List.mem_reverse.1 hx))


theorem cp_gen {k m : Nat} (hk : k < 10) (hm : m < 31671) :
    cp (tb G k m) = xS k * cp m * (xS k)⁻¹ := by
  have h := cp_eqv (gen k) hm
  rw [phiX_gen hk, xS_acts hk m hm] at h
  exact h

theorem cp_root : cp 4777 = xS 0 := (xS_cp (k := 0) (by norm_num)).symm

theorem path0 {p : Nat} (hp : p < 31671) (h0 : labP p = 0) :
    wK (pathK p) 4777 = p ∧ ∀ z ∈ pathK p, VL z := by
  have e : pathK p = pathF (rtP (labP p)) 100 p := by
    unfold pathK
    rw [labG_eq hp, rootsA_get (by omega)]
  obtain ⟨h1, h2⟩ := path_spec 100 p hp (dep_lt hp)
  rw [h0] at h1 h2 e
  rw [e]
  refine ⟨h1, fun z hz => ?_⟩
  obtain ⟨g, hg, rfl⟩ := h2 z hz
  exact VL_pos hg

theorem conj_cp {p : Nat} (hp : p < 31671) (h0 : labP p = 0) :
    ActsAs (cp p) (conjK (pathK p)) := by
  obtain ⟨h1, h2⟩ := path0 hp h0
  have hU := acts_wK _ h2
  have hUi : ActsAs (phiX (wPG (pathK p)))⁻¹ (wK (invWord (pathK p))) := by
    rw [← map_inv, ← wPG_invWord h2]
    exact acts_wK _ (invWord_VL h2)
  have hpU : (phiX (wPG (pathK p)) ⟨4777, by norm_num⟩).val = p := by
    rw [hU 4777 (by norm_num), h1]
  have e : cp p = phiX (wPG (pathK p)) * xS 0 * (phiX (wPG (pathK p)))⁻¹ := by
    have h := cp_eqv (wPG (pathK p)) (m := 4777) (by norm_num)
    rw [hpU, cp_root] at h
    exact h
  rw [e]
  refine acts_congr ((hU.mul (xS_acts (by norm_num))).mul hUi) fun x hx => ?_
  have hlt : wK (invWord (pathK p)) x < 31671 := by rw [← hUi x hx]; exact Fin.isLt _
  change wK (pathK p) (tb G 0 (wK (invWord (pathK p)) x)) =
    wK (pathK p) (XK 0 (wK (invWord (pathK p)) x))
  rw [XK_eq (by norm_num) hlt]

theorem cp_lt (p : Nat) {q : Nat} (hq : q < 31671) : (cp p ⟨q, hq⟩).val < 31671 := Fin.isLt _

theorem cp_gen_pt {k m q : Nat} (hk : k < 10) (hm : m < 31671) (hq : q < 31671) :
    (cp (tb G k m) ⟨q, hq⟩).val = tb G k (cp m ⟨tb G k q, rng k (by omega) q hq⟩).val := by
  rw [cp_gen hk hm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    acts_apply (xS_inv_acts hk) hq, xS_acts hk _ (Fin.isLt _)]

theorem tau_eq : tau = tauV := rfl

theorem trans_gen {k q : Nat} (hk : gOK k = true) (hq : q < 31671) (h0 : labP q = 0) :
    tb L 5 (tb G k q) = tauV (tb L 5 (piL.getD k 0)) (tb L 5 q) := by
  obtain ⟨i, hi, rfl⟩ : ∃ i < 255, tb L 7 i = q := by
    have := mem_sigL.2 ⟨hq, h0⟩
    unfold sigL at this
    rw [List.mem_map] at this
    obtain ⟨i, hi, e⟩ := this
    exact ⟨i, List.mem_range.1 hi, e⟩
  have h := allN_iff.1 trans_ok k ((gOK_iff k).1 hk).1
  rw [bIf_eq, if_pos hk] at h
  have h2 := allN_iff.1 h i hi
  rw [strictB_eq] at h2
  rw [← tau_eq]
  exact Nat.eq_of_beq_eq_true h2

theorem trans_cp : ∀ f p, p < 31671 → labP p = 0 → depP p < f → ∀ q (hq : q < 31671),
    labP q = 0 → labP (cp p ⟨q, hq⟩).val = 0 ∧
      tb L 5 (cp p ⟨q, hq⟩).val = tauV (tb L 5 p) (tb L 5 q)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, p, hp, h0, hd => by
    intro q hq hq0
    by_cases hr : p = rtP (labP p)
    · have e : p = 4777 := by rw [hr, h0]; rfl
      subst e
      rw [cp_root, xS_acts (by norm_num) q hq]
      exact ⟨(lab_T hq (k := 0) (by decide)).trans hq0, trans_gen (by decide) hq hq0⟩
    · obtain ⟨g1, g2, g3, g4, g5⟩ := nonroot hp hr
      have hg := ((gOK_iff _).1 g1).1
      have hq' := rng (genP p) (by omega) q hq
      have hq0' : labP (tb G (genP p) q) = 0 := by rw [← hq0]; exact lab_T hq g1
      obtain ⟨i1, i2⟩ := trans_cp f (parP p) g2 (by rw [g3]; exact h0) (by omega)
        (tb G (genP p) q) hq' hq0'
      have ep : tb G (genP p) (parP p) = p := g4
      have e := cp_gen_pt hg g2 hq
      rw [ep] at e
      rw [e]
      refine ⟨by rw [← i1]; exact lab_T (Fin.isLt _) g1, ?_⟩
      rw [trans_gen g1 (Fin.isLt _) i1, i2, trans_gen g1 hq hq0, tauV_conj,
        ← trans_gen g1 g2 (by rw [g3]; exact h0), ep]

theorem commK_eq {p q : Nat} (hp : p < 31671) (h0 : labP p = 0) (hq : q < 31671) :
    commK p q = ((cp p ⟨q, hq⟩).val == q) := by
  unfold commK
  rw [← conj_cp hp h0 q hq]

theorem tb_inj {k : Nat} (hk : k < 10) {a b : Nat} (ha : a < 31671) (hb : b < 31671) :
    (tb G k a == tb G k b) = (a == b) := by
  by_cases h : a = b
  · subst h
    simp
  · rw [beq_false_of_ne h]
    apply beq_false_of_ne
    intro e
    apply h
    rw [← x_inv hk ha, ← x_inv hk hb, e]

theorem commK_gen {k p y : Nat} (hk : gOK k = true) (hp : p < 31671) (h0 : labP p = 0)
    (hy : y < 31671) : commK (tb G k p) (tb G k y) = commK p y := by
  have hk' := ((gOK_iff k).1 hk).1
  have hp' : labP (tb G k p) = 0 := by rw [← h0]; exact lab_T hp hk
  rw [commK_eq (rng k (by omega) p hp) hp' (rng k (by omega) y hy), commK_eq hp h0 hy,
    cp_gen_pt hk' hp _]
  have e : (⟨tb G k (tb G k y), rng k (by omega) _ (rng k (by omega) y hy)⟩ : Fin 31671) =
      ⟨y, hy⟩ := Fin.ext (x_inv hk' hy)
  rw [e, tb_inj hk' (Fin.isLt _) hy]

noncomputable def cnt (y : Nat) : Nat := sigL.countP fun p => commK p y

theorem sigL_nodup : sigL.Nodup := sigL_pairwise.nodup

theorem perm_gen {k : Nat} (hk : gOK k = true) : (sigL.map (tb G k)).Perm sigL := by
  have hk' := ((gOK_iff k).1 hk).1
  rw [List.perm_ext_iff_of_nodup]
  · intro x
    rw [List.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨h1, h2⟩ := mem_sigL.1 hz
      exact mem_sigL.2 ⟨rng k (by omega) z h1, by rw [← h2]; exact lab_T h1 hk⟩
    · intro hx
      obtain ⟨h1, h2⟩ := mem_sigL.1 hx
      refine ⟨tb G k x, mem_sigL.2 ⟨rng k (by omega) x h1, by rw [← h2]; exact lab_T h1 hk⟩,
        x_inv hk' h1⟩
  · refine sigL_nodup.map_on fun a ha b hb e => ?_
    rw [← x_inv hk' (mem_sigL.1 ha).1, ← x_inv hk' (mem_sigL.1 hb).1, e]
  · exact sigL_nodup

theorem cnt_gen {k y : Nat} (hk : gOK k = true) (hy : y < 31671) : cnt (tb G k y) = cnt y := by
  have hk' := ((gOK_iff k).1 hk).1
  unfold cnt
  have e : sigL.countP (fun p => commK p (tb G k y)) =
      sigL.countP (fun p => commK (tb G k p) y) := by
    apply List.countP_congr
    intro p hp
    obtain ⟨h1, h2⟩ := mem_sigL.1 hp
    have hp' : labP (tb G k p) = 0 := by rw [← h2]; exact lab_T h1 hk
    rw [← commK_gen hk (rng k (by omega) p h1) hp' hy, x_inv hk' h1]
  rw [e]
  calc sigL.countP (fun p => commK (tb G k p) y)
      = (sigL.map (tb G k)).countP (fun p => commK p y) := by
        simp only [List.countP_map, Function.comp_def]
    _ = sigL.countP (fun p => commK p y) := (perm_gen hk).countP_eq _

theorem cnt_root : ∀ f y, y < 31671 → depP y < f → cnt y = cnt (rtP (labP y))
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, y, hy, hd => by
    by_cases hr : y = rtP (labP y)
    · rw [← hr]
    · obtain ⟨g1, g2, g3, g4, g5⟩ := nonroot hy hr
      have e : y = tb G (genP y) (parP y) := g4.symm
      rw [e, cnt_gen g1 g2, cnt_root f (parP y) g2 (by omega), g3, ← e]

theorem cnt_vals : cnt (rtP 0) = 127 ∧ cnt (rtP 1) = 45 ∧ cnt (rtP 2) = 15 :=
  ⟨Nat.eq_of_beq_eq_true cnt0_ok, Nat.eq_of_beq_eq_true cnt1_ok, Nat.eq_of_beq_eq_true cnt2_ok⟩

theorem sep_lab {y c : Nat} (hy : y < 31671) (hc : c < 3)
    (h : (sigL.all fun p => commK p y == commK p (rtP c)) = true) : labP y = c := by
  have e : cnt y = cnt (rtP c) := by
    unfold cnt
    apply List.countP_congr
    intro p hp
    have := List.all_eq_true.1 h p hp
    rw [beq_iff_eq] at this
    rw [this]
  rw [cnt_root 100 y hy (dep_lt hy)] at e
  have hl := lab_lt hy
  obtain ⟨v0, v1, v2⟩ := cnt_vals
  interval_cases c <;> interval_cases hlv : labP y <;> simp_all

end

theorem wK_wv : ∀ w : List Int, (∀ z ∈ w, zIdx z < 10) → ∀ y < 31671,
    wK w y = wv G (w.map zIdx) y ∧ wK w y < 31671
  | [], _, y, hy => ⟨rfl, hy⟩
  | z :: w, hw, y, hy => by
    obtain ⟨h1, h2⟩ := wK_wv w (fun x hx => hw x (List.mem_cons_of_mem z hx)) y hy
    have hz := hw z List.mem_cons_self
    change XK (zIdx z) (wK w y) = tb G (zIdx z) (wv G (w.map zIdx) y) ∧
      XK (zIdx z) (wK w y) < 31671
    rw [XK_eq hz h2, h1]
    exact ⟨rfl, by rw [← h1]; exact rng _ (by omega) _ h2⟩

theorem wR_eq (W : Nat → Nat) (o : Nat) : ∀ m x,
    wR G W o m x = wv G ((List.range m).map fun i => W (o + i)) x
  | 0, x => rfl
  | m + 1, x => by
    have e : wR G W o (m + 1) x = strictN (tb G (W (Nat.add o m)) x) (wR G W o m) := rfl
    rw [e, strictN_eq, wR_eq W o m, List.range_succ, List.map_append, wv_append]
    rfl

theorem wS_eq (t x : Nat) : wS t x = wv G (regW t) x := by
  unfold wS regW
  exact wR_eq _ _ _ _

theorem sLetter_idx {z : Int} (h : sLetterOK z = true) : zIdx z < 10 := by
  unfold sLetterOK letterOK at h
  unfold zIdx
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  split_ifs <;> omega

theorem stab_ok (c : Nat) (hc : c < 3) : ((stabPairs c).map (stabK c)).all (fun w =>
    w.all sLetterOK && wK w rootsA[c]! == rootsA[c]!) = true := by
  interval_cases c
  · exact stab_ok0
  · exact stab_ok1
  · exact stab_ok2

theorem regs_ok (c : Nat) (hc : c < 3) : ((stabPairs c).map (stabK c)).map (fun w => w.map zIdx) =
    (List.range (cntW c)).map fun j => regW (baseP c + j) := by
  interval_cases c
  · exact beq_iff_eq.1 regs_ok0
  · exact beq_iff_eq.1 regs_ok1
  · exact beq_iff_eq.1 regs_ok2

theorem base_cnt (c : Nat) (hc : c < 3) : baseP (c + 1) = baseP c + cntW c := by
  interval_cases c <;> rfl

theorem sep_root {y c : Nat} (hy : y < 31671) (hc : c < 3) (hl : labP y = c)
    (h : ∀ w ∈ (stabPairs c).map (stabK c), wK w y = y) : y = rtP c := by
  by_contra hr
  rw [← hl] at hr
  obtain ⟨m1, m2, m3⟩ := moving hy hr
  rw [hl] at m1 m2
  set t := tb L 8 y with ht
  have hj : t - baseP c < cntW c := by rw [base_cnt c hc] at m2; omega
  have e := congrArg (fun l => l[t - baseP c]?) (regs_ok c hc)
  simp only [List.getElem?_map, List.getElem?_range hj] at e
  obtain ⟨w, hw, hwe⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨pr, hpr, hpw⟩ := Option.map_eq_some_iff.1 hw
  have hmem : w ∈ (stabPairs c).map (stabK c) :=
    List.mem_map.2 ⟨pr, List.mem_of_getElem? hpr, hpw⟩
  have hlet : ∀ z ∈ w, zIdx z < 10 := by
    have := List.all_eq_true.1 (stab_ok c hc) w hmem
    rw [Bool.and_eq_true, List.all_eq_true] at this
    exact fun z hz => sLetter_idx (this.1 z hz)
  have ht2 : baseP c + (t - baseP c) = t := by omega
  dsimp only at hwe
  rw [ht2] at hwe
  rw [wS_eq] at m3
  apply m3
  rw [← hwe, ← (wK_wv w hlet y hy).1]
  exact h w hmem

end CertificateChecks.KernelFi23P

end
