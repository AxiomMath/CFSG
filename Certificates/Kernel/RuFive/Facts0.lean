module

public import Certificates.Kernel.RuFive.FactsQ
public import Certificates.Kernel.RuFive.K0
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KC.J2H
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier
open CFSG.Certificates CFSG.Certificates.Native


theorem lit3_0 (a b c : Array Nat) : (#[a, b, c] : Array (Array Nat))[0]! = a := rfl
theorem lit3_1 (a b c : Array Nat) : (#[a, b, c] : Array (Array Nat))[1]! = b := rfl
theorem lit3_2 (a b c : Array Nat) : (#[a, b, c] : Array (Array Nat))[2]! = c := rfl

theorem cgens_eq (k : Nat) (hk : k < 3) : ruFiveC0Gens[k]! = unpack 4060 12 (F (64 + k)) := by
  rw [ruFiveC0Gens]
  interval_cases k
  · exact (lit3_0 _ _ _).trans (arr_eq 64 (by norm_num))
  · exact (lit3_1 _ _ _).trans (arr_eq 65 (by norm_num))
  · exact (lit3_2 _ _ _).trans (arr_eq 66 (by norm_num))

@[expose] noncomputable def gpC (k : Nat) : Equiv.Perm (Fin 4060) := gp (64 + k)

theorem cgs : ∀ k < 3, Rep 4060 ruFiveC0Gens[k]! (gpC k) := fun k hk => by
  rw [cgens_eq k hk]
  exact rep_gp _ (by omega)

theorem cg : ∀ k < 3, RepF 4060 (gC k) (gpC k) := fun k hk => repF_pa (64 + k) (by omega)

theorem cg_mem : ∀ k < 3, gpC k ∈ ruP := fun k hk => gp_mem _ (by omega)

theorem ctree : TreeOK 3 1000 C0.P C0.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kCTree i hi
  rwa [beq_zero_false h0] at h

theorem cedges : ∀ i < 1000, ∀ k < 3, CE i k < 1000 ∧
    treeArr 4060 ruFiveC0Gens C0.P C0.L (CE i k) =
      compA 4060 ruFiveC0Gens[k]! (treeArr 4060 ruFiveC0Gens C0.P C0.L i) :=
  edges_of_edgeAtK ctree cg cgs hmul cg_mem (fun k hk => iff_of_true (cg_mem k hk) rfl)
    (fun _ _ => by decide) bs_lt hF fun i hi => Orb.allN_iff.1 kCEdge i hi

theorem ckeys_inj : ∀ a < 1000, ∀ b < 1000,
    keyA 4060 ruFiveKeys (treeArr 4060 ruFiveC0Gens C0.P C0.L a) =
      keyA 4060 ruFiveKeys (treeArr 4060 ruFiveC0Gens C0.P C0.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := ckey) fun j hj => Orb.allN_iff.1 kCSort j hj
  intro a ha b hb e
  rw [keyA_treeArr ctree cg cgs keys_lt ha, keyA_treeArr ctree cg cgs keys_lt hb] at e
  exact hk a ha b hb e

theorem c_pts : ruFiveC0Cert.pts =
    Array.ofFn (n := 1000) fun i => treeArr 4060 ruFiveC0Gens C0.P C0.L i.val :=
  enumBfs_tree ctree cgs (by rfl) (by norm_num) (by norm_num) ckeys_inj cedges kCReplay

theorem c_enum : enumOK 4060 ruFiveC0Gens ruFiveKeys ruFiveC0Cert = true :=
  enumOK_tree ctree cgs (by rfl) (by norm_num) (by norm_num) ckeys_inj cedges

theorem c_size : ruFiveC0Cert.pts.size = 1000 := by rw [c_pts, Array.size_ofFn]

theorem c_get {k : Nat} (hk : k < 1000) :
    ruFiveC0Cert.pts[k]! = treeArr 4060 ruFiveC0Gens C0.P C0.L k := by
  rw [c_pts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem c_rep {k : Nat} (hk : k < 1000) :
    Rep 4060 ruFiveC0Cert.pts[k]! (treePerm gpC C0.P C0.L k) := by
  rw [c_get hk]
  exact rep_treeArr ctree cgs k hk

theorem c_repF {k : Nat} (hk : k < 1000) : RepF 4060 (cv k) (treePerm gpC C0.P C0.L k) :=
  repF_trV ctree cg 1000 k hk.le hk

theorem c_mem {k : Nat} (hk : k < 1000) : treePerm gpC C0.P C0.L k ∈ ruP :=
  (trQ_spec ctree hmul cg_mem (fun k hk => iff_of_true (cg_mem k hk) rfl) (fun _ _ => by decide)
    1000 k hk.le hk).1

theorem csk_lt : ∀ j < 1000, C0.SK j < 1000 := sk_lt fun j hj => by
  have h := Orb.allN_iff.1 kCSort j hj
  unfold sortAtK at h
  rw [bAnd_iff, bAnd_iff, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1⟩

theorem agens_eq (k : Nat) (hk : k < 3) : ruFiveA0Gens[k]! = unpack 4060 12 (F (70 + k)) := by
  rw [ruFiveA0Gens]
  interval_cases k
  · exact (lit3_0 _ _ _).trans (arr_eq 70 (by norm_num))
  · exact (lit3_1 _ _ _).trans (arr_eq 71 (by norm_num))
  · exact (lit3_2 _ _ _).trans (arr_eq 72 (by norm_num))

@[expose] noncomputable def gpA (k : Nat) : Equiv.Perm (Fin 4060) := gp (70 + k)

theorem ags : ∀ k < 3, Rep 4060 ruFiveA0Gens[k]! (gpA k) := fun k hk => by
  rw [agens_eq k hk]
  exact rep_gp _ (by omega)

theorem ag : ∀ k < 3, RepF 4060 (gA k) (gpA k) := fun k hk => repF_pa (70 + k) (by omega)

theorem ag_mem : ∀ k < 3, gpA k ∈ ruP := fun k hk => gp_mem _ (by omega)

theorem atree : TreeOK 3 125 A0.P A0.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kATree i hi
  rwa [beq_zero_false h0] at h

theorem aedges : ∀ i < 125, ∀ k < 3, AE i k < 125 ∧
    treeArr 4060 ruFiveA0Gens A0.P A0.L (AE i k) =
      compA 4060 ruFiveA0Gens[k]! (treeArr 4060 ruFiveA0Gens A0.P A0.L i) :=
  edges_of_edgeAtK atree ag ags hmul ag_mem (fun k hk => iff_of_true (ag_mem k hk) rfl)
    (fun _ _ => by decide) bs_lt hF fun i hi => Orb.allN_iff.1 kAEdge i hi

theorem akeys_inj : ∀ a < 125, ∀ b < 125,
    keyA 4060 ruFiveKeys (treeArr 4060 ruFiveA0Gens A0.P A0.L a) =
      keyA 4060 ruFiveKeys (treeArr 4060 ruFiveA0Gens A0.P A0.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := akey) fun j hj => Orb.allN_iff.1 kASort j hj
  intro a ha b hb e
  rw [keyA_treeArr atree ag ags keys_lt ha, keyA_treeArr atree ag ags keys_lt hb] at e
  exact hk a ha b hb e

theorem a_pts : ruFiveA0Cert.pts =
    Array.ofFn (n := 125) fun i => treeArr 4060 ruFiveA0Gens A0.P A0.L i.val :=
  enumBfs_tree atree ags (by rfl) (by norm_num) (by norm_num) akeys_inj aedges kAReplay

theorem a_enum : enumOK 4060 ruFiveA0Gens ruFiveKeys ruFiveA0Cert = true :=
  enumOK_tree atree ags (by rfl) (by norm_num) (by norm_num) akeys_inj aedges

theorem a_size : ruFiveA0Cert.pts.size = 125 := by rw [a_pts, Array.size_ofFn]

theorem a_get {k : Nat} (hk : k < 125) :
    ruFiveA0Cert.pts[k]! = treeArr 4060 ruFiveA0Gens A0.P A0.L k := by
  rw [a_pts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem a_rep {k : Nat} (hk : k < 125) :
    Rep 4060 ruFiveA0Cert.pts[k]! (treePerm gpA A0.P A0.L k) := by
  rw [a_get hk]
  exact rep_treeArr atree ags k hk

theorem a_repF {k : Nat} (hk : k < 125) : RepF 4060 (av k) (treePerm gpA A0.P A0.L k) :=
  repF_trV atree ag 125 k hk.le hk

theorem a_mem {k : Nat} (hk : k < 125) : treePerm gpA A0.P A0.L k ∈ ruP :=
  (trQ_spec atree hmul ag_mem (fun k hk => iff_of_true (ag_mem k hk) rfl) (fun _ _ => by decide)
    125 k hk.le hk).1

theorem x0_rep : Rep 4060 ruFiveLines[0]! (gp 2) := rep_line 0 (by norm_num)

theorem x0_repF : RepF 4060 x0 (gp 2) := repF_pa 2 (by norm_num)

theorem x0_mem : gp 2 ∈ ruP := gp_mem 2 (by norm_num)

theorem base0_lt : ∀ t < 9, ruCase0BaseArr[t]! < 4060 := by decide

theorem rels0_ok : relsOKP 5 4060 ruCase0BaseArr ruFiveLines[0]! ruCase0Rels = true := by
  rw [relsOKP, List.all_eq_true]
  intro r hr
  have h := List.all_eq_true.1 kRels0 r hr
  unfold relAt0 at h
  simp only [bAnd_iff, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs : ruCase0BaseArr.size = 9 := by decide
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hs]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  rw [(rep_powArr x0_rep r.2.2).apply (base0_lt _ h2), ← (RepF.powF x0_repF r.2.2) _ (base0_lt _ h2)]
  exact Nat.eq_of_beq_eq_true h4

theorem tabs0 : TabsT 4060 12 8 9 S50.BP T50.NR T50.NR S50.S S50.SI S50.LR T50.Ts T50.LT T50.PT
    T50.QT 64 1024 4 1024 :=
  ⟨by decide, by decide, by decide, by decide, TS0.all, LT0.all, pt0B_all, qt0B_all⟩

theorem tc0 : TabChain 4060 12 8 9 S50.BP 64 64 T50.NR T50.NR 64 1024 4 1024 S50.S S50.SI
    S50.LR T50.Ts T50.LT T50.PT T50.QT ruCase0Arrs ruCase0BaseArr ruFiveKeys :=
  ⟨binds0, kPerm0, S50.ho, by norm_num, tabs0, rfl⟩

theorem fr0_ok : ∀ i < 9, fr0 i = 0 ∨ ∃ l e, fr0 i = 8 * l + e + 1 ∧ l < i ∧ e < 8 ∧
    (l, i, e) ∈ ruCase0Rels := by
  intro i hi
  have h := Orb.allN_iff.1 kFR0 i hi
  by_cases h0 : fr0 i = 0
  · exact Or.inl h0
  · right
    rw [show Nat.beq (fr0 i) 0 = false from Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)] at h
    simp only [bAnd_iff, Nat.blt_eq, List.any_eq_true] at h
    obtain ⟨h1, h2, r, hr, hr1, hr2, hr3⟩ := h
    refine ⟨(fr0 i - 1) / 8, (fr0 i - 1) % 8, by omega, h1, by omega, ?_⟩
    have e1 := Nat.eq_of_beq_eq_true hr1
    have e2 := Nat.eq_of_beq_eq_true hr2
    have e3 := Nat.eq_of_beq_eq_true hr3
    obtain ⟨a, b, c⟩ := r
    have e : (a, b, c) = ((fr0 i - 1) / 8, i, (fr0 i - 1) % 8) := by
      simp only [Prod.mk.injEq]
      exact ⟨e1, e2, e3⟩
    rw [← e]
    exact hr

theorem tail0 : ptailOK 4060 (rawLevels 4060 ruCase0Arrs ruCase0BaseArr) ruCase0BaseArr
    ruFiveLines[0]! (powPA 5 4060 ruFiveLines[0]!) ruCase0Rels ruFiveC0Cert.pts.toList 9 0
    (idA 4060) = true := by
  refine ptailOK_of_ptK_ tc0 x0_rep x0_repF (fun r hr => ?_) fr0_ok bs_lt ?_ (by norm_num) kTail0
  · have h := List.all_eq_true.1 kRels0 r hr
    unfold relAt0 at h
    rw [bAnd_iff, Nat.blt_eq] at h
    exact h.1
  · intro a A ha hA ⟨j, hj, e⟩
    have hR : A ∈ ruP := by
      refine (Subgroup.closure_le _).2 ?_ hA
      rintro _ ⟨i, rfl⟩
      exact faith0.2 i (by rw [hsize0]; exact i.2)
    have hm := csk_lt j hj
    unfold ckey cv at e
    rw [← keyA_treeArr ctree cg cgs keys_lt hm, ← c_get hm] at e
    have he := key_faith ha (c_rep hm) hR (c_mem hm) e
    exact any_mem (by rw [c_size]; exact hm) ((eqA_iff ha (c_rep hm)).2 he)

theorem cent0 : centOK 4060 ruCase0Arrs ruCase0BaseArr ruFiveLines[0]! ruCase0Rels ruFiveC0Gens
    ruFiveKeys ruFiveC0Cert 1000 = true := by
  change centOKP 5 4060 ruCase0Arrs ruCase0BaseArr ruFiveLines[0]! ruCase0Rels ruFiveC0Gens
    ruFiveKeys ruFiveC0Cert 1000 = true
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  have hs : ruCase0BaseArr.size = 9 := by decide
  refine ⟨⟨⟨⟨⟨rels0_ok, c_enum⟩, c_size⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, by rw [hs]; exact tail0⟩
  · have hk3 : k < 3 := hk
    exact commA_R (cgs k hk3) x0_rep (cg k hk3) x0_repF (cg_mem k hk3) x0_mem
      (Orb.allN_iff.1 kComm0 k hk3)
  · have hk3 : k < 3 := hk
    exact (sift0_iff (cgs k hk3)).2 (cg_mem k hk3)

theorem normal0 : normalOK 4060 ruFiveC0Gens ruFiveA0Gens ruFiveKeys ruFiveC0Cert ruFiveA0Cert 125
    ruPLevels ruCase0BaseArr = true := by
  change normalOKP 5 4060 ruFiveC0Gens ruFiveA0Gens ruFiveKeys ruFiveC0Cert ruFiveA0Cert 125
    ruPLevels ruCase0BaseArr = true
  simp only [normalOKP, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨⟨a_enum, a_size⟩, fun k hk => ?_⟩, fun l hl => ?_⟩, fun k hk => ?_⟩, fun l hl => ?_⟩
  · rw [a_size] at hk
    exact eqA_R (rep_powArr (a_rep hk) 5) rep_idA (RepF.powF (a_repF hk) 5) RepF.one
      (ruP.pow_mem (a_mem hk) 5) ruP.one_mem (Orb.allN_iff.1 kAPow k hk)
  · have hl3 : l < 3 := hl
    have h := Orb.allN_iff.1 kAinC l hl3
    rw [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨h1, h3⟩ := h
    refine any_mem (by rw [c_size]; exact h1) ?_
    exact eqA_R (ags l hl3) (c_rep h1) (ag l hl3) (c_repF h1) (ag_mem l hl3) (c_mem h1)
      (eqOnL_symm h3)
  · have hk3 : k < 3 := hk
    intro l hl
    have hl3 : l < 3 := hl
    have h := Orb.allN_iff.1 kConj (3 * k + l) (by omega)
    rw [show Nat.div (3 * k + l) 3 = k by change (3 * k + l) / 3 = k; omega,
      show Nat.mod (3 * k + l) 3 = l by change (3 * k + l) % 3 = l; omega] at h
    rw [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine any_mem (by rw [a_size]; exact h1) ?_
    have hc := rep_conjA (CFSG.RankThree.Native.F2.validA_of_rep (cgs k hk3)) (ags l hl3)
    rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (cgs k hk3)] at hc
    have hcf : RepF 4060 (fun y => gC k (gA l (pi (Nat.add 64 k) y)))
        (gpC k * gpA l * (gpC k)⁻¹) := by
      have := (cg k hk3).comp ((ag l hl3).comp (repF_pi (64 + k) (by omega)))
      rw [mul_assoc]
      exact this
    have hP : gpC k * gpA l * (gpC k)⁻¹ ∈ ruP :=
      ruP.mul_mem (ruP.mul_mem (cg_mem k hk3) (ag_mem l hl3)) (ruP.inv_mem (cg_mem k hk3))
    exact eqA_R hc (a_rep h1) hcf (a_repF h1) hP (a_mem h1) (eqOnL_symm h2)
  · have hl3 : l < 3 := hl
    exact (sift0_iff (ags l hl3)).2 (ag_mem l hl3)

theorem zcent0 : zCentOK 4060 ruFiveA0Gens ruFiveC0Cert ruFiveA0Cert ruFiveLines[0]! = true := by
  change zCentOKP 5 4060 ruFiveA0Gens ruFiveC0Cert ruFiveA0Cert ruFiveLines[0]! = true
  simp only [zCentOKP, Bool.and_eq_true, allLt_iff]
  have hx := kXinA
  rw [bAnd_iff, Nat.blt_eq] at hx
  refine ⟨any_mem (by rw [a_size]; exact hx.1)
    (eqA_R x0_rep (a_rep hx.1) x0_repF (a_repF hx.1) x0_mem (a_mem hx.1) (eqOnL_symm hx.2)),
    fun c hc => ?_⟩
  rw [c_size] at hc
  have hz := Orb.allN_iff.1 kZ0 c hc
  unfold zAt0 at hz
  rw [CFSG.KS.SporSch.strictB_val] at hz
  rw [Bool.or_eq_true]
  by_cases hw : ZW0.getD c 0 < 100
  · rw [show Nat.blt (ZW0.getD c 0) 100 = true from Nat.blt_eq.mpr hw] at hz
    simp only [bAnd_iff, Nat.blt_eq, Bool.not_eq_true'] at hz
    obtain ⟨h1, h2, h3⟩ := hz
    left
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro hall
    have hl : ZW0.getD c 0 - 1 < 3 := by omega
    have hcomm := (allLt_iff.1 hall) _ (show ZW0.getD c 0 - 1 < ruFiveA0Gens.size from hl)
    have e := (eqA_iff (rep_compA (c_rep hc) (ags _ hl)) (rep_compA (ags _ hl) (c_rep hc))).1 hcomm
    have := eqOnL_of_eq bs_lt ((c_repF hc).comp (ag _ hl)) ((e ▸ (ag _ hl).comp (c_repF hc)))
    rw [Bool.eq_false_iff] at h3
    exact h3 this
  · rw [show Nat.blt (ZW0.getD c 0) 100 = false from Bool.eq_false_iff.2 fun h =>
      hw (Nat.blt_eq.mp h)] at hz
    simp only [bAnd_iff, Nat.blt_eq] at hz
    obtain ⟨h1, h3⟩ := hz
    right
    rw [List.any_eq_true]
    refine ⟨ZW0.getD c 0 - 100, List.mem_range.2 h1, ?_⟩
    exact eqA_R (c_rep hc) (rep_powArr x0_rep _) (c_repF hc) (RepF.powF x0_repF _)
      (c_mem hc) (ruP.pow_mem x0_mem _) h3

theorem eq0 : eqA 4060 ruFiveC0Gens[0]! ruFiveLines[0]! = true := by
  rw [cgens_eq 0 (by norm_num), Nat.eq_of_beq_eq_true kEq0, ← arr_eq 2 (by norm_num)]
  rw [ruFiveLines, getElem!_pos _ 0 (by simp), Array.getElem_ofFn]
  exact eqA_self' _

theorem case0 : caseChainOK2 4060 ruCase0Arrs ruCase0BaseArr ruCase0Words (ruArr4060 0)
      (ruArr4060 1) = true ∧
    rawOrbitSizes 4060 ruCase0Arrs ruCase0BaseArr = [4060, 1755, 1024, 4, 5, 1, 1, 1, 1] ∧
    validA 4060 (ruArr4060 0) = true ∧ validA 4060 (ruArr4060 1) = true ∧
    centOK 4060 ruCase0Arrs ruCase0BaseArr ruFiveLines[0]! ruCase0Rels ruFiveC0Gens ruFiveKeys
      ruFiveC0Cert 1000 = true ∧
    normalOK 4060 ruFiveC0Gens ruFiveA0Gens ruFiveKeys ruFiveC0Cert ruFiveA0Cert 125 ruPLevels
      ruCase0BaseArr = true ∧
    zCentOK 4060 ruFiveA0Gens ruFiveC0Cert ruFiveA0Cert ruFiveLines[0]! = true ∧
    eqA 4060 ruFiveC0Gens[0]! ruFiveLines[0]! = true :=
  ⟨chain0, orb0, valid_a0, valid_a1, cent0, normal0, zcent0, eq0⟩

end CertificateChecks.KernelRuFive

end
