module

public import Certificates.Kernel.HeLoc.Seven0K
public import Certificates.Kernel.HeLoc.SevenQFacts
public import CFSG.Certificates.Kernel.HeLoc.PTailSound
public import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Schreier.PairHeClasses

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.RankThree.Native
open CFSG.RankThree.PartOne CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

theorem eqA_R {t u : Array Nat} {x y : Equiv.Perm (Fin 8330)} {f f' : Nat → Nat}
    (ht : Rep 8330 t x) (hu : Rep 8330 u y) (hf : RepF 8330 f x) (hf' : RepF 8330 f' y)
    (hx : x ∈ heAutGroup) (hy : y ∈ heAutGroup) (hxy : x ∈ heP ↔ y ∈ heP)
    (h : eqOnL bs f f' = true) : eqA 8330 t u = true :=
  (eqA_iff ht hu).2 (faithful x hx y hy hxy fun b hb => by
    rw [← hf b (bs_lt b hb), ← hf' b (bs_lt b hb)]
    exact (eqOnL_iff _ _ _).1 h b hb)

theorem comm_par {a b : Equiv.Perm (Fin 8330)} (ha : a ∈ heAutGroup) (hb : b ∈ heAutGroup) :
    a * b ∈ heP ↔ b * a ∈ heP := by
  rw [he_mul_mem_iff ha hb, he_mul_mem_iff hb ha]
  exact Iff.comm

theorem commA_R {t u : Array Nat} {x y : Equiv.Perm (Fin 8330)} {f f' : Nat → Nat}
    (ht : Rep 8330 t x) (hu : Rep 8330 u y) (hf : RepF 8330 f x) (hf' : RepF 8330 f' y)
    (hx : x ∈ heAutGroup) (hy : y ∈ heAutGroup)
    (h : eqOnL bs (fun z => f (f' z)) (fun z => f' (f z)) = true) : commA 8330 t u = true :=
  eqA_R (rep_compA ht hu) (rep_compA hu ht) (hf.comp hf') (hf'.comp hf)
    (heAutGroup.mul_mem hx hy) (heAutGroup.mul_mem hy hx) (comm_par hx hy) h

@[expose] noncomputable def gpC (k : Nat) : Equiv.Perm (Fin 8330) := gp (59 + k)

theorem cgens_eq (k : Nat) (hk : k < 3) : heSevenC0Gens[k]! = unpack 8330 14 (A (59 + k)) := by
  rw [heSevenC0Gens]
  interval_cases k
  · exact (lit3_0 _ _ _).trans (arr_eq 59 (by norm_num))
  · exact (lit3_1 _ _ _).trans (arr_eq 60 (by norm_num))
  · exact (lit3_2 _ _ _).trans (arr_eq 61 (by norm_num))

theorem cgs : ∀ k < 3, Rep 8330 heSevenC0Gens[k]! (gpC k) := fun k hk => by
  rw [cgens_eq k hk]
  exact rep_gp _ (by omega)

theorem cg : ∀ k < 3, RepF 8330 (gC k) (gpC k) := fun k hk => repF_pa (59 + k) (by omega)

theorem cg_mem : ∀ k < 3, gpC k ∈ heAutGroup := fun k hk => (gp_mem _ (by omega)).1

theorem cg_par : ∀ k < 3, (gpC k ∈ heP ↔ qC k = 0) := fun k hk => (gp_mem _ (by omega)).2

theorem cq_lt : ∀ k < 3, qC k < 2 := fun k hk => (nf_k (59 + k) (by omega)).2

theorem hmulR : ∀ a ∈ heAutGroup, ∀ b ∈ heAutGroup, (a * b ∈ heP ↔ (a ∈ heP ↔ b ∈ heP)) :=
  fun a ha b hb => he_mul_mem_iff ha hb

theorem ctree : TreeOK 3 2058 C0.P C0.L := treeOK_of fun i hi h0 => by
  have h := allN_spec kCTree i hi
  rwa [beq_zero_false h0] at h

theorem cedges : ∀ i < 2058, ∀ k < 3, CE i k < 2058 ∧
    treeArr 8330 heSevenC0Gens C0.P C0.L (CE i k) =
      compA 8330 heSevenC0Gens[k]! (treeArr 8330 heSevenC0Gens C0.P C0.L i) :=
  edges_of_edgeAtK ctree cg cgs hmulR cg_mem cg_par cq_lt bs_lt faithful
    fun i hi => allN_spec kCEdge i hi

theorem ckeys_inj : ∀ a < 2058, ∀ b < 2058,
    keyA 8330 heSevenKeys (treeArr 8330 heSevenC0Gens C0.P C0.L a) =
      keyA 8330 heSevenKeys (treeArr 8330 heSevenC0Gens C0.P C0.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := ckey) fun j hj => allN_spec kCSort j hj
  intro a ha b hb e
  rw [keyA_treeArr ctree cg cgs keys_lt ha, keyA_treeArr ctree cg cgs keys_lt hb] at e
  exact hk a ha b hb e

theorem c_pts : heSevenC0Cert.pts =
    Array.ofFn (n := 2058) fun i => treeArr 8330 heSevenC0Gens C0.P C0.L i.val :=
  enumBfs_tree ctree cgs (by rfl) (by norm_num) (by norm_num) ckeys_inj cedges kCReplay

theorem c_enum : enumOK 8330 heSevenC0Gens heSevenKeys heSevenC0Cert = true :=
  enumOK_tree ctree cgs (by rfl) (by norm_num) (by norm_num) ckeys_inj cedges

theorem c_size : heSevenC0Cert.pts.size = 2058 := by rw [c_pts, Array.size_ofFn]

theorem c_get {k : Nat} (hk : k < 2058) :
    heSevenC0Cert.pts[k]! = treeArr 8330 heSevenC0Gens C0.P C0.L k := by
  rw [c_pts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem c_rep {k : Nat} (hk : k < 2058) :
    Rep 8330 heSevenC0Cert.pts[k]! (treePerm gpC C0.P C0.L k) := by
  rw [c_get hk]
  exact rep_treeArr ctree cgs k hk

theorem c_repF {k : Nat} (hk : k < 2058) : RepF 8330 (cv k) (treePerm gpC C0.P C0.L k) :=
  repF_trV ctree cg 2058 k hk.le hk

theorem c_mem {k : Nat} (hk : k < 2058) : treePerm gpC C0.P C0.L k ∈ heAutGroup ∧
    (treePerm gpC C0.P C0.L k ∈ heP ↔ cq k = 0) := by
  obtain ⟨h1, h2, -⟩ := trQ_spec ctree hmulR cg_mem cg_par cq_lt 2058 k hk.le hk
  exact ⟨h1, h2⟩

@[expose] noncomputable def gpA (k : Nat) : Equiv.Perm (Fin 8330) := gp (62 + k)

theorem agens_eq (k : Nat) (hk : k < 3) : heSevenA0Gens[k]! = unpack 8330 14 (A (62 + k)) := by
  rw [heSevenA0Gens]
  interval_cases k
  · exact (lit3_0 _ _ _).trans (arr_eq 62 (by norm_num))
  · exact (lit3_1 _ _ _).trans (arr_eq 63 (by norm_num))
  · exact (lit3_2 _ _ _).trans (arr_eq 64 (by norm_num))

theorem ags : ∀ k < 3, Rep 8330 heSevenA0Gens[k]! (gpA k) := fun k hk => by
  rw [agens_eq k hk]
  exact rep_gp _ (by omega)

theorem ag : ∀ k < 3, RepF 8330 (gA k) (gpA k) := fun k hk => repF_pa (62 + k) (by omega)

theorem fl_a : FL.getD 62 0 = 0 ∧ FL.getD 63 0 = 0 ∧ FL.getD 64 0 = 0 := by decide

theorem ag_inP : ∀ k < 3, gpA k ∈ heP := by
  intro k hk
  have h := fl_a
  interval_cases k
  · exact (gp_mem 62 (by norm_num)).2.2 h.1
  · exact (gp_mem 63 (by norm_num)).2.2 h.2.1
  · exact (gp_mem 64 (by norm_num)).2.2 h.2.2

theorem atree : TreeOK 3 343 A0.P A0.L := treeOK_of fun i hi h0 => by
  have h := allN_spec kATree i hi
  rwa [beq_zero_false h0] at h

theorem aedges : ∀ i < 343, ∀ k < 3, AE i k < 343 ∧
    treeArr 8330 heSevenA0Gens A0.P A0.L (AE i k) =
      compA 8330 heSevenA0Gens[k]! (treeArr 8330 heSevenA0Gens A0.P A0.L i) :=
  edges_of_edgeAtK atree ag ags hmulP ag_inP (fun k hk => iff_of_true (ag_inP k hk) rfl)
    (fun _ _ => by decide) bs_lt
    (fun x hx y hy _ hb => faithful x (heP_le_heAutGroup hx) y (heP_le_heAutGroup hy)
      (iff_of_true hx hy) hb) fun i hi => allN_spec kAEdge i hi

theorem akeys_inj : ∀ a < 343, ∀ b < 343,
    keyA 8330 heSevenKeys (treeArr 8330 heSevenA0Gens A0.P A0.L a) =
      keyA 8330 heSevenKeys (treeArr 8330 heSevenA0Gens A0.P A0.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := akey) fun j hj => allN_spec kASort j hj
  intro a ha b hb e
  rw [keyA_treeArr atree ag ags keys_lt ha, keyA_treeArr atree ag ags keys_lt hb] at e
  exact hk a ha b hb e

theorem a_pts : heSevenA0Cert.pts =
    Array.ofFn (n := 343) fun i => treeArr 8330 heSevenA0Gens A0.P A0.L i.val :=
  enumBfs_tree atree ags (by rfl) (by norm_num) (by norm_num) akeys_inj aedges kAReplay

theorem a_enum : enumOK 8330 heSevenA0Gens heSevenKeys heSevenA0Cert = true :=
  enumOK_tree atree ags (by rfl) (by norm_num) (by norm_num) akeys_inj aedges

theorem a_size : heSevenA0Cert.pts.size = 343 := by rw [a_pts, Array.size_ofFn]

theorem a_get {k : Nat} (hk : k < 343) :
    heSevenA0Cert.pts[k]! = treeArr 8330 heSevenA0Gens A0.P A0.L k := by
  rw [a_pts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem a_rep {k : Nat} (hk : k < 343) :
    Rep 8330 heSevenA0Cert.pts[k]! (treePerm gpA A0.P A0.L k) := by
  rw [a_get hk]
  exact rep_treeArr atree ags k hk

theorem a_repF {k : Nat} (hk : k < 343) : RepF 8330 (av k) (treePerm gpA A0.P A0.L k) :=
  repF_trV atree ag 343 k hk.le hk

theorem a_inP {k : Nat} (hk : k < 343) : treePerm gpA A0.P A0.L k ∈ heP :=
  (trQ_spec atree hmulP ag_inP (fun k hk => iff_of_true (ag_inP k hk) rfl) (fun _ _ => by decide)
    343 k hk.le hk).1

theorem any_mem {c : CFSG.Monster.B.Fischer.ArrCert} {t : Array Nat} {k : Nat}
    (hk : k < c.pts.size) (h : eqA 8330 t c.pts[k]! = true) : c.pts.toList.any (eqA 8330 t) = true := by
  rw [List.any_eq_true]
  refine ⟨c.pts[k]!, ?_, h⟩
  rw [getElem!_pos c.pts k hk]
  exact Array.getElem_mem_toList _

theorem x0_rep : Rep 8330 heSevenLines[0]! (lp 0) := rep_line 0 (by norm_num)

theorem x0_repF : RepF 8330 x0 (lp 0) := repF_ln 0 (by norm_num)

theorem x0_inP : lp 0 ∈ heP := lp_inP 0 (by norm_num)

theorem lp0_eq : lp 0 = gp 59 := by
  rw [lp, gp_one 0 (by norm_num), one_mul, inv_one, mul_one]
  rfl

theorem x0_mem : lp 0 ∈ heAutGroup := heP_le_heAutGroup x0_inP

theorem eqOnL_symm {l : List Nat} {f g : Nat → Nat} (h : eqOnL l f g = true) : eqOnL l g f = true :=
  (eqOnL_iff _ _ _).2 fun b hb => ((eqOnL_iff _ _ _).1 h b hb).symm

theorem faith0 : CFSG.Sporadic.Schreier.BaseFaithful heAutGroup heSevenKeys ∧
    ∀ j < heSevenCase0Arrs.size, permOfArr 8330 heSevenCase0Arrs[j]! ∈ heAutGroup :=
  case_faithful (by norm_num) (by simp [heSevenCase0Arrs]) (by decide) chain0

theorem key_faith {a b : Array Nat} {A B : Equiv.Perm (Fin 8330)} (ha : Rep 8330 a A)
    (hb : Rep 8330 b B) (hA : A ∈ heAutGroup) (hB : B ∈ heAutGroup)
    (h : keyA 8330 heSevenKeys a = keyA 8330 heSevenKeys b) : A = B := by
  have hl := Nat.ofDigits_inj_of_len_eq (b := 8330) (by norm_num) (by simp)
    (fun l hl => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      rw [ha.apply (keys_lt p hp)]
      exact (A _).2)
    (fun l hl => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      rw [hb.apply (keys_lt p hp)]
      exact (B _).2) h
  have hpt : ∀ p (hp : p ∈ heSevenKeys), (A ⟨p, keys_lt p hp⟩ : Nat) = B ⟨p, keys_lt p hp⟩ := by
    intro p hp
    have := List.map_inj_left.1 hl p hp
    rwa [ha.apply (keys_lt p hp), hb.apply (keys_lt p hp)] at this
  have h1 := faith0.1 (B⁻¹ * A) (heAutGroup.mul_mem (heAutGroup.inv_mem hB) hA) fun x hx => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact Fin.ext (hpt x hx)
  exact (inv_mul_eq_one.1 h1).symm

theorem sk_lt {SK SKI : Nat → Nat} {N : Nat}
    (h : ∀ j < N, SKI j < N ∧ SK (SKI j) = j) : ∀ j < N, SK j < N := by
  have hinj : Set.InjOn SKI (Finset.range N : Set Nat) := fun a ha b hb e => by
    rw [← (h a (by simpa using ha)).2, ← (h b (by simpa using hb)).2, e]
  have himg : (Finset.range N).image SKI = Finset.range N := Finset.eq_of_subset_of_card_le
    (fun y hy => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_range.2 (h a (by simpa using ha)).1)
    (by rw [Finset.card_image_of_injOn hinj])
  intro j hj
  have : j ∈ (Finset.range N).image SKI := by rw [himg]; simpa using hj
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 this
  rw [(h a (by simpa using ha)).2]
  simpa using ha

theorem csk_lt : ∀ j < 2058, C0.SK j < 2058 := sk_lt fun j hj => by
  have h := allN_spec kCSort j hj
  unfold sortAtK at h
  rw [bAnd_iff, bAnd_iff, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1⟩

theorem base0_lt : ∀ t < 14, heSevenCase0BaseArr[t]! < 8330 := by decide

theorem rels_ok : relsOKP 7 8330 heSevenCase0BaseArr heSevenLines[0]! heSevenCase0Rels = true := by
  rw [relsOKP, List.all_eq_true]
  intro r hr
  have h := List.all_eq_true.1 kRels r hr
  unfold relAt at h
  simp only [bAnd_iff, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs : heSevenCase0BaseArr.size = 14 := by decide
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hs]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  rw [(rep_powArr x0_rep r.2.2).apply (base0_lt _ h2), ← (RepF.powF x0_repF r.2.2) _ (base0_lt _ h2)]
  exact Nat.eq_of_beq_eq_true h4

theorem tabs0 : TabsT 8330 14 10 14 S70.BP T70.NR T70.NR S70.S S70.SI S70.LR T70.Ts T70.LT T70.PT
    T70.QT 163 1024 9 1024 :=
  ⟨by decide, by decide, by decide, by decide, TS0.all, LT0.all, pt0B_all, qt0B_all⟩

theorem tc0 : TabChain 8330 14 10 14 S70.BP 131 64 T70.NR T70.NR 163 1024 9 1024 S70.S S70.SI
    S70.LR T70.Ts T70.LT T70.PT T70.QT heSevenCase0Arrs heSevenCase0BaseArr heSevenKeys :=
  ⟨binds0, k0Perm, S70.ho, by norm_num, tabs0, rfl⟩

theorem fr_ok : ∀ i < 14, fr0 i = 0 ∨ ∃ l e, fr0 i = 8 * l + e + 1 ∧ l < i ∧ e < 8 ∧
    (l, i, e) ∈ heSevenCase0Rels := by
  intro i hi
  have h := allN_spec kFR i hi
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

theorem tail0 : ptailOK 8330 (rawLevels 8330 heSevenCase0Arrs heSevenCase0BaseArr)
    heSevenCase0BaseArr heSevenLines[0]! (powPA 7 8330 heSevenLines[0]!) heSevenCase0Rels
    heSevenC0Cert.pts.toList 14 0 (idA 8330) = true := by
  refine ptailOK_of_ptK_ tc0 x0_rep x0_repF (fun r hr => ?_) fr_ok bs_lt ?_ (by norm_num) kTail
  · have h := List.all_eq_true.1 kRels r hr
    unfold relAt at h
    rw [bAnd_iff, Nat.blt_eq] at h
    exact h.1
  · intro a A ha hA ⟨j, hj, e⟩
    have hR : A ∈ heAutGroup := by
      refine (Subgroup.closure_le _).2 ?_ hA
      rintro _ ⟨i, rfl⟩
      exact faith0.2 i (by simpa [heSevenCase0Arrs] using i.2)
    have hm := csk_lt j hj
    unfold ckey cv at e
    rw [← keyA_treeArr ctree cg cgs keys_lt hm, ← c_get hm] at e
    have he := key_faith ha (c_rep hm) hR (c_mem hm).1 e
    exact any_mem (by rw [c_size]; exact hm) ((eqA_iff ha (c_rep hm)).2 he)

theorem cent0 : centOKP 7 8330 heSevenCase0Arrs heSevenCase0BaseArr heSevenLines[0]!
    heSevenCase0Rels heSevenC0Gens heSevenKeys heSevenC0Cert 2058 = true := by
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  have hs : heSevenCase0BaseArr.size = 14 := by decide
  refine ⟨⟨⟨⟨⟨rels_ok, c_enum⟩, c_size⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, by rw [hs]; exact tail0⟩
  · have hk3 : k < 3 := hk
    exact commA_R (cgs k hk3) x0_rep (cg k hk3) x0_repF (cg_mem k hk3) x0_mem
      (allN_spec kComm k hk3)
  · have hk3 : k < 3 := hk
    exact (sift0_iff (cgs k hk3)).2 (cg_mem k hk3)

theorem normal0 : normalOKP 7 8330 heSevenC0Gens heSevenA0Gens heSevenKeys heSevenC0Cert
    heSevenA0Cert 343 heLevels heBase.toArray = true := by
  simp only [normalOKP, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨⟨a_enum, a_size⟩, fun k hk => ?_⟩, fun l hl => ?_⟩, fun k hk => ?_⟩, fun l hl => ?_⟩
  · rw [a_size] at hk
    exact eqA_P (rep_powArr (a_rep hk) 7) rep_idA (RepF.powF (a_repF hk) 7) RepF.one
      (heP.pow_mem (a_inP hk) 7) heP.one_mem (allN_spec kAPow k hk)
  · have hl3 : l < 3 := hl
    have h := allN_spec kAinC l hl3
    simp only [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine any_mem (by rw [c_size]; exact h1) ?_
    exact eqA_P (ags l hl3) (c_rep h1) (ag l hl3) (c_repF h1) (ag_inP l hl3)
      ((c_mem h1).2.2 (Nat.eq_of_beq_eq_true h2)) (eqOnL_symm h3)
  · have hk3 : k < 3 := hk
    intro l hl
    have hl3 : l < 3 := hl
    have h := allN_spec kConj (3 * k + l) (by omega)
    rw [show Nat.div (3 * k + l) 3 = k by change (3 * k + l) / 3 = k; omega,
      show Nat.mod (3 * k + l) 3 = l by change (3 * k + l) % 3 = l; omega] at h
    rw [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine any_mem (by rw [a_size]; exact h1) ?_
    have hc := rep_conjA (CFSG.RankThree.Native.F2.validA_of_rep (cgs k hk3)) (ags l hl3)
    rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (cgs k hk3)] at hc
    have hcf : RepF 8330 (fun y => gC k (gA l (pi (Nat.add 59 k) y)))
        (gpC k * gpA l * (gpC k)⁻¹) := by
      have := (cg k hk3).comp ((ag l hl3).comp (repF_pi (59 + k) (by omega)))
      rw [mul_assoc]
      exact this
    have hP : gpC k * gpA l * (gpC k)⁻¹ ∈ heP := by
      have hn := heP_normal_heAutGroup
      have := hn.conj_mem ⟨gpA l, heP_le_heAutGroup (ag_inP l hl3)⟩
        (by rw [Subgroup.mem_subgroupOf]; exact ag_inP l hl3) ⟨gpC k, cg_mem k hk3⟩
      rwa [Subgroup.mem_subgroupOf] at this
    exact eqA_P hc (a_rep h1) hcf (a_repF h1) hP (a_inP h1) (eqOnL_symm h2)
  · have hl3 : l < 3 := hl
    rw [show heLevels = rawLevels 8330 heStrongArrs heBase.toArray from rfl,
      mem_heP_iff_siftA (ags l hl3)]
    exact ag_inP l hl3

theorem zcent0 : zCentOKP 7 8330 heSevenA0Gens heSevenC0Cert heSevenA0Cert heSevenLines[0]! =
    true := by
  simp only [zCentOKP, Bool.and_eq_true, allLt_iff]
  have hx := kXinA
  rw [bAnd_iff, Nat.blt_eq] at hx
  refine ⟨any_mem (by rw [a_size]; exact hx.1)
    (eqA_P x0_rep (a_rep hx.1) x0_repF (a_repF hx.1) x0_inP (a_inP hx.1) (eqOnL_symm hx.2)),
    fun c hc => ?_⟩
  rw [c_size] at hc
  have hz := allN_spec kZ c hc
  unfold zAt at hz
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
    have hcomm := (allLt_iff.1 hall) _ (show ZW0.getD c 0 - 1 < heSevenA0Gens.size from hl)
    have e := (eqA_iff (rep_compA (c_rep hc) (ags _ hl)) (rep_compA (ags _ hl) (c_rep hc))).1 hcomm
    have := eqOnL_of_eq bs_lt ((c_repF hc).comp (ag _ hl))
      ((e ▸ (ag _ hl).comp (c_repF hc)))
    rw [Bool.eq_false_iff] at h3
    exact h3 this
  · rw [show Nat.blt (ZW0.getD c 0) 100 = false from Bool.eq_false_iff.2 fun h =>
      hw (Nat.blt_eq.mp h)] at hz
    simp only [bAnd_iff, Nat.blt_eq] at hz
    obtain ⟨h1, h2, h3⟩ := hz
    right
    rw [List.any_eq_true]
    refine ⟨ZW0.getD c 0 - 100, List.mem_range.2 h1, ?_⟩
    exact eqA_P (c_rep hc) (rep_powArr x0_rep _) (c_repF hc) (RepF.powF x0_repF _)
      ((c_mem hc).2.2 (Nat.eq_of_beq_eq_true h2)) (heP.pow_mem x0_inP _) h3

open Certificates in
open CFSG.RankThree.PartOne CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native in
theorem facts0 :
    caseChainOK3 8330 heSevenCase0Arrs heSevenCase0BaseArr heSevenCase0Words (heGen 0) (heGen 1)
        heUArr = true ∧
      centOKP 7 8330 heSevenCase0Arrs heSevenCase0BaseArr heSevenLines[0]! heSevenCase0Rels
        heSevenC0Gens heSevenKeys heSevenC0Cert 2058 = true ∧
      eqA 8330 heSevenC0Gens[0]! heSevenLines[0]! = true ∧
      normalOKP 7 8330 heSevenC0Gens heSevenA0Gens heSevenKeys heSevenC0Cert heSevenA0Cert 343
        heLevels heBase.toArray = true ∧
      zCentOKP 7 8330 heSevenA0Gens heSevenC0Cert heSevenA0Cert heSevenLines[0]! = true := by
  refine ⟨chain0, cent0, ?_, normal0, zcent0⟩
  refine (eqA_iff (cgs 0 (by norm_num)) x0_rep).2 ?_
  rw [lp0_eq]
  rfl

end CertificateChecks.KernelHeLoc.Seven

end
