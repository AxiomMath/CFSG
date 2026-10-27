module

public import Certificates.Kernel.HeLoc.FiveK
public import Certificates.Kernel.HeLoc.FiveLFacts
public import CFSG.Certificates.Kernel.HeLoc.PTailSound
public import CFSG.Certificates.Kernel.HeLoc.GroupConjSound
public import CFSG.RankThree.PartOne.KS.HeFiveData
public import CFSG.RankThree.PartOne.KS.HeFiveAux
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.RankThree.PartOne.KS.HeFiveCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Schreier.PairHeClasses

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.FiveL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.RankThree.Native
open CFSG.RankThree.PartOne CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open scoped commutatorElement


theorem conj_inP {g x : Equiv.Perm (Fin 8330)} (hg : g ∈ heAutGroup) (hx : x ∈ heP) :
    g * x * g⁻¹ ∈ heP := by
  have := heP_normal_heAutGroup.conj_mem ⟨x, heP_le_heAutGroup hx⟩
    (by rw [Subgroup.mem_subgroupOf]; exact hx) ⟨g, hg⟩
  rwa [Subgroup.mem_subgroupOf] at this

theorem comm_inP {a b : Equiv.Perm (Fin 8330)} (ha : a ∈ heAutGroup) (hb : b ∈ heAutGroup) :
    ⁅a, b⁆ ∈ heP := by
  have e : ⁅a, b⁆ = a * b * (b * a)⁻¹ := by rw [commutatorElement_def]; group
  have hab := heAutGroup.mul_mem ha hb
  have hba := heAutGroup.mul_mem hb ha
  rw [e, he_mul_mem_iff hab (heAutGroup.inv_mem hba), inv_mem_iff, he_mul_mem_iff ha hb,
    he_mul_mem_iff hb ha]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem commA_R {t u : Array Nat} {x y : Equiv.Perm (Fin 8330)} {f f' : Nat → Nat}
    (ht : Rep 8330 t x) (hu : Rep 8330 u y) (hf : RepF 8330 f x) (hf' : RepF 8330 f' y)
    (hx : x ∈ heAutGroup) (hy : y ∈ heAutGroup)
    (h : eqOnL Five.bs (fun z => f (f' z)) (fun z => f' (f z)) = true) :
    commA 8330 t u = true := by
  refine eqA_R (rep_compA ht hu) (rep_compA hu ht) (hf.comp hf') (hf'.comp hf)
    (heAutGroup.mul_mem hx hy) (heAutGroup.mul_mem hy hx) ?_ h
  rw [he_mul_mem_iff hx hy, he_mul_mem_iff hy hx]
  exact Iff.comm

theorem any_mem {c : CFSG.Monster.B.Fischer.ArrCert} {t : Array Nat} {k : Nat}
    (hk : k < c.pts.size) (h : eqA 8330 t c.pts[k]! = true) :
    c.pts.toList.any (eqA 8330 t) = true := by
  rw [List.any_eq_true]
  refine ⟨c.pts[k]!, ?_, h⟩
  rw [getElem!_pos c.pts k hk]
  exact Array.getElem_mem_toList _

theorem eqOnL_symm {l : List Nat} {f g : Nat → Nat} (h : eqOnL l f g = true) :
    eqOnL l g f = true :=
  (eqOnL_iff _ _ _).2 fun b hb => ((eqOnL_iff _ _ _).1 h b hb).symm

theorem key_faith {a b : Array Nat} {A B : Equiv.Perm (Fin 8330)} (ha : Rep 8330 a A)
    (hb : Rep 8330 b B) (hA : A ∈ heAutGroup) (hB : B ∈ heAutGroup)
    (h : keyA 8330 heFiveKeys a = keyA 8330 heFiveKeys b) : A = B := by
  have hl := Nat.ofDigits_inj_of_len_eq (b := 8330) (by norm_num) (by simp)
    (fun l hl => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      rw [ha.apply (Five.keys_lt p hp)]
      exact (A _).2)
    (fun l hl => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      rw [hb.apply (Five.keys_lt p hp)]
      exact (B _).2) h
  have hpt : ∀ p (hp : p ∈ heFiveKeys),
      (A ⟨p, Five.keys_lt p hp⟩ : Nat) = B ⟨p, Five.keys_lt p hp⟩ := by
    intro p hp
    have := List.map_inj_left.1 hl p hp
    rwa [ha.apply (Five.keys_lt p hp), hb.apply (Five.keys_lt p hp)] at this
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

theorem c_enum : enumOK 8330 heFiveC0Gens heFiveKeys heFiveC0Cert = true := by
  have hk := keys_inj_of_sortAtK (key := Five.key) fun j hj => allN_spec Five.kSort j hj
  refine enumOK_tree Five.tree Five.hgs (by rfl) (by norm_num) (by norm_num) ?_ Five.edges
  intro a ha b hb e
  rw [keyA_treeArr Five.tree Five.hg Five.hgs Five.keys_lt ha,
    keyA_treeArr Five.tree Five.hg Five.hgs Five.keys_lt hb] at e
  exact hk a ha b hb e

theorem c_size : heFiveC0Cert.pts.size = 600 := by rw [Five.pts_eq, Array.size_ofFn]

theorem c_get {k : Nat} (hk : k < 600) :
    heFiveC0Cert.pts[k]! = treeArr 8330 heFiveC0Gens Five.C0.P Five.C0.L k := by
  rw [Five.pts_eq, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

@[expose] noncomputable def cT (k : Nat) : Equiv.Perm (Fin 8330) :=
  treePerm Five.gp Five.C0.P Five.C0.L k

theorem c_rep {k : Nat} (hk : k < 600) : Rep 8330 heFiveC0Cert.pts[k]! (cT k) := by
  rw [c_get hk]
  exact rep_treeArr Five.tree Five.hgs k hk

theorem c_repF {k : Nat} (hk : k < 600) : RepF 8330 (Five.tv k) (cT k) :=
  repF_trV Five.tree Five.hg 600 k hk.le hk

theorem c_mem {k : Nat} (hk : k < 600) : cT k ∈ heAutGroup ∧ (cT k ∈ heP ↔ cq k = 0) := by
  obtain ⟨h1, h2, -⟩ := trQ_spec Five.tree (fun a ha b hb => he_mul_mem_iff ha hb) Five.gp_mem
    Five.gp_par Five.q_lt 600 k hk.le hk
  exact ⟨h1, h2⟩

theorem csk_lt : ∀ j < 600, Five.C0.SK j < 600 := sk_lt fun j hj => by
  have h := allN_spec Five.kSort j hj
  unfold sortAtK at h
  rw [bAnd_iff, bAnd_iff, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1⟩

@[expose] noncomputable def gpD (l : Nat) : Equiv.Perm (Fin 8330) :=
  if l = 0 then ⁅Five.gp 1, Five.gp 2⁆ else Five.gp 2

theorem dgs : ∀ l < 2, Rep 8330 heFiveDGens0[l]! (gpD l) := by
  intro l hl
  rw [heFiveDGens0]
  interval_cases l
  · rw [lit2_0, gpD, if_pos rfl]
    have h := rep_commutatorA (F2.validA_of_rep (Five.hgs 1 (by norm_num)))
      (F2.validA_of_rep (Five.hgs 2 (by norm_num)))
    rwa [CFSG.RankThree.Native.permOfArr_eq_of_rep (Five.hgs 1 (by norm_num)),
      CFSG.RankThree.Native.permOfArr_eq_of_rep (Five.hgs 2 (by norm_num))] at h
  · rw [lit2_1, gpD, if_neg (by norm_num)]
    exact Five.hgs 2 (by norm_num)

theorem dg : ∀ l < 2, RepF 8330 (gD l) (gpD l) := by
  intro l hl
  interval_cases l
  · rw [gpD, if_pos rfl, commutatorElement_def]
    have h := (repF_pa 9 (by norm_num)).comp ((repF_pa 10 (by norm_num)).comp
      ((repF_pi 9 (by norm_num)).comp (repF_pi 10 (by norm_num))))
    rw [← mul_assoc, ← mul_assoc] at h
    exact h
  · rw [gpD, if_neg (by norm_num)]
    exact repF_pa 10 (by norm_num)

theorem dg_inP : ∀ l < 2, gpD l ∈ heP := by
  intro l hl
  interval_cases l
  · rw [gpD, if_pos rfl]
    exact comm_inP (Five.gp_mem 1 (by norm_num)) (Five.gp_mem 2 (by norm_num))
  · rw [gpD, if_neg (by norm_num)]
    exact (Five.gp_par 2 (by norm_num)).2 rfl

theorem pfaith : ∀ x ∈ heP, ∀ y ∈ heP, (x ∈ heP ↔ y ∈ heP) →
    (∀ b (hb : b ∈ Five.bs), (x ⟨b, Five.bs_lt b hb⟩ : Nat) = y ⟨b, Five.bs_lt b hb⟩) → x = y :=
  fun x hx y hy _ hb => Five.faithful x (heP_le_heAutGroup hx) y (heP_le_heAutGroup hy)
    (iff_of_true hx hy) hb

theorem dtree : TreeOK 2 60 D0.P D0.L := treeOK_of fun i hi h0 => by
  have h := allN_spec kDTree i hi
  rwa [beq_zero_false h0] at h

theorem dedges : ∀ i < 60, ∀ k < 2, DE i k < 60 ∧
    treeArr 8330 heFiveDGens0 D0.P D0.L (DE i k) =
      compA 8330 heFiveDGens0[k]! (treeArr 8330 heFiveDGens0 D0.P D0.L i) :=
  edges_of_edgeAtK dtree dg dgs hmulP dg_inP (fun k hk => iff_of_true (dg_inP k hk) rfl)
    (fun _ _ => by decide) Five.bs_lt pfaith fun i hi => allN_spec kDEdge i hi

theorem dkeys_inj : ∀ a < 60, ∀ b < 60,
    keyA 8330 heFiveKeys (treeArr 8330 heFiveDGens0 D0.P D0.L a) =
      keyA 8330 heFiveKeys (treeArr 8330 heFiveDGens0 D0.P D0.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := dkey) fun j hj => allN_spec kDSort j hj
  intro a ha b hb e
  rw [keyA_treeArr dtree dg dgs Five.keys_lt ha, keyA_treeArr dtree dg dgs Five.keys_lt hb] at e
  exact hk a ha b hb e

theorem d_pts : heFiveDCert0.pts =
    Array.ofFn (n := 60) fun i => treeArr 8330 heFiveDGens0 D0.P D0.L i.val :=
  enumBfs_tree dtree dgs (by rfl) (by norm_num) (by norm_num) dkeys_inj dedges kDReplay

theorem d_enum : enumOK 8330 heFiveDGens0 heFiveKeys heFiveDCert0 = true :=
  enumOK_tree dtree dgs (by rfl) (by norm_num) (by norm_num) dkeys_inj dedges

theorem d_size : heFiveDCert0.pts.size = 60 := by rw [d_pts, Array.size_ofFn]

theorem d_get {k : Nat} (hk : k < 60) :
    heFiveDCert0.pts[k]! = treeArr 8330 heFiveDGens0 D0.P D0.L k := by
  rw [d_pts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

@[expose] noncomputable def dT (k : Nat) : Equiv.Perm (Fin 8330) := treePerm gpD D0.P D0.L k

theorem d_rep {k : Nat} (hk : k < 60) : Rep 8330 heFiveDCert0.pts[k]! (dT k) := by
  rw [d_get hk]
  exact rep_treeArr dtree dgs k hk

theorem d_repF {k : Nat} (hk : k < 60) : RepF 8330 (dv k) (dT k) :=
  repF_trV dtree dg 60 k hk.le hk

theorem d_inP {k : Nat} (hk : k < 60) : dT k ∈ heP :=
  (trQ_spec dtree hmulP dg_inP (fun k hk => iff_of_true (dg_inP k hk) rfl)
    (fun _ _ => by decide) 60 k hk.le hk).1

theorem d_psize {k : Nat} (hk : k < 60) : heFiveDCert0.pts[k]!.size = 8330 := by
  rw [d_get hk]
  exact size_treeArr k

theorem mt_spec {a b : Nat} (ha : a < 60) (hb : b < 60) :
    mt a b < 60 ∧ dT (mt a b) = dT a * dT b := by
  have h' := allN_spec (allN_spec kMT a ha) b hb
  rw [bAnd_iff, Nat.blt_eq] at h'
  exact ⟨h'.1, eq_of_P (d_repF h'.1) ((d_repF ha).comp (d_repF hb)) (d_inP h'.1)
    (heP.mul_mem (d_inP ha) (d_inP hb)) h'.2⟩

theorem iv_spec {a : Nat} (ha : a < 60) : iv a < 60 ∧ dT (iv a) = (dT a)⁻¹ := by
  have h := allN_spec kIV a ha
  rw [bAnd_iff, Nat.blt_eq] at h
  refine ⟨h.1, eq_inv_of_mul_eq_one_left ?_⟩
  exact eq_of_P ((d_repF h.1).comp (d_repF ha)) RepF.one
    (heP.mul_mem (d_inP h.1) (d_inP ha)) heP.one_mem h.2

theorem d_idA : heFiveDCert0.pts[0]! = idA 8330 := by
  rw [d_get (k := 0) (by norm_num), treeArr_zero]

theorem conjSimple : conjSimpleOK 8330 heFiveKeys heFiveDCert0 = true := by
  unfold conjSimpleOK
  rw [allLt_iff]
  intro k hk
  rw [d_size] at hk
  rw [Bool.or_eq_true]
  by_cases hk0 : k = 0
  · subst hk0
    left
    rw [d_idA]
    exact (eqA_iff rep_idA rep_idA).2 rfl
  · right
    have hbt := allN_spec kBT k hk
    unfold btB at hbt
    rw [beq_zero_false (Nat.pos_of_ne_zero hk0)] at hbt
    refine conjPointOK_of_table (N := 60) d_size (fun i hi => d_rep hi) (fun i hi => d_psize hi)
      (by norm_num) d_idA
      (fun a ha b hb e => dkeys_inj a ha b hb (by rwa [d_get ha, d_get hb] at e))
      (fun a ha b hb => mt_spec ha hb) (fun a ha => iv_spec ha) hk
      (par := btP k) (lab := btL k) (dep := btD k) fun i hi => ?_
    have h := allN_spec hbt i hi
    by_cases hi0 : i = 0
    · exact Or.inl hi0
    · right
      rw [beq_zero_false (Nat.pos_of_ne_zero hi0)] at h
      simp only [bAnd_iff, Nat.blt_eq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      exact ⟨h1, h2, Nat.eq_of_beq_eq_true h3, (Nat.eq_of_beq_eq_true h4).symm⟩

theorem x0_rep : Rep 8330 heFiveLines[0]! (lp 0) := rep_line 0 (by norm_num)

theorem x0_repF : RepF 8330 x0 (lp 0) := repF_ln 0 (by norm_num)

theorem x0_inP : lp 0 ∈ heP := lp_inP 0 (by norm_num)

theorem lp0_eq : lp 0 = Five.gp 0 := by
  rw [lp, gp_one, one_mul, inv_one, mul_one]
  rfl

theorem wit_eq (i : Nat) (hi : i < 2) : heFiveDWit0[i]! = unpack 8330 14 (A (11 + i)) := by
  rw [heFiveDWit0]
  interval_cases i
  · exact (lit2_0 _ _).trans (arr_eq 11 (by norm_num))
  · exact (lit2_1 _ _).trans (arr_eq 12 (by norm_num))

theorem wit_rep (i : Nat) (hi : i < 2) : Rep 8330 heFiveDWit0[i]! (gp (11 + i)) := by
  rw [wit_eq i hi]
  exact rep_gp _ (by omega)

theorem wit_mem (i : Nat) (hi : i < 2) :
    heFiveC0Cert.pts.toList.any (eqA 8330 heFiveDWit0[i]!) = true := by
  have h := allN_spec kCD i hi
  simp only [bAnd_iff, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hm := gp_mem (11 + i) (by omega)
  refine any_mem (by rw [c_size]; exact h1) (eqA_R (wit_rep i hi) (c_rep h1)
    (repF_pa (11 + i) (by omega)) (c_repF h1) hm.1 (c_mem h1).1 ?_ (eqOnL_symm h3))
  rw [hm.2, (c_mem h1).2, Nat.eq_of_beq_eq_true h2]
  rfl

theorem base_lt : ∀ t < 9, heFiveCase0BaseArr[t]! < 8330 := by decide

theorem rels_ok : relsOKP 5 8330 heFiveCase0BaseArr heFiveLines[0]! heFiveCase0Rels = true := by
  rw [relsOKP, List.all_eq_true]
  intro r hr
  have h := List.all_eq_true.1 kRels r hr
  unfold relAt at h
  simp only [bAnd_iff, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs : heFiveCase0BaseArr.size = 9 := by decide
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hs]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  rw [(rep_powArr x0_rep r.2.2).apply (base_lt _ h2),
    ← (RepF.powF x0_repF r.2.2) _ (base_lt _ h2)]
  exact Nat.eq_of_beq_eq_true h4

theorem tabs : TabsT 8330 14 11 9 S50.BP T50.NR T50.NR S50.S S50.SI S50.LR T50.Ts T50.LT T50.PT
    T50.QT 179 1024 9 1024 :=
  ⟨by decide, by decide, by decide, by decide, TS5.all, LT5.all, pt5B_all, qt5B_all⟩

theorem tc : TabChain 8330 14 11 9 S50.BP 131 64 T50.NR T50.NR 179 1024 9 1024 S50.S S50.SI
    S50.LR T50.Ts T50.LT T50.PT T50.QT heFiveCase0Arrs heFiveCase0BaseArr
    (heFiveCase0Base.map Fin.val) :=
  ⟨binds0, k5Perm, S50.ho, by norm_num, tabs, rfl⟩

theorem fr_ok : ∀ i < 9, fr5 i = 0 ∨ ∃ l e, fr5 i = 8 * l + e + 1 ∧ l < i ∧ e < 8 ∧
    (l, i, e) ∈ heFiveCase0Rels := by
  intro i hi
  have h := allN_spec kFR i hi
  by_cases h0 : fr5 i = 0
  · exact Or.inl h0
  · right
    rw [show Nat.beq (fr5 i) 0 = false from
      Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)] at h
    simp only [bAnd_iff, Nat.blt_eq, List.any_eq_true] at h
    obtain ⟨h1, h2, r, hr, hr1, hr2, hr3⟩ := h
    refine ⟨(fr5 i - 1) / 8, (fr5 i - 1) % 8, by omega, h1, by omega, ?_⟩
    have e1 := Nat.eq_of_beq_eq_true hr1
    have e2 := Nat.eq_of_beq_eq_true hr2
    have e3 := Nat.eq_of_beq_eq_true hr3
    obtain ⟨a, b, c⟩ := r
    have e : (a, b, c) = ((fr5 i - 1) / 8, i, (fr5 i - 1) % 8) := by
      simp only [Prod.mk.injEq]
      exact ⟨e1, e2, e3⟩
    rw [← e]
    exact hr

theorem tail : ptailOK 8330 (rawLevels 8330 heFiveCase0Arrs heFiveCase0BaseArr)
    heFiveCase0BaseArr heFiveLines[0]! (powPA 5 8330 heFiveLines[0]!) heFiveCase0Rels
    heFiveC0Cert.pts.toList 9 0 (idA 8330) = true := by
  refine ptailOK_of_ptK_ tc x0_rep x0_repF (fun r hr => ?_) fr_ok Five.bs_lt ?_ (by norm_num) kTail
  · have h := List.all_eq_true.1 kRels r hr
    unfold relAt at h
    rw [bAnd_iff, Nat.blt_eq] at h
    exact h.1
  · intro a A ha hA ⟨j, hj, e⟩
    have hR : A ∈ heAutGroup := by
      refine (Subgroup.closure_le _).2 ?_ hA
      rintro _ ⟨i, rfl⟩
      exact faith0.2 i (by simpa [heFiveCase0Arrs] using i.2)
    have hm := csk_lt j hj
    unfold Five.key Five.tv at e
    rw [← keyA_treeArr Five.tree Five.hg Five.hgs Five.keys_lt hm, ← c_get hm] at e
    have he := key_faith ha (c_rep hm) hR (c_mem hm).1 e
    exact any_mem (by rw [c_size]; exact hm) ((eqA_iff ha (c_rep hm)).2 he)

theorem cent : centOKP 5 8330 heFiveCase0Arrs heFiveCase0BaseArr heFiveLines[0]!
    heFiveCase0Rels heFiveC0Gens heFiveKeys heFiveC0Cert 600 = true := by
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  have hs : heFiveCase0BaseArr.size = 9 := by decide
  refine ⟨⟨⟨⟨⟨rels_ok, c_enum⟩, c_size⟩, fun k hk => ?_⟩, fun k hk => ?_⟩,
    by rw [hs]; exact tail⟩
  · have hk3 : k < 3 := hk
    exact commA_R (Five.hgs k hk3) x0_rep (Five.hg k hk3) x0_repF (Five.gp_mem k hk3)
      (heP_le_heAutGroup x0_inP) (allN_spec kComm k hk3)
  · have hk3 : k < 3 := hk
    exact (sift0_iff (Five.hgs k hk3)).2 (Five.gp_mem k hk3)

theorem derived : derivedOKP 5 60 8330 heFiveC0Gens heFiveDGens0 heFiveKeys heFiveC0Cert
    heFiveDCert0 heFiveDWit0[0]! heFiveDWit0[1]! heFiveLines[0]! heLevels heBase.toArray =
    true := by
  simp only [derivedOKP, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  have hgC : heFiveC0Gens.size = 3 := rfl
  have hgD : heFiveDGens0.size = 2 := rfl
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨d_enum, d_size⟩, F2.validA_of_rep (wit_rep 0 (by norm_num))⟩,
    F2.validA_of_rep (wit_rep 1 (by norm_num))⟩, wit_mem 0 (by norm_num)⟩,
    wit_mem 1 (by norm_num)⟩, ?_⟩, fun k hk l hl => ?_⟩, fun k hk l hl => ?_⟩, ?_⟩,
    conjSimple⟩, fun k hk => ?_⟩, fun l hl => ?_⟩
  ·
    have h := rep_commutatorA (F2.validA_of_rep (wit_rep 0 (by norm_num)))
      (F2.validA_of_rep (wit_rep 1 (by norm_num)))
    rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (wit_rep 0 (by norm_num)),
      CFSG.RankThree.Native.permOfArr_eq_of_rep (wit_rep 1 (by norm_num))] at h
    have hP := comm_inP (gp_mem 11 (by norm_num)).1 (gp_mem 12 (by norm_num)).1
    rw [commutatorElement_def] at h hP
    have hf := (repF_pa 11 (by norm_num)).comp ((repF_pa 12 (by norm_num)).comp
      ((repF_pi 11 (by norm_num)).comp (repF_pi 12 (by norm_num))))
    rw [← mul_assoc, ← mul_assoc] at hf
    exact eqA_P (Five.hgs 2 (by norm_num)) h (repF_pa 10 (by norm_num)) hf
      ((Five.gp_par 2 (by norm_num)).2 rfl) hP kCom
  ·
    rw [hgC] at hk
    rw [hgD] at hl
    have h := allN_spec kDK (2 * k + l) (by omega)
    rw [show Nat.div (2 * k + l) 2 = k by change (2 * k + l) / 2 = k; omega,
      show Nat.mod (2 * k + l) 2 = l by change (2 * k + l) % 2 = l; omega] at h
    rw [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine any_mem (by rw [d_size]; exact h1) ?_
    have hc := rep_conjA (F2.validA_of_rep (Five.hgs k hk)) (dgs l hl)
    rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (Five.hgs k hk)] at hc
    have hcf : RepF 8330 (fun y => pa (Nat.add 8 k) (gD l (pi (Nat.add 8 k) y)))
        (Five.gp k * gpD l * (Five.gp k)⁻¹) := by
      have := (repF_pa (8 + k) (by omega)).comp ((dg l hl).comp (repF_pi (8 + k) (by omega)))
      rw [mul_assoc]
      exact this
    exact eqA_P hc (d_rep h1) hcf (d_repF h1) (conj_inP (Five.gp_mem k hk) (dg_inP l hl))
      (d_inP h1) (eqOnL_symm h2)
  ·
    rw [hgC] at hk hl
    have h := allN_spec kDC (3 * k + l) (by omega)
    rw [show Nat.div (3 * k + l) 3 = k by change (3 * k + l) / 3 = k; omega,
      show Nat.mod (3 * k + l) 3 = l by change (3 * k + l) % 3 = l; omega] at h
    rw [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine any_mem (by rw [d_size]; exact h1) ?_
    have hc := rep_commutatorA (F2.validA_of_rep (Five.hgs k hk)) (F2.validA_of_rep (Five.hgs l hl))
    rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (Five.hgs k hk),
      CFSG.RankThree.Native.permOfArr_eq_of_rep (Five.hgs l hl)] at hc
    have hP := comm_inP (Five.gp_mem k hk) (Five.gp_mem l hl)
    rw [commutatorElement_def] at hc hP
    have hcf : RepF 8330 (fun y => pa (Nat.add 8 k) (pa (Nat.add 8 l) (pi (Nat.add 8 k)
        (pi (Nat.add 8 l) y)))) (Five.gp k * Five.gp l * (Five.gp k)⁻¹ * (Five.gp l)⁻¹) := by
      have := (repF_pa (8 + k) (by omega)).comp ((repF_pa (8 + l) (by omega)).comp
        ((repF_pi (8 + k) (by omega)).comp (repF_pi (8 + l) (by omega))))
      rw [← mul_assoc, ← mul_assoc] at this
      exact this
    exact eqA_P hc (d_rep h1) hcf (d_repF h1) hP (d_inP h1) (eqOnL_symm h2)
  ·
    have h := kNC
    rw [Bool.not_eq_true'] at h
    rw [Bool.not_eq_true']
    exact neA_P (rep_compA (dgs 0 (by norm_num)) (dgs 1 (by norm_num)))
      (rep_compA (dgs 1 (by norm_num)) (dgs 0 (by norm_num)))
      ((dg 0 (by norm_num)).comp (dg 1 (by norm_num)))
      ((dg 1 (by norm_num)).comp (dg 0 (by norm_num))) h
  ·
    rw [c_size] at hk
    have hz := allN_spec kZ k hk
    unfold zAt at hz
    rw [CFSG.KS.SporSch.strictB_val] at hz
    rw [Bool.or_eq_true]
    by_cases hw : ZW0.getD k 0 < 100
    · rw [show Nat.blt (ZW0.getD k 0) 100 = true from Nat.blt_eq.mpr hw] at hz
      simp only [bAnd_iff, Nat.blt_eq, Bool.not_eq_true'] at hz
      obtain ⟨h1, h2, h3⟩ := hz
      left
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      intro hall
      have hl : ZW0.getD k 0 - 1 < 2 := by omega
      have hcomm := (allLt_iff.1 hall) _ (show ZW0.getD k 0 - 1 < heFiveDGens0.size from hl)
      have e := (eqA_iff (rep_compA (c_rep hk) (dgs _ hl))
        (rep_compA (dgs _ hl) (c_rep hk))).1 hcomm
      have := eqOnL_of_eq Five.bs_lt ((c_repF hk).comp (dg _ hl))
        ((e ▸ (dg _ hl).comp (c_repF hk)))
      rw [Bool.eq_false_iff] at h3
      exact h3 this
    · rw [show Nat.blt (ZW0.getD k 0) 100 = false from Bool.eq_false_iff.2 fun h =>
        hw (Nat.blt_eq.mp h)] at hz
      simp only [bAnd_iff, Nat.blt_eq] at hz
      obtain ⟨h1, h2, h3⟩ := hz
      right
      rw [List.any_eq_true]
      refine ⟨ZW0.getD k 0 - 100, List.mem_range.2 h1, ?_⟩
      exact eqA_P (c_rep hk) (rep_powArr x0_rep _) (c_repF hk) (RepF.powF x0_repF _)
        ((c_mem hk).2.2 (Nat.eq_of_beq_eq_true h2)) (heP.pow_mem x0_inP _) h3
  · rw [hgD] at hl
    rw [show heLevels = rawLevels 8330 heStrongArrs heBase.toArray from rfl,
      mem_heP_iff_siftA (dgs l hl)]
    exact dg_inP l hl

open Certificates in
open CFSG.RankThree.PartOne CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB in
theorem facts :
    (linesOKG 5 25 6 8330 heFiveQGens heFiveKeys heFiveQCert heFiveLines = true ∧
      allLt heFiveQGens.size (fun l => siftA 8330 heLevels heBase.toArray 0 heFiveQGens[l]!) =
        true ∧
      transOKG 6 8330 heFiveTransporters heFiveLines heFiveRec heFiveRLevels heFiveCase0BaseArr =
        true ∧
      allLt 6 (fun j => (List.range 1).any fun i => heFiveRec.getD j 0 == i) = true ∧
      heFiveRec.getD 0 0 = 0)
    ∧ (caseChainOK3 8330 heFiveCase0Arrs heFiveCase0BaseArr heFiveCase0Words (heGen 0) (heGen 1)
        heUArr = true ∧
      centOKP 5 8330 heFiveCase0Arrs heFiveCase0BaseArr heFiveLines[0]! heFiveCase0Rels
        heFiveC0Gens heFiveKeys heFiveC0Cert 600 = true ∧
      eqA 8330 heFiveC0Gens[0]! heFiveLines[0]! = true ∧
      derivedOKP 5 60 8330 heFiveC0Gens heFiveDGens0 heFiveKeys heFiveC0Cert heFiveDCert0
        heFiveDWit0[0]! heFiveDWit0[1]! heFiveLines[0]! heLevels heBase.toArray = true) := by
  refine ⟨qfacts, chain0, cent, ?_, derived⟩
  refine (eqA_iff (Five.hgs 0 (by norm_num)) x0_rep).2 ?_
  rw [lp0_eq]

end CertificateChecks.KernelHeLoc.FiveL

end
