module

public import Certificates.Kernel.RuFive.FactsQ
public import Certificates.Kernel.RuFive.K1
public import CFSG.Certificates.Kernel.HeLoc.GroupConjSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KC.J2H
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier
open CFSG.Certificates CFSG.Certificates.Native
open scoped commutatorElement


theorem lit3_0' (a b c : Array Nat) : (#[a, b, c] : Array (Array Nat))[0]! = a := rfl
theorem lit3_1' (a b c : Array Nat) : (#[a, b, c] : Array (Array Nat))[1]! = b := rfl
theorem lit3_2' (a b c : Array Nat) : (#[a, b, c] : Array (Array Nat))[2]! = c := rfl
theorem lit2_0 (a b : Array Nat) : (#[a, b] : Array (Array Nat))[0]! = a := rfl
theorem lit2_1 (a b : Array Nat) : (#[a, b] : Array (Array Nat))[1]! = b := rfl

theorem c1gens_eq (k : Nat) (hk : k < 3) : ruFiveC1Gens[k]! = unpack 4060 12 (F (67 + k)) := by
  rw [ruFiveC1Gens]
  interval_cases k
  · exact (lit3_0' _ _ _).trans (arr_eq 67 (by norm_num))
  · exact (lit3_1' _ _ _).trans (arr_eq 68 (by norm_num))
  · exact (lit3_2' _ _ _).trans (arr_eq 69 (by norm_num))

@[expose] noncomputable def gpC1 (k : Nat) : Equiv.Perm (Fin 4060) := gp (67 + k)

theorem c1gs : ∀ k < 3, Rep 4060 ruFiveC1Gens[k]! (gpC1 k) := fun k hk => by
  rw [c1gens_eq k hk]
  exact rep_gp _ (by omega)

theorem c1g : ∀ k < 3, RepF 4060 (gC1 k) (gpC1 k) := fun k hk => repF_pa (67 + k) (by omega)

theorem c1g_mem : ∀ k < 3, gpC1 k ∈ ruP := fun k hk => gp_mem _ (by omega)

theorem c1tree : TreeOK 3 300 C1.P C1.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kC1Tree i hi
  rwa [beq_zero_false h0] at h

theorem c1edges : ∀ i < 300, ∀ k < 3, CE1 i k < 300 ∧
    treeArr 4060 ruFiveC1Gens C1.P C1.L (CE1 i k) =
      compA 4060 ruFiveC1Gens[k]! (treeArr 4060 ruFiveC1Gens C1.P C1.L i) :=
  edges_of_edgeAtK c1tree c1g c1gs hmul c1g_mem (fun k hk => iff_of_true (c1g_mem k hk) rfl)
    (fun _ _ => by decide) bs_lt hF fun i hi => Orb.allN_iff.1 kC1Edge i hi

theorem c1keys_inj : ∀ a < 300, ∀ b < 300,
    keyA 4060 ruFiveKeys (treeArr 4060 ruFiveC1Gens C1.P C1.L a) =
      keyA 4060 ruFiveKeys (treeArr 4060 ruFiveC1Gens C1.P C1.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := ckey1) fun j hj => Orb.allN_iff.1 kC1Sort j hj
  intro a ha b hb e
  rw [keyA_treeArr c1tree c1g c1gs keys_lt ha, keyA_treeArr c1tree c1g c1gs keys_lt hb] at e
  exact hk a ha b hb e

theorem c1_pts : ruFiveC1Cert.pts =
    Array.ofFn (n := 300) fun i => treeArr 4060 ruFiveC1Gens C1.P C1.L i.val :=
  enumBfs_tree c1tree c1gs (by rfl) (by norm_num) (by norm_num) c1keys_inj c1edges kC1Replay

theorem c1_enum : enumOK 4060 ruFiveC1Gens ruFiveKeys ruFiveC1Cert = true :=
  enumOK_tree c1tree c1gs (by rfl) (by norm_num) (by norm_num) c1keys_inj c1edges

theorem c1_size : ruFiveC1Cert.pts.size = 300 := by rw [c1_pts, Array.size_ofFn]

theorem c1_get {k : Nat} (hk : k < 300) :
    ruFiveC1Cert.pts[k]! = treeArr 4060 ruFiveC1Gens C1.P C1.L k := by
  rw [c1_pts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem c1_rep {k : Nat} (hk : k < 300) :
    Rep 4060 ruFiveC1Cert.pts[k]! (treePerm gpC1 C1.P C1.L k) := by
  rw [c1_get hk]
  exact rep_treeArr c1tree c1gs k hk

theorem c1_repF {k : Nat} (hk : k < 300) : RepF 4060 (cv1 k) (treePerm gpC1 C1.P C1.L k) :=
  repF_trV c1tree c1g 300 k hk.le hk

theorem c1_mem {k : Nat} (hk : k < 300) : treePerm gpC1 C1.P C1.L k ∈ ruP :=
  (trQ_spec c1tree hmul c1g_mem (fun k hk => iff_of_true (c1g_mem k hk) rfl) (fun _ _ => by decide)
    300 k hk.le hk).1

theorem c1sk_lt : ∀ j < 300, C1.SK j < 300 := sk_lt fun j hj => by
  have h := Orb.allN_iff.1 kC1Sort j hj
  unfold sortAtK at h
  rw [bAnd_iff, bAnd_iff, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1⟩

@[expose] noncomputable def gpD (l : Nat) : Equiv.Perm (Fin 4060) :=
  if l = 0 then ⁅gp 68, gp 69⁆ else gp 69

theorem dgs : ∀ l < 2, Rep 4060 ruFiveDGens[l]! (gpD l) := by
  intro l hl
  rw [ruFiveDGens]
  interval_cases l
  · rw [lit2_0, gpD, if_pos rfl]
    have h1 := c1gs 1 (by norm_num)
    have h2 := c1gs 2 (by norm_num)
    have h := rep_commutatorA (F2.validA_of_rep h1) (F2.validA_of_rep h2)
    rwa [CFSG.RankThree.Native.permOfArr_eq_of_rep h1,
      CFSG.RankThree.Native.permOfArr_eq_of_rep h2] at h
  · rw [lit2_1, gpD, if_neg (by norm_num)]
    exact c1gs 2 (by norm_num)

theorem dg : ∀ l < 2, RepF 4060 (gD l) (gpD l) := by
  intro l hl
  interval_cases l
  · rw [gpD, if_pos rfl, commutatorElement_def]
    have h := (repF_pa 68 (by norm_num)).comp ((repF_pa 69 (by norm_num)).comp
      ((repF_pi 68 (by norm_num)).comp (repF_pi 69 (by norm_num))))
    rw [← mul_assoc, ← mul_assoc] at h
    exact h
  · rw [gpD, if_neg (by norm_num)]
    exact repF_pa 69 (by norm_num)

theorem comm_mem {a b : Equiv.Perm (Fin 4060)} (ha : a ∈ ruP) (hb : b ∈ ruP) : ⁅a, b⁆ ∈ ruP := by
  rw [commutatorElement_def]
  exact ruP.mul_mem (ruP.mul_mem (ruP.mul_mem ha hb) (ruP.inv_mem ha)) (ruP.inv_mem hb)

theorem dg_mem : ∀ l < 2, gpD l ∈ ruP := by
  intro l hl
  interval_cases l
  · rw [gpD, if_pos rfl]
    exact comm_mem (gp_mem 68 (by norm_num)) (gp_mem 69 (by norm_num))
  · rw [gpD, if_neg (by norm_num)]
    exact gp_mem 69 (by norm_num)

theorem dtree : TreeOK 2 60 D0.P D0.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kDTree i hi
  rwa [beq_zero_false h0] at h

theorem dedges : ∀ i < 60, ∀ k < 2, DE i k < 60 ∧
    treeArr 4060 ruFiveDGens D0.P D0.L (DE i k) =
      compA 4060 ruFiveDGens[k]! (treeArr 4060 ruFiveDGens D0.P D0.L i) :=
  edges_of_edgeAtK dtree dg dgs hmul dg_mem (fun k hk => iff_of_true (dg_mem k hk) rfl)
    (fun _ _ => by decide) bs_lt hF fun i hi => Orb.allN_iff.1 kDEdge i hi

theorem dkeys_inj : ∀ a < 60, ∀ b < 60,
    keyA 4060 ruFiveKeys (treeArr 4060 ruFiveDGens D0.P D0.L a) =
      keyA 4060 ruFiveKeys (treeArr 4060 ruFiveDGens D0.P D0.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := dkey) fun j hj => Orb.allN_iff.1 kDSort j hj
  intro a ha b hb e
  rw [keyA_treeArr dtree dg dgs keys_lt ha, keyA_treeArr dtree dg dgs keys_lt hb] at e
  exact hk a ha b hb e

theorem d_pts : ruFiveDCert.pts =
    Array.ofFn (n := 60) fun i => treeArr 4060 ruFiveDGens D0.P D0.L i.val :=
  enumBfs_tree dtree dgs (by rfl) (by norm_num) (by norm_num) dkeys_inj dedges kDReplay

theorem d_enum : enumOK 4060 ruFiveDGens ruFiveKeys ruFiveDCert = true :=
  enumOK_tree dtree dgs (by rfl) (by norm_num) (by norm_num) dkeys_inj dedges

theorem d_size : ruFiveDCert.pts.size = 60 := by rw [d_pts, Array.size_ofFn]

theorem d_get {k : Nat} (hk : k < 60) :
    ruFiveDCert.pts[k]! = treeArr 4060 ruFiveDGens D0.P D0.L k := by
  rw [d_pts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

@[expose] noncomputable def dT (k : Nat) : Equiv.Perm (Fin 4060) := treePerm gpD D0.P D0.L k

theorem d_rep {k : Nat} (hk : k < 60) : Rep 4060 ruFiveDCert.pts[k]! (dT k) := by
  rw [d_get hk]
  exact rep_treeArr dtree dgs k hk

theorem d_repF {k : Nat} (hk : k < 60) : RepF 4060 (dv k) (dT k) :=
  repF_trV dtree dg 60 k hk.le hk

theorem d_mem {k : Nat} (hk : k < 60) : dT k ∈ ruP :=
  (trQ_spec dtree hmul dg_mem (fun k hk => iff_of_true (dg_mem k hk) rfl)
    (fun _ _ => by decide) 60 k hk.le hk).1

theorem d_psize {k : Nat} (hk : k < 60) : ruFiveDCert.pts[k]!.size = 4060 := by
  rw [d_get hk]
  exact size_treeArr k

theorem mt_spec {a b : Nat} (ha : a < 60) (hb : b < 60) :
    mt a b < 60 ∧ dT (mt a b) = dT a * dT b := by
  have h' := Orb.allN_iff.1 (Orb.allN_iff.1 kMT a ha) b hb
  rw [bAnd_iff, Nat.blt_eq] at h'
  exact ⟨h'.1, eq_of_R (d_repF h'.1) ((d_repF ha).comp (d_repF hb)) (d_mem h'.1)
    (ruP.mul_mem (d_mem ha) (d_mem hb)) h'.2⟩

theorem iv_spec {a : Nat} (ha : a < 60) : iv a < 60 ∧ dT (iv a) = (dT a)⁻¹ := by
  have h := Orb.allN_iff.1 kIV a ha
  rw [bAnd_iff, Nat.blt_eq] at h
  refine ⟨h.1, eq_inv_of_mul_eq_one_left ?_⟩
  exact eq_of_R ((d_repF h.1).comp (d_repF ha)) RepF.one
    (ruP.mul_mem (d_mem h.1) (d_mem ha)) ruP.one_mem h.2

theorem d_idA : ruFiveDCert.pts[0]! = idA 4060 := by
  rw [d_get (k := 0) (by norm_num), treeArr_zero]

theorem conjSimple : conjSimpleOK 4060 ruFiveKeys ruFiveDCert = true := by
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
    have hbt := Orb.allN_iff.1 kBT k hk
    unfold btB at hbt
    rw [beq_zero_false (Nat.pos_of_ne_zero hk0)] at hbt
    refine conjPointOK_of_table (N := 60) d_size (fun i hi => d_rep hi) (fun i hi => d_psize hi)
      (by norm_num) d_idA
      (fun a ha b hb e => dkeys_inj a ha b hb (by rwa [d_get ha, d_get hb] at e))
      (fun a ha b hb => mt_spec ha hb) (fun a ha => iv_spec ha) hk
      (par := btP k) (lab := btL k) (dep := btD k) fun i hi => ?_
    have h := Orb.allN_iff.1 hbt i hi
    by_cases hi0 : i = 0
    · exact Or.inl hi0
    · right
      rw [beq_zero_false (Nat.pos_of_ne_zero hi0)] at h
      simp only [bAnd_iff, Nat.blt_eq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      exact ⟨h1, h2, Nat.eq_of_beq_eq_true h3, (Nat.eq_of_beq_eq_true h4).symm⟩

theorem x1_rep : Rep 4060 ruFiveLines[1]! (gp 3) := rep_line 1 (by norm_num)

theorem x1_repF : RepF 4060 x1 (gp 3) := repF_pa 3 (by norm_num)

theorem x1_mem : gp 3 ∈ ruP := gp_mem 3 (by norm_num)

theorem wit_eq (i : Nat) (hi : i < 2) : ruFiveDWit[i]! = unpack 4060 12 (F (73 + i)) := by
  rw [ruFiveDWit]
  interval_cases i
  · exact (lit2_0 _ _).trans (arr_eq 73 (by norm_num))
  · exact (lit2_1 _ _).trans (arr_eq 74 (by norm_num))

theorem wit_rep (i : Nat) (hi : i < 2) : Rep 4060 ruFiveDWit[i]! (gp (73 + i)) := by
  rw [wit_eq i hi]
  exact rep_gp _ (by omega)

theorem wit_mem (i : Nat) (hi : i < 2) :
    ruFiveC1Cert.pts.toList.any (eqA 4060 ruFiveDWit[i]!) = true := by
  have h := Orb.allN_iff.1 kCD i hi
  rw [bAnd_iff, Nat.blt_eq] at h
  obtain ⟨h1, h3⟩ := h
  exact any_mem (by rw [c1_size]; exact h1) (eqA_R (wit_rep i hi) (c1_rep h1)
    (repF_pa (73 + i) (by omega)) (c1_repF h1) (gp_mem _ (by omega)) (c1_mem h1) (eqOnL_symm h3))

theorem base1_lt : ∀ t < 5, ruCase1BaseArr[t]! < 4060 := by decide

theorem rels1_ok : relsOKP 5 4060 ruCase1BaseArr ruFiveLines[1]! ruCase1Rels = true := by
  rw [relsOKP, List.all_eq_true]
  intro r hr
  have h := List.all_eq_true.1 kRels1 r hr
  unfold relAt1 at h
  simp only [bAnd_iff, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs : ruCase1BaseArr.size = 5 := by decide
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hs]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  rw [(rep_powArr x1_rep r.2.2).apply (base1_lt _ h2), ← (RepF.powF x1_repF r.2.2) _ (base1_lt _ h2)]
  exact Nat.eq_of_beq_eq_true h4

theorem tabs1 : TabsT 4060 12 10 5 S51.BP T51.NR T51.NR S51.S S51.SI S51.LR T51.Ts T51.LT T51.PT
    T51.QT 80 1024 4 1024 :=
  ⟨by decide, by decide, by decide, by decide, TS1.all, LT1.all, pt1B_all, qt1B_all⟩

theorem tc1 : TabChain 4060 12 10 5 S51.BP 64 64 T51.NR T51.NR 80 1024 4 1024 S51.S S51.SI
    S51.LR T51.Ts T51.LT T51.PT T51.QT ruCase1Arrs ruCase1BaseArr (ruCase1Base.map Fin.val) :=
  ⟨binds1, kPerm1, S51.ho, by norm_num, tabs1, rfl⟩

theorem fr1_ok : ∀ i < 5, fr1 i = 0 ∨ ∃ l e, fr1 i = 8 * l + e + 1 ∧ l < i ∧ e < 8 ∧
    (l, i, e) ∈ ruCase1Rels := by
  intro i hi
  have h := Orb.allN_iff.1 kFR1 i hi
  by_cases h0 : fr1 i = 0
  · exact Or.inl h0
  · right
    rw [show Nat.beq (fr1 i) 0 = false from Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)] at h
    simp only [bAnd_iff, Nat.blt_eq, List.any_eq_true] at h
    obtain ⟨h1, h2, r, hr, hr1, hr2, hr3⟩ := h
    refine ⟨(fr1 i - 1) / 8, (fr1 i - 1) % 8, by omega, h1, by omega, ?_⟩
    have e1 := Nat.eq_of_beq_eq_true hr1
    have e2 := Nat.eq_of_beq_eq_true hr2
    have e3 := Nat.eq_of_beq_eq_true hr3
    obtain ⟨a, b, c⟩ := r
    have e : (a, b, c) = ((fr1 i - 1) / 8, i, (fr1 i - 1) % 8) := by
      simp only [Prod.mk.injEq]
      exact ⟨e1, e2, e3⟩
    rw [← e]
    exact hr

theorem tail1 : ptailOK 4060 (rawLevels 4060 ruCase1Arrs ruCase1BaseArr) ruCase1BaseArr
    ruFiveLines[1]! (powPA 5 4060 ruFiveLines[1]!) ruCase1Rels ruFiveC1Cert.pts.toList 5 0
    (idA 4060) = true := by
  refine ptailOK_of_ptK_ tc1 x1_rep x1_repF (fun r hr => ?_) fr1_ok bs_lt ?_ (by norm_num) kTail1
  · have h := List.all_eq_true.1 kRels1 r hr
    unfold relAt1 at h
    rw [bAnd_iff, Nat.blt_eq] at h
    exact h.1
  · intro a A ha hA ⟨j, hj, e⟩
    have hR : A ∈ ruP := by
      refine (Subgroup.closure_le _).2 ?_ hA
      rintro _ ⟨i, rfl⟩
      exact faith1 i (by rw [hsize1]; exact i.2)
    have hm := c1sk_lt j hj
    unfold ckey1 cv1 at e
    rw [← keyA_treeArr c1tree c1g c1gs keys_lt hm, ← c1_get hm] at e
    have he := key_faith ha (c1_rep hm) hR (c1_mem hm) e
    exact any_mem (by rw [c1_size]; exact hm) ((eqA_iff ha (c1_rep hm)).2 he)

theorem cent1 : centOK 4060 ruCase1Arrs ruCase1BaseArr ruFiveLines[1]! ruCase1Rels ruFiveC1Gens
    ruFiveKeys ruFiveC1Cert 300 = true := by
  change centOKP 5 4060 ruCase1Arrs ruCase1BaseArr ruFiveLines[1]! ruCase1Rels ruFiveC1Gens
    ruFiveKeys ruFiveC1Cert 300 = true
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  have hs : ruCase1BaseArr.size = 5 := by decide
  refine ⟨⟨⟨⟨⟨rels1_ok, c1_enum⟩, c1_size⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, by rw [hs]; exact tail1⟩
  · have hk3 : k < 3 := hk
    exact commA_R (c1gs k hk3) x1_rep (c1g k hk3) x1_repF (c1g_mem k hk3) x1_mem
      (Orb.allN_iff.1 kComm1 k hk3)
  · have hk3 : k < 3 := hk
    exact (sift1_iff (c1gs k hk3)).2 (c1g_mem k hk3)

theorem derived : derivedOK 4060 ruFiveC1Gens ruFiveDGens ruFiveKeys ruFiveC1Cert ruFiveDCert
    ruFiveDWit[0]! ruFiveDWit[1]! ruFiveLines[1]! ruPLevels ruCase0BaseArr = true := by
  change derivedOKP 5 60 4060 ruFiveC1Gens ruFiveDGens ruFiveKeys ruFiveC1Cert ruFiveDCert
    ruFiveDWit[0]! ruFiveDWit[1]! ruFiveLines[1]! ruPLevels ruCase0BaseArr = true
  simp only [derivedOKP, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  have hgC : ruFiveC1Gens.size = 3 := rfl
  have hgD : ruFiveDGens.size = 2 := rfl
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨d_enum, d_size⟩, F2.validA_of_rep (wit_rep 0 (by norm_num))⟩,
    F2.validA_of_rep (wit_rep 1 (by norm_num))⟩, wit_mem 0 (by norm_num)⟩,
    wit_mem 1 (by norm_num)⟩, ?_⟩, fun k hk l hl => ?_⟩, fun k hk l hl => ?_⟩, ?_⟩,
    conjSimple⟩, fun k hk => ?_⟩, fun l hl => ?_⟩
  ·
    have h := rep_commutatorA (F2.validA_of_rep (wit_rep 0 (by norm_num)))
      (F2.validA_of_rep (wit_rep 1 (by norm_num)))
    rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (wit_rep 0 (by norm_num)),
      CFSG.RankThree.Native.permOfArr_eq_of_rep (wit_rep 1 (by norm_num))] at h
    have hP := comm_mem (gp_mem 73 (by norm_num)) (gp_mem 74 (by norm_num))
    rw [commutatorElement_def] at h hP
    have hf := (repF_pa 73 (by norm_num)).comp ((repF_pa 74 (by norm_num)).comp
      ((repF_pi 73 (by norm_num)).comp (repF_pi 74 (by norm_num))))
    rw [← mul_assoc, ← mul_assoc] at hf
    exact eqA_R (c1gs 2 (by norm_num)) h (repF_pa 69 (by norm_num)) hf
      (gp_mem 69 (by norm_num)) hP kCom
  ·
    rw [hgC] at hk
    rw [hgD] at hl
    have h := Orb.allN_iff.1 kDK (2 * k + l) (by omega)
    rw [show Nat.div (2 * k + l) 2 = k by change (2 * k + l) / 2 = k; omega,
      show Nat.mod (2 * k + l) 2 = l by change (2 * k + l) % 2 = l; omega] at h
    rw [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine any_mem (by rw [d_size]; exact h1) ?_
    have hc := rep_conjA (F2.validA_of_rep (c1gs k hk)) (dgs l hl)
    rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (c1gs k hk)] at hc
    have hcf : RepF 4060 (fun y => gC1 k (gD l (pi (Nat.add 67 k) y)))
        (gpC1 k * gpD l * (gpC1 k)⁻¹) := by
      have := (c1g k hk).comp ((dg l hl).comp (repF_pi (67 + k) (by omega)))
      rw [mul_assoc]
      exact this
    exact eqA_R hc (d_rep h1) hcf (d_repF h1)
      (ruP.mul_mem (ruP.mul_mem (c1g_mem k hk) (dg_mem l hl)) (ruP.inv_mem (c1g_mem k hk)))
      (d_mem h1) (eqOnL_symm h2)
  ·
    rw [hgC] at hk hl
    have h := Orb.allN_iff.1 kDC (3 * k + l) (by omega)
    rw [show Nat.div (3 * k + l) 3 = k by change (3 * k + l) / 3 = k; omega,
      show Nat.mod (3 * k + l) 3 = l by change (3 * k + l) % 3 = l; omega] at h
    rw [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine any_mem (by rw [d_size]; exact h1) ?_
    have hc := rep_commutatorA (F2.validA_of_rep (c1gs k hk)) (F2.validA_of_rep (c1gs l hl))
    rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (c1gs k hk),
      CFSG.RankThree.Native.permOfArr_eq_of_rep (c1gs l hl)] at hc
    have hP := comm_mem (c1g_mem k hk) (c1g_mem l hl)
    rw [commutatorElement_def] at hc hP
    have hcf : RepF 4060 (fun y => gC1 k (gC1 l (pi (Nat.add 67 k) (pi (Nat.add 67 l) y))))
        (gpC1 k * gpC1 l * (gpC1 k)⁻¹ * (gpC1 l)⁻¹) := by
      have := (c1g k hk).comp ((c1g l hl).comp ((repF_pi (67 + k) (by omega)).comp
        (repF_pi (67 + l) (by omega))))
      rw [← mul_assoc, ← mul_assoc] at this
      exact this
    exact eqA_R hc (d_rep h1) hcf (d_repF h1) hP (d_mem h1) (eqOnL_symm h2)
  ·
    have h := kNC
    rw [Bool.not_eq_true'] at h
    rw [Bool.not_eq_true']
    exact neA_R (rep_compA (dgs 0 (by norm_num)) (dgs 1 (by norm_num)))
      (rep_compA (dgs 1 (by norm_num)) (dgs 0 (by norm_num)))
      ((dg 0 (by norm_num)).comp (dg 1 (by norm_num)))
      ((dg 1 (by norm_num)).comp (dg 0 (by norm_num))) h
  ·
    rw [c1_size] at hk
    have hz := Orb.allN_iff.1 kZ1 k hk
    unfold zAt1 at hz
    rw [CFSG.KS.SporSch.strictB_val] at hz
    rw [Bool.or_eq_true]
    by_cases hw : ZW1.getD k 0 < 100
    · rw [show Nat.blt (ZW1.getD k 0) 100 = true from Nat.blt_eq.mpr hw] at hz
      simp only [bAnd_iff, Nat.blt_eq, Bool.not_eq_true'] at hz
      obtain ⟨h1, h2, h3⟩ := hz
      left
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      intro hall
      have hl : ZW1.getD k 0 - 1 < 2 := by omega
      have hcomm := (allLt_iff.1 hall) _ (show ZW1.getD k 0 - 1 < ruFiveDGens.size from hl)
      have e := (eqA_iff (rep_compA (c1_rep hk) (dgs _ hl))
        (rep_compA (dgs _ hl) (c1_rep hk))).1 hcomm
      have := eqOnL_of_eq bs_lt ((c1_repF hk).comp (dg _ hl))
        ((e ▸ (dg _ hl).comp (c1_repF hk)))
      rw [Bool.eq_false_iff] at h3
      exact h3 this
    · rw [show Nat.blt (ZW1.getD k 0) 100 = false from Bool.eq_false_iff.2 fun h =>
        hw (Nat.blt_eq.mp h)] at hz
      simp only [bAnd_iff, Nat.blt_eq] at hz
      obtain ⟨h1, h3⟩ := hz
      right
      rw [List.any_eq_true]
      refine ⟨ZW1.getD k 0 - 100, List.mem_range.2 h1, ?_⟩
      exact eqA_R (c1_rep hk) (rep_powArr x1_rep _) (c1_repF hk) (RepF.powF x1_repF _)
        (c1_mem hk) (ruP.pow_mem x1_mem _) h3
  · rw [hgD] at hl
    exact (sift0_iff (dgs l hl)).2 (dg_mem l hl)

theorem eq1 : eqA 4060 ruFiveC1Gens[0]! ruFiveLines[1]! = true := by
  rw [c1gens_eq 0 (by norm_num), Nat.eq_of_beq_eq_true kEq1, ← arr_eq 3 (by norm_num)]
  rw [ruFiveLines, getElem!_pos _ 1 (by simp), Array.getElem_ofFn]
  exact eqA_self' _

theorem case1 : caseChainOK2 4060 ruCase1Arrs ruCase1BaseArr ruCase1Words (ruArr4060 0)
      (ruArr4060 1) = true ∧
    centOK 4060 ruCase1Arrs ruCase1BaseArr ruFiveLines[1]! ruCase1Rels ruFiveC1Gens ruFiveKeys
      ruFiveC1Cert 300 = true ∧
    derivedOK 4060 ruFiveC1Gens ruFiveDGens ruFiveKeys ruFiveC1Cert ruFiveDCert ruFiveDWit[0]!
      ruFiveDWit[1]! ruFiveLines[1]! ruPLevels ruCase0BaseArr = true ∧
    eqA 4060 ruFiveC1Gens[0]! ruFiveLines[1]! = true :=
  ⟨chain1, cent1, derived, eq1⟩

end CertificateChecks.KernelRuFive

end
