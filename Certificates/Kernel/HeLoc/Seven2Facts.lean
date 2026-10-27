module

public import Certificates.Kernel.HeLoc.Seven2K
public import Certificates.Kernel.HeLoc.Seven0Facts
public import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.RankThree.Native
open CFSG.RankThree.PartOne CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch


theorem cs2_eq (j : Nat) (hj : j < 10) : heSevenCase2Arrs[j]! = unpack 8330 14 (S72.S j) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound S72T.all j hj
  rw [← S72T.eq] at h
  rw [heSevenCase2Arrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change hexTable 4 8330 (8330 * j) heSevenCase2Hex = _
  rw [h, Nat.eq_of_beq_eq_true (allN_spec k2Bind j hj)]

theorem binds2 : Binds 8330 14 S72.S 10 7 S72.BP heSevenCase2Arrs
    (heSevenCase2Base.map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [heSevenCase2Arrs], cs2_eq, by decide,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec k2Base t ht)⟩

theorem words2 : heSevenCase2Words = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 10 derivs2 := by
  decide

theorem chain2 : caseChainOK3 8330 heSevenCase2Arrs heSevenCase2BaseArr heSevenCase2Words
    (heGen 0) (heGen 1) heUArr = true := by
  have hg := k2Gen
  rw [bAnd_iff] at hg
  have hU : Rep 8330 heSevenCase2Arrs[2]! heAutU := by
    rw [cs2_eq 2 (by norm_num)]
    have hall := CFSG.KC.Misc.Clos.forall_of_chunks 833 10 _ fun c hc => by
      have h := allN_spec k2U c hc
      unfold u2B at h
      exact h
    intro x
    rw [Five.unpackGet x.2]
    have h1 := hall x (by omega)
    rw [CFSG.KS.SporSch.blt_true x.2] at h1
    rw [Nat.eq_of_beq_eq_true h1]
    exact Five.hU x x.2
  exact case_chain binds2 S72.head S72.ho (by norm_num) k2Perm words2
    (Nat.eq_of_beq_eq_true k2Prod)
    (by rw [cs2_eq 0 (by norm_num), heGen_eq 0 (by norm_num), Nat.eq_of_beq_eq_true hg.1])
    (by rw [cs2_eq 1 (by norm_num), heGen_eq 1 (by norm_num), Nat.eq_of_beq_eq_true hg.2]) hU
    (by norm_num)

theorem sift2_iff {g : Array Nat} {G : Equiv.Perm (Fin 8330)} (hG : Rep 8330 g G) :
    siftA 8330 (rawLevels 8330 heSevenCase2Arrs heSevenCase2BaseArr) heSevenCase2BaseArr 0 g =
      true ↔ G ∈ heAutGroup :=
  case_sift_iff (by norm_num) (by simp [heSevenCase2Arrs]) (by decide) chain2 hG

theorem faith2 : ∀ j < heSevenCase2Arrs.size, permOfArr 8330 heSevenCase2Arrs[j]! ∈ heAutGroup :=
  (case_faithful (by norm_num) (by simp [heSevenCase2Arrs]) (by decide) chain2).2

@[expose] noncomputable def gpC2 (k : Nat) : Equiv.Perm (Fin 8330) := gp (70 + k)

theorem c2gens_eq (k : Nat) (hk : k < 3) : heSevenC2Gens[k]! = unpack 8330 14 (A (70 + k)) := by
  rw [heSevenC2Gens]
  interval_cases k
  · exact (lit3_0 _ _ _).trans (arr_eq 70 (by norm_num))
  · exact (lit3_1 _ _ _).trans (arr_eq 71 (by norm_num))
  · exact (lit3_2 _ _ _).trans (arr_eq 72 (by norm_num))

theorem c2gs : ∀ k < 3, Rep 8330 heSevenC2Gens[k]! (gpC2 k) := fun k hk => by
  rw [c2gens_eq k hk]
  exact rep_gp _ (by omega)

theorem c2g : ∀ k < 3, RepF 8330 (gC2 k) (gpC2 k) := fun k hk => repF_pa (70 + k) (by omega)

theorem fl_c2 : FL.getD 70 0 = 0 ∧ FL.getD 71 0 = 0 ∧ FL.getD 72 0 = 0 ∧ FL.getD 73 0 = 0 ∧
    FL.getD 74 0 = 0 := by decide

theorem c2g_inP : ∀ k < 3, gpC2 k ∈ heP := by
  intro k hk
  have h := fl_c2
  interval_cases k
  · exact (gp_mem 70 (by norm_num)).2.2 h.1
  · exact (gp_mem 71 (by norm_num)).2.2 h.2.1
  · exact (gp_mem 72 (by norm_num)).2.2 h.2.2.1

theorem ctree2 : TreeOK 3 98 C2.P C2.L := treeOK_of fun i hi h0 => by
  have h := allN_spec kCTree2 i hi
  rwa [beq_zero_false h0] at h

theorem pfaith : ∀ x ∈ heP, ∀ y ∈ heP, (x ∈ heP ↔ y ∈ heP) →
    (∀ b (hb : b ∈ bs), (x ⟨b, bs_lt b hb⟩ : Nat) = y ⟨b, bs_lt b hb⟩) → x = y :=
  fun x hx y hy _ hb => faithful x (heP_le_heAutGroup hx) y (heP_le_heAutGroup hy)
    (iff_of_true hx hy) hb

theorem cedges2 : ∀ i < 98, ∀ k < 3, CE2 i k < 98 ∧
    treeArr 8330 heSevenC2Gens C2.P C2.L (CE2 i k) =
      compA 8330 heSevenC2Gens[k]! (treeArr 8330 heSevenC2Gens C2.P C2.L i) :=
  edges_of_edgeAtK ctree2 c2g c2gs hmulP c2g_inP (fun k hk => iff_of_true (c2g_inP k hk) rfl)
    (fun _ _ => by decide) bs_lt pfaith fun i hi => allN_spec kCEdge2 i hi

theorem ckeys2_inj : ∀ a < 98, ∀ b < 98,
    keyA 8330 heSevenKeys (treeArr 8330 heSevenC2Gens C2.P C2.L a) =
      keyA 8330 heSevenKeys (treeArr 8330 heSevenC2Gens C2.P C2.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := ckey2) fun j hj => allN_spec kCSort2 j hj
  intro a ha b hb e
  rw [keyA_treeArr ctree2 c2g c2gs keys_lt ha, keyA_treeArr ctree2 c2g c2gs keys_lt hb] at e
  exact hk a ha b hb e

theorem c2_pts : heSevenC2Cert.pts =
    Array.ofFn (n := 98) fun i => treeArr 8330 heSevenC2Gens C2.P C2.L i.val :=
  enumBfs_tree ctree2 c2gs (by rfl) (by norm_num) (by norm_num) ckeys2_inj cedges2 kCReplay2

theorem c2_enum : enumOK 8330 heSevenC2Gens heSevenKeys heSevenC2Cert = true :=
  enumOK_tree ctree2 c2gs (by rfl) (by norm_num) (by norm_num) ckeys2_inj cedges2

theorem c2_size : heSevenC2Cert.pts.size = 98 := by rw [c2_pts, Array.size_ofFn]

theorem c2_get {k : Nat} (hk : k < 98) :
    heSevenC2Cert.pts[k]! = treeArr 8330 heSevenC2Gens C2.P C2.L k := by
  rw [c2_pts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem c2_rep {k : Nat} (hk : k < 98) :
    Rep 8330 heSevenC2Cert.pts[k]! (treePerm gpC2 C2.P C2.L k) := by
  rw [c2_get hk]
  exact rep_treeArr ctree2 c2gs k hk

theorem c2_repF {k : Nat} (hk : k < 98) : RepF 8330 (cv2 k) (treePerm gpC2 C2.P C2.L k) :=
  repF_trV ctree2 c2g 98 k hk.le hk

theorem c2_inP {k : Nat} (hk : k < 98) : treePerm gpC2 C2.P C2.L k ∈ heP :=
  (trQ_spec ctree2 hmulP c2g_inP (fun k hk => iff_of_true (c2g_inP k hk) rfl)
    (fun _ _ => by decide) 98 k hk.le hk).1

@[expose] noncomputable def gpA2 (k : Nat) : Equiv.Perm (Fin 8330) := gp (73 + k)

theorem a2gens_eq (k : Nat) (hk : k < 2) : heSevenA2Gens[k]! = unpack 8330 14 (A (73 + k)) := by
  rw [heSevenA2Gens]
  interval_cases k
  · exact (lit2_0 _ _).trans (arr_eq 73 (by norm_num))
  · exact (lit2_1 _ _).trans (arr_eq 74 (by norm_num))

theorem a2gs : ∀ k < 2, Rep 8330 heSevenA2Gens[k]! (gpA2 k) := fun k hk => by
  rw [a2gens_eq k hk]
  exact rep_gp _ (by omega)

theorem a2g : ∀ k < 2, RepF 8330 (gA2 k) (gpA2 k) := fun k hk => repF_pa (73 + k) (by omega)

theorem a2g_inP : ∀ k < 2, gpA2 k ∈ heP := by
  intro k hk
  have h := fl_c2
  interval_cases k
  · exact (gp_mem 73 (by norm_num)).2.2 h.2.2.2.1
  · exact (gp_mem 74 (by norm_num)).2.2 h.2.2.2.2

theorem atree2 : TreeOK 2 49 A2.P A2.L := treeOK_of fun i hi h0 => by
  have h := allN_spec kATree2 i hi
  rwa [beq_zero_false h0] at h

theorem aedges2 : ∀ i < 49, ∀ k < 2, AE2 i k < 49 ∧
    treeArr 8330 heSevenA2Gens A2.P A2.L (AE2 i k) =
      compA 8330 heSevenA2Gens[k]! (treeArr 8330 heSevenA2Gens A2.P A2.L i) :=
  edges_of_edgeAtK atree2 a2g a2gs hmulP a2g_inP (fun k hk => iff_of_true (a2g_inP k hk) rfl)
    (fun _ _ => by decide) bs_lt pfaith fun i hi => allN_spec kAEdge2 i hi

theorem akeys2_inj : ∀ a < 49, ∀ b < 49,
    keyA 8330 heSevenKeys (treeArr 8330 heSevenA2Gens A2.P A2.L a) =
      keyA 8330 heSevenKeys (treeArr 8330 heSevenA2Gens A2.P A2.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := akey2) fun j hj => allN_spec kASort2 j hj
  intro a ha b hb e
  rw [keyA_treeArr atree2 a2g a2gs keys_lt ha, keyA_treeArr atree2 a2g a2gs keys_lt hb] at e
  exact hk a ha b hb e

theorem a2_pts : heSevenA2Cert.pts =
    Array.ofFn (n := 49) fun i => treeArr 8330 heSevenA2Gens A2.P A2.L i.val :=
  enumBfs_tree atree2 a2gs (by rfl) (by norm_num) (by norm_num) akeys2_inj aedges2 kAReplay2

theorem a2_enum : enumOK 8330 heSevenA2Gens heSevenKeys heSevenA2Cert = true :=
  enumOK_tree atree2 a2gs (by rfl) (by norm_num) (by norm_num) akeys2_inj aedges2

theorem a2_size : heSevenA2Cert.pts.size = 49 := by rw [a2_pts, Array.size_ofFn]

theorem a2_get {k : Nat} (hk : k < 49) :
    heSevenA2Cert.pts[k]! = treeArr 8330 heSevenA2Gens A2.P A2.L k := by
  rw [a2_pts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem a2_rep {k : Nat} (hk : k < 49) :
    Rep 8330 heSevenA2Cert.pts[k]! (treePerm gpA2 A2.P A2.L k) := by
  rw [a2_get hk]
  exact rep_treeArr atree2 a2gs k hk

theorem a2_repF {k : Nat} (hk : k < 49) : RepF 8330 (av2 k) (treePerm gpA2 A2.P A2.L k) :=
  repF_trV atree2 a2g 49 k hk.le hk

theorem a2_inP {k : Nat} (hk : k < 49) : treePerm gpA2 A2.P A2.L k ∈ heP :=
  (trQ_spec atree2 hmulP a2g_inP (fun k hk => iff_of_true (a2g_inP k hk) rfl)
    (fun _ _ => by decide) 49 k hk.le hk).1

theorem x2_rep : Rep 8330 heSevenLines[2]! (lp 2) := rep_line 2 (by norm_num)

theorem x2_repF : RepF 8330 x2 (lp 2) := repF_ln 2 (by norm_num)

theorem x2_inP : lp 2 ∈ heP := lp_inP 2 (by norm_num)

theorem lp2_eq : lp 2 = gp 70 := by
  rw [lp, gp_one 2 (by norm_num), one_mul, inv_one, mul_one]
  rfl

theorem base2_lt : ∀ t < 7, heSevenCase2BaseArr[t]! < 8330 := by decide

theorem rels_ok2 : relsOKP 7 8330 heSevenCase2BaseArr heSevenLines[2]! heSevenCase2Rels = true := by
  rw [relsOKP, List.all_eq_true]
  intro r hr
  have h := List.all_eq_true.1 kRels2 r hr
  unfold relAt2 at h
  simp only [bAnd_iff, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs : heSevenCase2BaseArr.size = 7 := by decide
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hs]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  rw [(rep_powArr x2_rep r.2.2).apply (base2_lt _ h2), ← (RepF.powF x2_repF r.2.2) _ (base2_lt _ h2)]
  exact Nat.eq_of_beq_eq_true h4

theorem tabs2 : TabsT 8330 14 10 7 S72.BP T72.NR T72.NR S72.S S72.SI S72.LR T72.Ts T72.LT T72.PT
    T72.QT 163 1024 9 1024 :=
  ⟨by decide, by decide, by decide, by decide, TS2.all, LT2.all, pt2B_all, qt2B_all⟩

theorem tc2 : TabChain 8330 14 10 7 S72.BP 131 64 T72.NR T72.NR 163 1024 9 1024 S72.S S72.SI
    S72.LR T72.Ts T72.LT T72.PT T72.QT heSevenCase2Arrs heSevenCase2BaseArr
    (heSevenCase2Base.map Fin.val) :=
  ⟨binds2, k2Perm, S72.ho, by norm_num, tabs2, rfl⟩

theorem fr_ok2 : ∀ i < 7, fr2 i = 0 ∨ ∃ l e, fr2 i = 8 * l + e + 1 ∧ l < i ∧ e < 8 ∧
    (l, i, e) ∈ heSevenCase2Rels := by
  intro i hi
  have h := allN_spec kFR2 i hi
  by_cases h0 : fr2 i = 0
  · exact Or.inl h0
  · right
    rw [show Nat.beq (fr2 i) 0 = false from Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)] at h
    simp only [bAnd_iff, Nat.blt_eq, List.any_eq_true] at h
    obtain ⟨h1, h2, r, hr, hr1, hr2, hr3⟩ := h
    refine ⟨(fr2 i - 1) / 8, (fr2 i - 1) % 8, by omega, h1, by omega, ?_⟩
    have e1 := Nat.eq_of_beq_eq_true hr1
    have e2 := Nat.eq_of_beq_eq_true hr2
    have e3 := Nat.eq_of_beq_eq_true hr3
    obtain ⟨a, b, c⟩ := r
    have e : (a, b, c) = ((fr2 i - 1) / 8, i, (fr2 i - 1) % 8) := by
      simp only [Prod.mk.injEq]
      exact ⟨e1, e2, e3⟩
    rw [← e]
    exact hr

theorem csk2_lt : ∀ j < 98, C2.SK j < 98 := sk_lt fun j hj => by
  have h := allN_spec kCSort2 j hj
  unfold sortAtK at h
  rw [bAnd_iff, bAnd_iff, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1⟩

theorem tail2 : ptailOK 8330 (rawLevels 8330 heSevenCase2Arrs heSevenCase2BaseArr)
    heSevenCase2BaseArr heSevenLines[2]! (powPA 7 8330 heSevenLines[2]!) heSevenCase2Rels
    heSevenC2Cert.pts.toList 7 0 (idA 8330) = true := by
  refine ptailOK_of_ptK_ tc2 x2_rep x2_repF (fun r hr => ?_) fr_ok2 bs_lt ?_ (by norm_num) kTail2
  · have h := List.all_eq_true.1 kRels2 r hr
    unfold relAt2 at h
    rw [bAnd_iff, Nat.blt_eq] at h
    exact h.1
  · intro a A ha hA ⟨j, hj, e⟩
    have hR : A ∈ heAutGroup := by
      refine (Subgroup.closure_le _).2 ?_ hA
      rintro _ ⟨i, rfl⟩
      exact faith2 i (by simpa [heSevenCase2Arrs] using i.2)
    have hm := csk2_lt j hj
    unfold ckey2 cv2 at e
    rw [← keyA_treeArr ctree2 c2g c2gs keys_lt hm, ← c2_get hm] at e
    have he := key_faith ha (c2_rep hm) hR (heP_le_heAutGroup (c2_inP hm)) e
    exact any_mem (by rw [c2_size]; exact hm) ((eqA_iff ha (c2_rep hm)).2 he)

theorem cent2 : centOKP 7 8330 heSevenCase2Arrs heSevenCase2BaseArr heSevenLines[2]!
    heSevenCase2Rels heSevenC2Gens heSevenKeys heSevenC2Cert 98 = true := by
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  have hs : heSevenCase2BaseArr.size = 7 := by decide
  refine ⟨⟨⟨⟨⟨rels_ok2, c2_enum⟩, c2_size⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, by rw [hs]; exact tail2⟩
  · have hk3 : k < 3 := hk
    exact commA_R (c2gs k hk3) x2_rep (c2g k hk3) x2_repF (heP_le_heAutGroup (c2g_inP k hk3))
      (heP_le_heAutGroup x2_inP) (allN_spec kComm2 k hk3)
  · have hk3 : k < 3 := hk
    exact (sift2_iff (c2gs k hk3)).2 (heP_le_heAutGroup (c2g_inP k hk3))

theorem normal2 : normalOKP 7 8330 heSevenC2Gens heSevenA2Gens heSevenKeys heSevenC2Cert
    heSevenA2Cert 49 heLevels heBase.toArray = true := by
  simp only [normalOKP, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨⟨a2_enum, a2_size⟩, fun k hk => ?_⟩, fun l hl => ?_⟩, fun k hk => ?_⟩, fun l hl => ?_⟩
  · rw [a2_size] at hk
    exact eqA_P (rep_powArr (a2_rep hk) 7) rep_idA (RepF.powF (a2_repF hk) 7) RepF.one
      (heP.pow_mem (a2_inP hk) 7) heP.one_mem (allN_spec kAPow2 k hk)
  · have hl2 : l < 2 := hl
    have h := allN_spec kAinC2 l hl2
    rw [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨h1, h3⟩ := h
    refine any_mem (by rw [c2_size]; exact h1) ?_
    exact eqA_P (a2gs l hl2) (c2_rep h1) (a2g l hl2) (c2_repF h1) (a2g_inP l hl2) (c2_inP h1)
      (eqOnL_symm h3)
  · have hk3 : k < 3 := hk
    intro l hl
    have hl2 : l < 2 := hl
    have h := allN_spec kConj2 (2 * k + l) (by omega)
    rw [show Nat.div (2 * k + l) 2 = k by change (2 * k + l) / 2 = k; omega,
      show Nat.mod (2 * k + l) 2 = l by change (2 * k + l) % 2 = l; omega] at h
    rw [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine any_mem (by rw [a2_size]; exact h1) ?_
    have hc := rep_conjA (CFSG.RankThree.Native.F2.validA_of_rep (c2gs k hk3)) (a2gs l hl2)
    rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (c2gs k hk3)] at hc
    have hcf : RepF 8330 (fun y => gC2 k (gA2 l (pi (Nat.add 70 k) y)))
        (gpC2 k * gpA2 l * (gpC2 k)⁻¹) := by
      have := (c2g k hk3).comp ((a2g l hl2).comp (repF_pi (70 + k) (by omega)))
      rw [mul_assoc]
      exact this
    have hP : gpC2 k * gpA2 l * (gpC2 k)⁻¹ ∈ heP :=
      heP.mul_mem (heP.mul_mem (c2g_inP k hk3) (a2g_inP l hl2)) (heP.inv_mem (c2g_inP k hk3))
    exact eqA_P hc (a2_rep h1) hcf (a2_repF h1) hP (a2_inP h1) (eqOnL_symm h2)
  · have hl2 : l < 2 := hl
    rw [show heLevels = rawLevels 8330 heStrongArrs heBase.toArray from rfl,
      mem_heP_iff_siftA (a2gs l hl2)]
    exact a2g_inP l hl2

theorem self2 : selfCentOKG 8330 heSevenA2Gens heSevenC2Cert heSevenA2Cert = true := by
  simp only [selfCentOKG, Bool.and_eq_true, allLt_iff]
  refine ⟨fun l hl l' hl' => ?_, fun c hc => ?_⟩
  · have hl2 : l < 2 := hl
    have hl2' : l' < 2 := hl'
    exact commA_R (a2gs l hl2) (a2gs l' hl2') (a2g l hl2) (a2g l' hl2')
      (heP_le_heAutGroup (a2g_inP l hl2)) (heP_le_heAutGroup (a2g_inP l' hl2'))
      (allN_spec (allN_spec kACom2 l hl2) l' hl2')
  · rw [c2_size] at hc
    have hz := allN_spec kS2 c hc
    unfold sAt2 at hz
    rw [CFSG.KS.SporSch.strictB_val] at hz
    rw [Bool.or_eq_true]
    by_cases hw : SW2.getD c 0 < 100
    · rw [show Nat.blt (SW2.getD c 0) 100 = true from Nat.blt_eq.mpr hw] at hz
      simp only [bAnd_iff, Nat.blt_eq, Bool.not_eq_true'] at hz
      obtain ⟨h1, h2, h3⟩ := hz
      left
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      intro hall
      have hl : SW2.getD c 0 - 1 < 2 := by omega
      have hcomm := (allLt_iff.1 hall) _ (show SW2.getD c 0 - 1 < heSevenA2Gens.size from hl)
      have e := (eqA_iff (rep_compA (c2_rep hc) (a2gs _ hl))
        (rep_compA (a2gs _ hl) (c2_rep hc))).1 hcomm
      have := eqOnL_of_eq bs_lt ((c2_repF hc).comp (a2g _ hl)) ((e ▸ (a2g _ hl).comp (c2_repF hc)))
      rw [Bool.eq_false_iff] at h3
      exact h3 this
    · rw [show Nat.blt (SW2.getD c 0) 100 = false from Bool.eq_false_iff.2 fun h =>
        hw (Nat.blt_eq.mp h)] at hz
      rw [bAnd_iff, Nat.blt_eq] at hz
      obtain ⟨h1, h3⟩ := hz
      right
      exact any_mem (by rw [a2_size]; exact h1)
        (eqA_P (c2_rep hc) (a2_rep h1) (c2_repF hc) (a2_repF h1) (c2_inP hc) (a2_inP h1) h3)

open Certificates in
open CFSG.RankThree.PartOne CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native in
theorem facts2 :
    caseChainOK3 8330 heSevenCase2Arrs heSevenCase2BaseArr heSevenCase2Words (heGen 0) (heGen 1)
        heUArr = true ∧
      centOKP 7 8330 heSevenCase2Arrs heSevenCase2BaseArr heSevenLines[2]! heSevenCase2Rels
        heSevenC2Gens heSevenKeys heSevenC2Cert 98 = true ∧
      eqA 8330 heSevenC2Gens[0]! heSevenLines[2]! = true ∧
      normalOKP 7 8330 heSevenC2Gens heSevenA2Gens heSevenKeys heSevenC2Cert heSevenA2Cert 49
        heLevels heBase.toArray = true ∧
      selfCentOKG 8330 heSevenA2Gens heSevenC2Cert heSevenA2Cert = true := by
  refine ⟨chain2, cent2, ?_, normal2, self2⟩
  refine (eqA_iff (c2gs 0 (by norm_num)) x2_rep).2 ?_
  rw [lp2_eq]
  rfl

end CertificateChecks.KernelHeLoc.Seven

end
