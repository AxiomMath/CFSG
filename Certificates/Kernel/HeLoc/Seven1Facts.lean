module

public import Certificates.Kernel.HeLoc.Seven1K
public import Certificates.Kernel.HeLoc.Seven0Facts
public import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
public import CFSG.RankThree.PartOne.KS.PKitSimple
public import CFSG.Certificates.Kernel.HeLoc.GroupConjSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.RankThree.Native
open CFSG.RankThree.PartOne CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open scoped commutatorElement


theorem cs1_eq (j : Nat) (hj : j < 11) : heSevenCase1Arrs[j]! = unpack 8330 14 (S71.S j) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound S71T.all j hj
  rw [← S71T.eq] at h
  rw [heSevenCase1Arrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change hexTable 4 8330 (8330 * j) heSevenCase1Hex = _
  rw [h, Nat.eq_of_beq_eq_true (allN_spec k1Bind j hj)]

theorem binds1 : Binds 8330 14 S71.S 11 10 S71.BP heSevenCase1Arrs
    (heSevenCase1Base.map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [heSevenCase1Arrs], cs1_eq, by decide,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec k1Base t ht)⟩

theorem words1 : heSevenCase1Words = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 11 derivs1 := by
  decide

theorem chain1 : caseChainOK3 8330 heSevenCase1Arrs heSevenCase1BaseArr heSevenCase1Words
    (heGen 0) (heGen 1) heUArr = true := by
  have hg := k1Gen
  rw [bAnd_iff] at hg
  have hU : Rep 8330 heSevenCase1Arrs[2]! heAutU := by
    rw [cs1_eq 2 (by norm_num)]
    have hall := CFSG.KC.Misc.Clos.forall_of_chunks 833 10 _ fun c hc => by
      have h := allN_spec k1U c hc
      unfold u1B at h
      exact h
    intro x
    rw [Five.unpackGet x.2]
    have h1 := hall x (by omega)
    rw [CFSG.KS.SporSch.blt_true x.2] at h1
    rw [Nat.eq_of_beq_eq_true h1]
    exact Five.hU x x.2
  exact case_chain binds1 S71.head S71.ho (by norm_num) k1Perm words1
    (Nat.eq_of_beq_eq_true k1Prod)
    (by rw [cs1_eq 0 (by norm_num), heGen_eq 0 (by norm_num), Nat.eq_of_beq_eq_true hg.1])
    (by rw [cs1_eq 1 (by norm_num), heGen_eq 1 (by norm_num), Nat.eq_of_beq_eq_true hg.2]) hU
    (by norm_num)

theorem sift1_iff {g : Array Nat} {G : Equiv.Perm (Fin 8330)} (hG : Rep 8330 g G) :
    siftA 8330 (rawLevels 8330 heSevenCase1Arrs heSevenCase1BaseArr) heSevenCase1BaseArr 0 g =
      true ↔ G ∈ heAutGroup :=
  case_sift_iff (by norm_num) (by simp [heSevenCase1Arrs]) (by decide) chain1 hG

theorem faith1 : ∀ j < heSevenCase1Arrs.size, permOfArr 8330 heSevenCase1Arrs[j]! ∈ heAutGroup :=
  (case_faithful (by norm_num) (by simp [heSevenCase1Arrs]) (by decide) chain1).2

@[expose] noncomputable def gpC1 (k : Nat) : Equiv.Perm (Fin 8330) := gp (65 + k)

theorem c1gens_eq (k : Nat) (hk : k < 3) : heSevenC1Gens[k]! = unpack 8330 14 (A (65 + k)) := by
  rw [heSevenC1Gens]
  interval_cases k
  · exact (lit3_0 _ _ _).trans (arr_eq 65 (by norm_num))
  · exact (lit3_1 _ _ _).trans (arr_eq 66 (by norm_num))
  · exact (lit3_2 _ _ _).trans (arr_eq 67 (by norm_num))

theorem c1gs : ∀ k < 3, Rep 8330 heSevenC1Gens[k]! (gpC1 k) := fun k hk => by
  rw [c1gens_eq k hk]
  exact rep_gp _ (by omega)

theorem c1g : ∀ k < 3, RepF 8330 (gC1 k) (gpC1 k) := fun k hk => repF_pa (65 + k) (by omega)

theorem fl_c1 : FL.getD 65 0 = 0 ∧ FL.getD 66 0 = 0 ∧ FL.getD 67 0 = 0 ∧ FL.getD 68 0 = 0 ∧
    FL.getD 69 0 = 0 := by decide

theorem c1g_inP : ∀ k < 3, gpC1 k ∈ heP := by
  intro k hk
  have h := fl_c1
  interval_cases k
  · exact (gp_mem 65 (by norm_num)).2.2 h.1
  · exact (gp_mem 66 (by norm_num)).2.2 h.2.1
  · exact (gp_mem 67 (by norm_num)).2.2 h.2.2.1

theorem pfaith1 : ∀ x ∈ heP, ∀ y ∈ heP, (x ∈ heP ↔ y ∈ heP) →
    (∀ b (hb : b ∈ bs), (x ⟨b, bs_lt b hb⟩ : Nat) = y ⟨b, bs_lt b hb⟩) → x = y :=
  fun x hx y hy _ hb => faithful x (heP_le_heAutGroup hx) y (heP_le_heAutGroup hy)
    (iff_of_true hx hy) hb

theorem ctree1 : TreeOK 3 1176 C1.P C1.L := treeOK_of fun i hi h0 => by
  have h := allN_spec kCTree1 i hi
  rwa [beq_zero_false h0] at h

theorem cedges1 : ∀ i < 1176, ∀ k < 3, CE1 i k < 1176 ∧
    treeArr 8330 heSevenC1Gens C1.P C1.L (CE1 i k) =
      compA 8330 heSevenC1Gens[k]! (treeArr 8330 heSevenC1Gens C1.P C1.L i) :=
  edges_of_edgeAtK ctree1 c1g c1gs hmulP c1g_inP (fun k hk => iff_of_true (c1g_inP k hk) rfl)
    (fun _ _ => by decide) bs_lt pfaith1 fun i hi => allN_spec kCEdge1 i hi

theorem ckeys1_inj : ∀ a < 1176, ∀ b < 1176,
    keyA 8330 heSevenKeys (treeArr 8330 heSevenC1Gens C1.P C1.L a) =
      keyA 8330 heSevenKeys (treeArr 8330 heSevenC1Gens C1.P C1.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := ckey1) fun j hj => allN_spec kCSort1 j hj
  intro a ha b hb e
  rw [keyA_treeArr ctree1 c1g c1gs keys_lt ha, keyA_treeArr ctree1 c1g c1gs keys_lt hb] at e
  exact hk a ha b hb e

theorem c1_pts : heSevenC1Cert.pts =
    Array.ofFn (n := 1176) fun i => treeArr 8330 heSevenC1Gens C1.P C1.L i.val :=
  enumBfs_tree ctree1 c1gs (by rfl) (by norm_num) (by norm_num) ckeys1_inj cedges1 kCReplay1

theorem c1_enum : enumOK 8330 heSevenC1Gens heSevenKeys heSevenC1Cert = true :=
  enumOK_tree ctree1 c1gs (by rfl) (by norm_num) (by norm_num) ckeys1_inj cedges1

theorem c1_size : heSevenC1Cert.pts.size = 1176 := by rw [c1_pts, Array.size_ofFn]

theorem c1_get {k : Nat} (hk : k < 1176) :
    heSevenC1Cert.pts[k]! = treeArr 8330 heSevenC1Gens C1.P C1.L k := by
  rw [c1_pts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem c1_rep {k : Nat} (hk : k < 1176) :
    Rep 8330 heSevenC1Cert.pts[k]! (treePerm gpC1 C1.P C1.L k) := by
  rw [c1_get hk]
  exact rep_treeArr ctree1 c1gs k hk

theorem c1_repF {k : Nat} (hk : k < 1176) : RepF 8330 (cv1 k) (treePerm gpC1 C1.P C1.L k) :=
  repF_trV ctree1 c1g 1176 k hk.le hk

theorem c1_inP {k : Nat} (hk : k < 1176) : treePerm gpC1 C1.P C1.L k ∈ heP :=
  (trQ_spec ctree1 hmulP c1g_inP (fun k hk => iff_of_true (c1g_inP k hk) rfl)
    (fun _ _ => by decide) 1176 k hk.le hk).1

@[expose] noncomputable def gpD1 (l : Nat) : Equiv.Perm (Fin 8330) :=
  if l = 0 then ⁅gpC1 1, gpC1 2⁆ else gpC1 2

theorem dgs1 : ∀ l < 2, Rep 8330 heSevenDGens1[l]! (gpD1 l) := by
  intro l hl
  rw [heSevenDGens1]
  interval_cases l
  · rw [lit2_0, gpD1, if_pos rfl]
    have h := rep_commutatorA (F2.validA_of_rep (c1gs 1 (by norm_num)))
      (F2.validA_of_rep (c1gs 2 (by norm_num)))
    rwa [CFSG.RankThree.Native.permOfArr_eq_of_rep (c1gs 1 (by norm_num)),
      CFSG.RankThree.Native.permOfArr_eq_of_rep (c1gs 2 (by norm_num))] at h
  · rw [lit2_1, gpD1, if_neg (by norm_num)]
    exact c1gs 2 (by norm_num)

theorem dg1 : ∀ l < 2, RepF 8330 (gD1 l) (gpD1 l) := by
  intro l hl
  interval_cases l
  · rw [gpD1, if_pos rfl, commutatorElement_def]
    have h := (c1g 1 (by norm_num)).comp ((c1g 2 (by norm_num)).comp
      ((repF_pi 66 (by norm_num)).comp (repF_pi 67 (by norm_num))))
    rw [← mul_assoc, ← mul_assoc] at h
    exact h
  · rw [gpD1, if_neg (by norm_num)]
    exact c1g 2 (by norm_num)

theorem dg1_inP : ∀ l < 2, gpD1 l ∈ heP := by
  intro l hl
  have h1 := c1g_inP 1 (by norm_num)
  have h2 := c1g_inP 2 (by norm_num)
  interval_cases l
  · rw [gpD1, if_pos rfl, commutatorElement_def]
    exact heP.mul_mem (heP.mul_mem (heP.mul_mem h1 h2) (heP.inv_mem h1)) (heP.inv_mem h2)
  · rw [gpD1, if_neg (by norm_num)]
    exact h2

theorem dtree1 : TreeOK 2 168 D1.P D1.L := treeOK_of fun i hi h0 => by
  have h := allN_spec kDTree1 i hi
  rwa [beq_zero_false h0] at h

theorem dedges1 : ∀ i < 168, ∀ k < 2, DE1 i k < 168 ∧
    treeArr 8330 heSevenDGens1 D1.P D1.L (DE1 i k) =
      compA 8330 heSevenDGens1[k]! (treeArr 8330 heSevenDGens1 D1.P D1.L i) :=
  edges_of_edgeAtK dtree1 dg1 dgs1 hmulP dg1_inP (fun k hk => iff_of_true (dg1_inP k hk) rfl)
    (fun _ _ => by decide) bs_lt pfaith1 fun i hi => allN_spec kDEdge1 i hi

theorem dkeys1_inj : ∀ a < 168, ∀ b < 168,
    keyA 8330 heSevenKeys (treeArr 8330 heSevenDGens1 D1.P D1.L a) =
      keyA 8330 heSevenKeys (treeArr 8330 heSevenDGens1 D1.P D1.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := dkey1) fun j hj => allN_spec kDSort1 j hj
  intro a ha b hb e
  rw [keyA_treeArr dtree1 dg1 dgs1 keys_lt ha, keyA_treeArr dtree1 dg1 dgs1 keys_lt hb] at e
  exact hk a ha b hb e

theorem d1_pts : heSevenDCert1.pts =
    Array.ofFn (n := 168) fun i => treeArr 8330 heSevenDGens1 D1.P D1.L i.val :=
  enumBfs_tree dtree1 dgs1 (by rfl) (by norm_num) (by norm_num) dkeys1_inj dedges1 kDReplay1

theorem d1_enum : enumOK 8330 heSevenDGens1 heSevenKeys heSevenDCert1 = true :=
  enumOK_tree dtree1 dgs1 (by rfl) (by norm_num) (by norm_num) dkeys1_inj dedges1

theorem d1_size : heSevenDCert1.pts.size = 168 := by rw [d1_pts, Array.size_ofFn]

theorem d1_get {k : Nat} (hk : k < 168) :
    heSevenDCert1.pts[k]! = treeArr 8330 heSevenDGens1 D1.P D1.L k := by
  rw [d1_pts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

@[expose] noncomputable def dT (k : Nat) : Equiv.Perm (Fin 8330) := treePerm gpD1 D1.P D1.L k

theorem d1_rep {k : Nat} (hk : k < 168) : Rep 8330 heSevenDCert1.pts[k]! (dT k) := by
  rw [d1_get hk]
  exact rep_treeArr dtree1 dgs1 k hk

theorem d1_repF {k : Nat} (hk : k < 168) : RepF 8330 (dv1 k) (dT k) :=
  repF_trV dtree1 dg1 168 k hk.le hk

theorem d1_inP {k : Nat} (hk : k < 168) : dT k ∈ heP :=
  (trQ_spec dtree1 hmulP dg1_inP (fun k hk => iff_of_true (dg1_inP k hk) rfl)
    (fun _ _ => by decide) 168 k hk.le hk).1

theorem d1_valid {k : Nat} (hk : k < 168) : validA 8330 heSevenDCert1.pts[k]! = true :=
  F2.validA_of_rep (d1_rep hk)

theorem d1_psize {k : Nat} (hk : k < 168) : heSevenDCert1.pts[k]!.size = 8330 := by
  rw [d1_get hk]
  exact size_treeArr k

theorem dT_inj {a b : Nat} (ha : a < 168) (hb : b < 168) (h : dT a = dT b) : a = b := by
  have hb' : Rep 8330 (treeArr 8330 heSevenDGens1 D1.P D1.L b) (dT a) := by
    rw [h]
    exact rep_treeArr dtree1 dgs1 b hb
  have e := arr_eq_of_rep (size_treeArr a) (size_treeArr b) (rep_treeArr dtree1 dgs1 a ha) hb'
  exact dkeys1_inj a ha b hb (by rw [e])

theorem mt_spec {a b : Nat} (ha : a < 168) (hb : b < 168) :
    mt1 a b < 168 ∧ dT (mt1 a b) = dT a * dT b := by
  have h := MTC1.all a ha
  unfold mtB at h
  have h' := allN_spec h b hb
  rw [bAnd_iff, Nat.blt_eq] at h'
  exact ⟨h'.1, eq_of_P (d1_repF h'.1) ((d1_repF ha).comp (d1_repF hb)) (d1_inP h'.1)
    (heP.mul_mem (d1_inP ha) (d1_inP hb)) h'.2⟩

theorem iv_spec {a : Nat} (ha : a < 168) : iv1 a < 168 ∧ dT (iv1 a) = (dT a)⁻¹ := by
  have h := allN_spec kIV1 a ha
  rw [bAnd_iff, Nat.blt_eq] at h
  refine ⟨h.1, eq_inv_of_mul_eq_one_left ?_⟩
  exact eq_of_P ((d1_repF h.1).comp (d1_repF ha)) RepF.one
    (heP.mul_mem (d1_inP h.1) (d1_inP ha)) heP.one_mem h.2

theorem cj_spec {j r : Nat} (hj : j < 168) (hr : r < 168) :
    cj1 j r < 168 ∧ dT (cj1 j r) = dT j * dT r * (dT j)⁻¹ := by
  obtain ⟨h1, e1⟩ := mt_spec hj hr
  obtain ⟨h2, e2⟩ := iv_spec hj
  obtain ⟨h3, e3⟩ := mt_spec h1 h2
  exact ⟨h3, by rw [cj1, e3, e1, e2]⟩

theorem eqA_d {k m : Nat} (hk : k < 168) (hm : m < 168) {t : Array Nat}
    {X : Equiv.Perm (Fin 8330)} (ht : Rep 8330 t X) (hX : X = dT m) :
    eqA 8330 heSevenDCert1.pts[k]! t = (k == m) := by
  rw [Bool.eq_iff_iff, eqA_iff (d1_rep hk) ht, hX, beq_iff_eq]
  exact ⟨dT_inj hk hm, fun e => by rw [e]⟩

theorem conj_rep {j r : Nat} (hj : j < 168) (hr : r < 168) :
    Rep 8330 (conjA 8330 heSevenDCert1.pts[j]! heSevenDCert1.pts[r]!) (dT j * dT r * (dT j)⁻¹) := by
  have h := rep_conjA (d1_valid hj) (d1_rep hr)
  rwa [CFSG.RankThree.Native.permOfArr_eq_of_rep (d1_rep hj)] at h

theorem classReps1 : classReps 8330 heSevenDCert1 = RP1 := by
  rw [classReps_eq (n := 8330) d1_size (id0 := 0) (cj := cj1)
    (fun k hk => eqA_d hk (by norm_num) rep_idA (by rw [dT, treePerm_zero]))
    (fun k hk j hj r hr => eqA_d hk (cj_spec hj hr).1 (conj_rep hj hr) (cj_spec hj hr).2.symm)]
  exact eq_of_beq kRP1

theorem rp_lt : ∀ r ∈ RP1, r < 168 := by
  have h := kCover1
  rw [bAnd_iff, List.all_eq_true] at h
  exact fun r hr => Nat.blt_eq.mp (h.1 r hr)

theorem conjPoint1 {r : Nat} (hr : r ∈ RP1) :
    conjPointOK 8330 heSevenKeys heSevenDCert1 r
      (enumBfs 8330 (conjGens 8330 heSevenDCert1 r) heSevenKeys (heSevenDCert1.pts.size + 1)) =
      true := by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hr
  have hbt := allN_spec kBT1 t ht
  unfold btB at hbt
  rw [show RP1.getD t 0 = RP1[t] by simp [ht]] at hbt
  refine conjPointOK_of_table (N := 168) d1_size (fun i hi => d1_rep hi) (fun i hi => d1_psize hi)
    (by norm_num) (by rw [d1_get (k := 0) (by norm_num), treeArr_zero])
    (fun a ha b hb e => dkeys1_inj a ha b hb (by rwa [d1_get ha, d1_get hb] at e))
    (fun a ha b hb => mt_spec ha hb) (fun a ha => iv_spec ha) (rp_lt _ hr)
    (par := btP t) (lab := btL t) (dep := btD t) fun i hi => ?_
  have h := allN_spec hbt i hi
  by_cases hi0 : i = 0
  · exact Or.inl hi0
  · right
    rw [beq_zero_false (Nat.pos_of_ne_zero hi0)] at h
    simp only [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, Nat.eq_of_beq_eq_true h3, (Nat.eq_of_beq_eq_true h4).symm⟩

theorem conjSimple1 : conjSimpleRepsOK 8330 heSevenKeys heSevenDCert1 RP1 = true := by
  unfold conjSimpleRepsOK conjClassCoverOK
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨fun r hr => by rw [d1_size]; exact rp_lt r hr, ?_⟩, fun r hr => conjPoint1 hr⟩
  rw [allLt_iff]
  intro k hk
  rw [d1_size] at hk
  have h := kCover1
  rw [bAnd_iff] at h
  have hc := allN_spec h.2 k hk
  have e : (RP1.any fun r => (List.range 168).any fun j =>
      eqA 8330 heSevenDCert1.pts[k]! (conjA 8330 heSevenDCert1.pts[j]! heSevenDCert1.pts[r]!)) =
      (RP1.any fun r => (List.range 168).any fun j => k == cj1 j r) :=
    any_congr_mem _ _ _ fun r hr => any_congr_mem _ _ _ fun j hj =>
      eqA_d hk (cj_spec (List.mem_range.1 hj) (rp_lt r hr)).1
        (conj_rep (List.mem_range.1 hj) (rp_lt r hr))
        (cj_spec (List.mem_range.1 hj) (rp_lt r hr)).2.symm
  rw [eqA_d (m := 0) hk (by norm_num) rep_idA (by rw [dT, treePerm_zero]), d1_size, e]
  exact hc

theorem x1_rep : Rep 8330 heSevenLines[1]! (lp 1) := rep_line 1 (by norm_num)

theorem x1_repF : RepF 8330 x1 (lp 1) := repF_ln 1 (by norm_num)

theorem x1_inP : lp 1 ∈ heP := lp_inP 1 (by norm_num)

theorem lp1_eq : lp 1 = gp 65 := by
  rw [lp, gp_one 1 (by norm_num), one_mul, inv_one, mul_one]
  rfl

theorem wit_eq (i : Nat) (hi : i < 2) : heSevenDWit1[i]! = unpack 8330 14 (A (68 + i)) := by
  rw [heSevenDWit1]
  interval_cases i
  · exact (lit2_0 _ _).trans (arr_eq 68 (by norm_num))
  · exact (lit2_1 _ _).trans (arr_eq 69 (by norm_num))

theorem wit_rep (i : Nat) (hi : i < 2) : Rep 8330 heSevenDWit1[i]! (gp (68 + i)) := by
  rw [wit_eq i hi]
  exact rep_gp _ (by omega)

theorem wit_inP (i : Nat) (hi : i < 2) : gp (68 + i) ∈ heP := by
  have h := fl_c1
  interval_cases i
  · exact (gp_mem 68 (by norm_num)).2.2 h.2.2.2.1
  · exact (gp_mem 69 (by norm_num)).2.2 h.2.2.2.2

theorem wit_mem (i : Nat) (hi : i < 2) : heSevenC1Cert.pts.toList.any (eqA 8330 heSevenDWit1[i]!) =
    true := by
  have h := allN_spec kCD1 i hi
  rw [bAnd_iff, Nat.blt_eq] at h
  exact any_mem (by rw [c1_size]; exact h.1) (eqA_P (wit_rep i hi) (c1_rep h.1)
    (repF_pa (68 + i) (by omega)) (c1_repF h.1) (wit_inP i hi) (c1_inP h.1) (eqOnL_symm h.2))

theorem base1_lt : ∀ t < 10, heSevenCase1BaseArr[t]! < 8330 := by decide

theorem rels_ok1 : relsOKP 7 8330 heSevenCase1BaseArr heSevenLines[1]! heSevenCase1Rels = true := by
  rw [relsOKP, List.all_eq_true]
  intro r hr
  have h := List.all_eq_true.1 kRels1 r hr
  unfold relAt1 at h
  simp only [bAnd_iff, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs : heSevenCase1BaseArr.size = 10 := by decide
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hs]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  rw [(rep_powArr x1_rep r.2.2).apply (base1_lt _ h2),
    ← (RepF.powF x1_repF r.2.2) _ (base1_lt _ h2)]
  exact Nat.eq_of_beq_eq_true h4

theorem tabs1 : TabsT 8330 14 11 10 S71.BP T71.NR T71.NR S71.S S71.SI S71.LR T71.Ts T71.LT T71.PT
    T71.QT 179 1024 9 1024 :=
  ⟨by decide, by decide, by decide, by decide, TS1.all, LT1.all, pt1B_all, qt1B_all⟩

theorem tc1 : TabChain 8330 14 11 10 S71.BP 131 64 T71.NR T71.NR 179 1024 9 1024 S71.S S71.SI
    S71.LR T71.Ts T71.LT T71.PT T71.QT heSevenCase1Arrs heSevenCase1BaseArr
    (heSevenCase1Base.map Fin.val) :=
  ⟨binds1, k1Perm, S71.ho, by norm_num, tabs1, rfl⟩

theorem fr_ok1 : ∀ i < 10, fr1 i = 0 ∨ ∃ l e, fr1 i = 8 * l + e + 1 ∧ l < i ∧ e < 8 ∧
    (l, i, e) ∈ heSevenCase1Rels := by
  intro i hi
  have h := allN_spec kFR1 i hi
  by_cases h0 : fr1 i = 0
  · exact Or.inl h0
  · right
    rw [show Nat.beq (fr1 i) 0 = false from
      Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)] at h
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

theorem csk1_lt : ∀ j < 1176, C1.SK j < 1176 := sk_lt fun j hj => by
  have h := allN_spec kCSort1 j hj
  unfold sortAtK at h
  rw [bAnd_iff, bAnd_iff, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1⟩

theorem tail1 : ptailOK 8330 (rawLevels 8330 heSevenCase1Arrs heSevenCase1BaseArr)
    heSevenCase1BaseArr heSevenLines[1]! (powPA 7 8330 heSevenLines[1]!) heSevenCase1Rels
    heSevenC1Cert.pts.toList 10 0 (idA 8330) = true := by
  refine ptailOK_of_ptK_ tc1 x1_rep x1_repF (fun r hr => ?_) fr_ok1 bs_lt ?_ (by norm_num) kTail1
  · have h := List.all_eq_true.1 kRels1 r hr
    unfold relAt1 at h
    rw [bAnd_iff, Nat.blt_eq] at h
    exact h.1
  · intro a A ha hA ⟨j, hj, e⟩
    have hR : A ∈ heAutGroup := by
      refine (Subgroup.closure_le _).2 ?_ hA
      rintro _ ⟨i, rfl⟩
      exact faith1 i (by simpa [heSevenCase1Arrs] using i.2)
    have hm := csk1_lt j hj
    unfold ckey1 cv1 at e
    rw [← keyA_treeArr ctree1 c1g c1gs keys_lt hm, ← c1_get hm] at e
    have he := key_faith ha (c1_rep hm) hR (heP_le_heAutGroup (c1_inP hm)) e
    exact any_mem (by rw [c1_size]; exact hm) ((eqA_iff ha (c1_rep hm)).2 he)

theorem cent1 : centOKP 7 8330 heSevenCase1Arrs heSevenCase1BaseArr heSevenLines[1]!
    heSevenCase1Rels heSevenC1Gens heSevenKeys heSevenC1Cert 1176 = true := by
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  have hs : heSevenCase1BaseArr.size = 10 := by decide
  refine ⟨⟨⟨⟨⟨rels_ok1, c1_enum⟩, c1_size⟩, fun k hk => ?_⟩, fun k hk => ?_⟩,
    by rw [hs]; exact tail1⟩
  · have hk3 : k < 3 := hk
    exact commA_R (c1gs k hk3) x1_rep (c1g k hk3) x1_repF (heP_le_heAutGroup (c1g_inP k hk3))
      (heP_le_heAutGroup x1_inP) (allN_spec kComm1 k hk3)
  · have hk3 : k < 3 := hk
    exact (sift1_iff (c1gs k hk3)).2 (heP_le_heAutGroup (c1g_inP k hk3))

theorem derived1 : derivedOKQ 7 168 8330 heSevenC1Gens heSevenDGens1 heSevenKeys heSevenC1Cert
    heSevenDCert1 heSevenDWit1[0]! heSevenDWit1[1]! heSevenLines[1]! heLevels heBase.toArray =
    true := by
  simp only [derivedOKQ, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  have hgC : heSevenC1Gens.size = 3 := rfl
  have hgD : heSevenDGens1.size = 2 := rfl
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨d1_enum, d1_size⟩, F2.validA_of_rep (wit_rep 0 (by norm_num))⟩,
    F2.validA_of_rep (wit_rep 1 (by norm_num))⟩, wit_mem 0 (by norm_num)⟩,
    wit_mem 1 (by norm_num)⟩, ?_⟩, fun k hk l hl => ?_⟩, fun k hk l hl => ?_⟩, ?_⟩, ?_⟩,
    fun k hk => ?_⟩, fun l hl => ?_⟩
  ·
    have h := rep_commutatorA (F2.validA_of_rep (wit_rep 0 (by norm_num)))
      (F2.validA_of_rep (wit_rep 1 (by norm_num)))
    rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (wit_rep 0 (by norm_num)),
      CFSG.RankThree.Native.permOfArr_eq_of_rep (wit_rep 1 (by norm_num)),
      commutatorElement_def] at h
    have hf := (repF_pa 68 (by norm_num)).comp ((repF_pa 69 (by norm_num)).comp
      ((repF_pi 68 (by norm_num)).comp (repF_pi 69 (by norm_num))))
    rw [← mul_assoc, ← mul_assoc] at hf
    have h68 := wit_inP 0 (by norm_num)
    have h69 := wit_inP 1 (by norm_num)
    exact eqA_P (c1gs 2 (by norm_num)) h (c1g 2 (by norm_num)) hf (c1g_inP 2 (by norm_num))
      (heP.mul_mem (heP.mul_mem (heP.mul_mem h68 h69) (heP.inv_mem h68)) (heP.inv_mem h69)) kCom1
  ·
    rw [hgC] at hk
    rw [hgD] at hl
    have h := allN_spec kDK1 (2 * k + l) (by omega)
    rw [show Nat.div (2 * k + l) 2 = k by change (2 * k + l) / 2 = k; omega,
      show Nat.mod (2 * k + l) 2 = l by change (2 * k + l) % 2 = l; omega] at h
    rw [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine any_mem (by rw [d1_size]; exact h1) ?_
    have hc := rep_conjA (F2.validA_of_rep (c1gs k hk)) (dgs1 l hl)
    rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (c1gs k hk)] at hc
    have hcf : RepF 8330 (fun y => gC1 k (gD1 l (pi (Nat.add 65 k) y)))
        (gpC1 k * gpD1 l * (gpC1 k)⁻¹) := by
      have := (c1g k hk).comp ((dg1 l hl).comp (repF_pi (65 + k) (by omega)))
      rw [mul_assoc]
      exact this
    have hP : gpC1 k * gpD1 l * (gpC1 k)⁻¹ ∈ heP :=
      heP.mul_mem (heP.mul_mem (c1g_inP k hk) (dg1_inP l hl)) (heP.inv_mem (c1g_inP k hk))
    exact eqA_P hc (d1_rep h1) hcf (d1_repF h1) hP (d1_inP h1) (eqOnL_symm h2)
  ·
    rw [hgC] at hk hl
    have h := allN_spec kDC1 (3 * k + l) (by omega)
    rw [show Nat.div (3 * k + l) 3 = k by change (3 * k + l) / 3 = k; omega,
      show Nat.mod (3 * k + l) 3 = l by change (3 * k + l) % 3 = l; omega] at h
    rw [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine any_mem (by rw [d1_size]; exact h1) ?_
    have hc := rep_commutatorA (F2.validA_of_rep (c1gs k hk)) (F2.validA_of_rep (c1gs l hl))
    rw [CFSG.RankThree.Native.permOfArr_eq_of_rep (c1gs k hk),
      CFSG.RankThree.Native.permOfArr_eq_of_rep (c1gs l hl), commutatorElement_def] at hc
    have hcf : RepF 8330 (fun y => gC1 k (gC1 l (pi (Nat.add 65 k) (pi (Nat.add 65 l) y))))
        (gpC1 k * gpC1 l * (gpC1 k)⁻¹ * (gpC1 l)⁻¹) := by
      have := (c1g k hk).comp ((c1g l hl).comp ((repF_pi (65 + k) (by omega)).comp
        (repF_pi (65 + l) (by omega))))
      rw [← mul_assoc, ← mul_assoc] at this
      exact this
    have hk' := c1g_inP k hk
    have hl' := c1g_inP l hl
    have hP : gpC1 k * gpC1 l * (gpC1 k)⁻¹ * (gpC1 l)⁻¹ ∈ heP :=
      heP.mul_mem (heP.mul_mem (heP.mul_mem hk' hl') (heP.inv_mem hk')) (heP.inv_mem hl')
    exact eqA_P hc (d1_rep h1) hcf (d1_repF h1) hP (d1_inP h1) (eqOnL_symm h2)
  ·
    have h := kNC1
    rw [Bool.not_eq_true'] at h
    rw [Bool.not_eq_true']
    exact neA_P (rep_compA (dgs1 0 (by norm_num)) (dgs1 1 (by norm_num)))
      (rep_compA (dgs1 1 (by norm_num)) (dgs1 0 (by norm_num)))
      ((dg1 0 (by norm_num)).comp (dg1 1 (by norm_num)))
      ((dg1 1 (by norm_num)).comp (dg1 0 (by norm_num))) h
  · rw [classReps1]
    exact conjSimple1
  ·
    rw [c1_size] at hk
    have hz := allN_spec kZ1 k hk
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
      have hcomm := (allLt_iff.1 hall) _ (show ZW1.getD k 0 - 1 < heSevenDGens1.size from hl)
      have e := (eqA_iff (rep_compA (c1_rep hk) (dgs1 _ hl))
        (rep_compA (dgs1 _ hl) (c1_rep hk))).1 hcomm
      have := eqOnL_of_eq bs_lt ((c1_repF hk).comp (dg1 _ hl)) ((e ▸ (dg1 _ hl).comp (c1_repF hk)))
      rw [Bool.eq_false_iff] at h3
      exact h3 this
    · rw [show Nat.blt (ZW1.getD k 0) 100 = false from Bool.eq_false_iff.2 fun h =>
        hw (Nat.blt_eq.mp h)] at hz
      rw [bAnd_iff, Nat.blt_eq] at hz
      obtain ⟨h1, h3⟩ := hz
      right
      rw [List.any_eq_true]
      refine ⟨ZW1.getD k 0 - 100, List.mem_range.2 h1, ?_⟩
      exact eqA_P (c1_rep hk) (rep_powArr x1_rep _) (c1_repF hk) (RepF.powF x1_repF _)
        (c1_inP hk) (heP.pow_mem x1_inP _) h3
  · rw [hgD] at hl
    rw [show heLevels = rawLevels 8330 heStrongArrs heBase.toArray from rfl,
      mem_heP_iff_siftA (dgs1 l hl)]
    exact dg1_inP l hl

open Certificates in
open CFSG.RankThree.PartOne CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native in
theorem facts1 :
    caseChainOK3 8330 heSevenCase1Arrs heSevenCase1BaseArr heSevenCase1Words (heGen 0) (heGen 1)
        heUArr = true ∧
      centOKP 7 8330 heSevenCase1Arrs heSevenCase1BaseArr heSevenLines[1]! heSevenCase1Rels
        heSevenC1Gens heSevenKeys heSevenC1Cert 1176 = true ∧
      eqA 8330 heSevenC1Gens[0]! heSevenLines[1]! = true ∧
      derivedOKQ 7 168 8330 heSevenC1Gens heSevenDGens1 heSevenKeys heSevenC1Cert heSevenDCert1
        heSevenDWit1[0]! heSevenDWit1[1]! heSevenLines[1]! heLevels heBase.toArray = true := by
  refine ⟨chain1, cent1, ?_, derived1⟩
  refine (eqA_iff (c1gs 0 (by norm_num)) x1_rep).2 ?_
  rw [lp1_eq]
  rfl

end CertificateChecks.KernelHeLoc.Seven

end
