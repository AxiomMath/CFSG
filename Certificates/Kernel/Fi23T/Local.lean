module

public import Certificates.Kernel.Fi23T.Far
public import Certificates.Kernel.Fi23T.Misc

public section

set_option maxRecDepth 400000

open Pointwise

namespace CertificateChecks.KernelFi23T

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23T CFSG.KC.Fi23C CFSG.KD.Fi23K CFSG.KD.Fi23T
  CFSG.KS.Fi23Tr CertificateChecks.KernelFi23M CFSG.KS.PC CFSG.KS.Raw.Orb
open CertificateChecks.KernelFi23C (rep_alpha rep_beta)
open CFSG.Sporadic.Fi23.Native (trData cData tauAct dTable genTables PBits pBit pOf pZero pImg TrOrb
  trBFS trAct trD trBi trIncOK trMemOK trStarOK trGensOK trCommOK trDomOK trCsOK trOrbitOK
  trLetters cGens rRoot failC commTreeP domWit ncWit pMaps trFind pKey starPts starPhiPos inTreeB
  treeActTab)
open CFSG.Sporadic.Th.Native (ap Table none32 allIn parAll)
open CFSG.Sporadic.Th (Rep idx_of_lt allIn_eq_true ap_ofFn parAll_eq_true_of)
open CFSG.Perm.Native (treeBFS treeOK)

theorem cGens_eq : cGens = #[1, 32, 37, 39, 49, 52, 53, 59, 64] := rfl

theorem cGens_size : cGens.size = 9 := rfl

theorem cGens_mem : ∀ l < 9, cGens[l]! ∈ cgL := by decide

theorem cgL_lt : ∀ x ∈ cgL, x < 31671 := by decide

theorem lv9 : ∀ l ∈ Array.range cGens.size, l < 9 := fun l hl => by
  rw [Array.mem_range, cGens_size] at hl
  exact hl

theorem contains_hList {Hh : ℕ → ℕ} {rl rp c bd : ℕ} (h : listK Hh rl rp c bd = true) {u : ℕ}
    (hu : u < bd) : (hList Hh rl 0 c).toArray.contains u = true ↔ tb Hh rp u < c := by
  rw [Array.contains_iff_mem, mem_hList_arr]
  obtain ⟨h1, -, h3⟩ := listK_spec h
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [(h1 l hl).2]
    exact hl
  · intro hc
    rcases h3 u hu with e | e
    · exact ⟨_, hc, e.2⟩
    · omega

theorem inc_of {Hh : ℕ → ℕ} {rl rp c : ℕ} (h : listK Hh rl rp c 31671 = true) (hc : 0 < c) :
    trIncOK (hList Hh rl 0 c).toArray c = true := by
  obtain ⟨h1, h2, -⟩ := listK_spec h
  unfold trIncOK
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, hList_size,
    hList_get _ _ _ (by omega)]
  refine ⟨⟨rfl, allIn_eq_true.2 fun k _ hk => ?_⟩, (h1 _ (by omega)).1⟩
  rw [decide_eq_true_eq, hList_get _ _ _ (by omega), hList_get _ _ _ (by omega)]
  exact h2 k (by omega)

theorem mem_of {xs : Array ℕ} (hxs : ∀ x ∈ xs, x < 31671) : trMemOK (pOf (pZero ()) xs) xs = true := by
  unfold trMemOK
  refine allIn_eq_true.2 fun x _ _ => ?_
  rw [beq_iff_eq, pBit_pOf0 hxs]

section


theorem inc_c : trIncOK (cData ()) 1080 = true := by
  rw [cData_eq]
  exact inc_of o_list (by norm_num)

theorem inc_t : trIncOK (trData ()) 3240 = true := by
  rw [trData_eq]
  exact inc_of t_list (by norm_num)

theorem mem_c : trMemOK (pOf (pZero ()) (cData ())) (cData ()) = true := mem_of cData_lt

theorem mem_t : trMemOK (pOf (pZero ()) (trData ())) (trData ()) = true := mem_of trData_lt

theorem cJ_val {k x : ℕ} (hk : k < 31671) (hx : x < 31671) : cJ G k x = (tau (fp k) (fp x)).val := by
  rw [← cJ_tau hk hx, fp_val (CertificateChecks.KernelFi23C.cJ_lt hk hx)]

theorem tauAct_cJ {k x : ℕ} (hk : k < 31671) (hx : x < 31671) :
    tauAct orbLit (dTable orbLit) (genTables orbLit (-2)) k x = cJ G k x := by
  rw [tauAct_eq hk hx, cJ_val hk hx]

theorem cB_false {y : ℕ} (hy : y < 31671) :
    pBit (pOf (pZero ()) (cData ())) y = false ↔ fp y ∉ O0 := by
  rw [← Bool.not_eq_true, cB_iff hy]

theorem O0_T0 {x : Fin 31671} (hx : x ∈ O0) : x ∈ T0 := by
  have h := allN_iff.1 o_sub (tb H 3 x.val) (mem_O0.1 hx)
  rw [← O0_idx hx, ← domT_iff (o_spec.1 _ (mem_O0.1 hx)).1]
  exact h

theorem cg_O0 {x : ℕ} (hx : x ∈ cgL) : fp x ∈ O0 := by
  obtain ⟨l, hl, rfl⟩ := mem_reg cg_eq hx
  have h := allN_iff.1 cg_in l hl
  exact (memS_O0 (cgL_lt _ (reg_mem cg_eq hl))).1 h

theorem cg_pres {x : ℕ} (hx : x ∈ cgL) : presK G H 2 1080 [x] = true := by
  simp only [cgL, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact o_1
  · exact o_32
  · exact o_37
  · exact o_39
  · exact o_49
  · exact o_52
  · exact o_53
  · exact o_59
  · exact o_64

theorem tau_O0 {x : ℕ} (hx : x ∈ cgL) : tau (fp x) • O0 = O0 := by
  have h := presO (ltr_of (w := [x]) (fun p hp => by
    rw [List.mem_singleton] at hp
    rw [hp]
    exact cgL_lt x hx)) (cg_pres hx)
  rwa [wP_cons, wP_nil, mul_one, lP_pt (cgL_lt x hx)] at h

theorem tau_O0_iff {x : ℕ} (hx : x ∈ cgL) (y : Fin 31671) : tau (fp x) y ∈ O0 ↔ y ∈ O0 := by
  rw [← Equiv.Perm.smul_def]
  conv_lhs => rw [← tau_O0 hx]
  exact Finset.smul_mem_smul_finset_iff _

theorem star_ok' : trStarOK orbLit (dTable orbLit) (genTables orbLit (-2))
    (starPts (dTable orbLit)) (starPhiPos ()) (pOf (pZero ()) (cData ())) = true := by
  unfold trStarOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨by decide, by decide⟩, ?_⟩, allIn_eq_true.2 fun u _ hu => ?_⟩
  · rw [CertificateChecks.KernelFi23C.dTable_star _ (by decide)]
    have h := fc_moved
    rw [Bool.not_eq_true'] at h
    exact Nat.ne_of_beq_eq_false h
  · have hp := CertificateChecks.KernelFi23C.phi_facts hu
    rw [CertificateChecks.KernelFi23C.starPhiPos_get hu,
      CertificateChecks.KernelFi23C.starPts_get CertificateChecks.KernelFi23C.dTable_star hp.2.1]
    have hx := CertificateChecks.KernelFi23C.E_lt hp.2.1
    obtain ⟨s1, s2⟩ := starK_spec star_ok hu
    have hfc : failC () = 11504 := rfl
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, hfc, tauAct_cJ (by norm_num) hx, lh_lit]
    have e0 : (#[(hList H 4 0 351).toArray, (hList H 6 0 351).toArray] : Array (Array ℕ))[0]! =
      (hList H 4 0 351).toArray := rfl
    have e1 : (#[(hList H 4 0 351).toArray, (hList H 6 0 351).toArray] : Array (Array ℕ))[1]! =
      (hList H 6 0 351).toArray := rfl
    rw [e0, e1]
    refine ⟨Bool.eq_iff_iff.2 ?_, Bool.eq_iff_iff.2 ?_⟩
    · rw [cB_iff hx, contains_hList l0_list hu, mem_O0, fp_val hx]
      exact s1.symm
    · rw [contains_hList l1_list hu, beq_iff_eq]
      exact s2.symm

theorem letters_get {l : ℕ} (hl : l < 9) :
    (trLetters orbLit (dTable orbLit) (genTables orbLit (-2)))[l]! =
      treeActTab orbLit (dTable orbLit) (genTables orbLit (-2)) cGens[l]! := by
  unfold trLetters
  exact map_get _ _ (by rw [cGens_size]; exact hl)

theorem ap_letters {l x : ℕ} (hl : l < 9) (hx : x < 31671) :
    ap (trLetters orbLit (dTable orbLit) (genTables orbLit (-2)))[l]! x = cJ G cGens[l]! x := by
  have hg := cgL_lt _ (cGens_mem l hl)
  rw [letters_get hl, ap_tab hg hx, cJ_val hg hx]

theorem letters_lt : ∀ l ∈ Array.range cGens.size, ∀ x < 31671,
    ap (trLetters orbLit (dTable orbLit) (genTables orbLit (-2)))[l]! x < 31671 := by
  intro l hl x hx
  rw [ap_letters (lv9 l hl) hx]
  exact CertificateChecks.KernelFi23C.cJ_lt (cgL_lt _ (cGens_mem _ (lv9 l hl))) hx

theorem lv9_32 : ∀ l ∈ Array.range cGens.size, l < 2 ^ 32 := fun l hl =>
  (lv9 l hl).trans (by norm_num)

theorem cg_reg {l : ℕ} (hl : l < 9) : tb H 41 l = cGens[l]! := by
  have e : cGens = (hList H 41 0 9).toArray := by rw [cg_lit]; rfl
  rw [e, hList_get _ _ _ hl]

theorem forest_reach {b : ℕ} {dom : ℕ → Bool} {s e : ℕ}
    (hN : ∀ j, s ≤ j → j < e → NodeOK b 41 9 dom s j) :
    ∀ j, s ≤ j → j < e → CFSG.KC.VecK.Reach (· ∈ Array.range cGens.size)
      (fun l x => ap (trLetters orbLit (dTable orbLit) (genTables orbLit (-2)))[l]! x)
      (tb H b s) (tb H b j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hs he
    by_cases hj : j = s
    · subst hj
      exact CFSG.KC.VecK.Reach.root
    · obtain ⟨-, -, -, -, hn⟩ := hN j hs he
      obtain ⟨h1, h2, h3, h4⟩ := hn hj
      have hr := ih _ h2 h1 (by omega)
      have hrlt := (hN _ h1 (by omega)).1
      have hlv : tb H (b + 2) j ∈ Array.range cGens.size := by
        rw [Array.mem_range, cGens_size]
        exact h3
      have h := CFSG.KC.VecK.Reach.step (f := fun l x =>
        ap (trLetters orbLit (dTable orbLit) (genTables orbLit (-2)))[l]! x) hr hlv
      beta_reduce at h
      rwa [ap_letters h3 hrlt, ← cg_reg h3, h4] at h

theorem gens_ok' : trGensOK (pOf (pZero ()) (cData ())) (pOf (pZero ()) (trData ()))
    (trLetters orbLit (dTable orbLit) (genTables orbLit (-2)))
    (treeBFS 31671 0 (trLetters orbLit (dTable orbLit) (genTables orbLit (-2)))
      (Array.range cGens.size))
    (treeBFS 31671 (rRoot ()) (trLetters orbLit (dTable orbLit) (genTables orbLit (-2)))
      (Array.range cGens.size)) = true := by
  unfold trGensOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  have hB0 := CFSG.KC.VecK.treeBFS_spec (n := 31671) (root := 0) (by norm_num) (by norm_num)
    lv9_32 letters_lt
  have hB1 := CFSG.KC.VecK.treeBFS_spec (n := 31671) (root := rRoot ()) (by norm_num)
    (by decide) lv9_32 letters_lt
  refine ⟨⟨⟨⟨by unfold trLetters; rw [Array.size_map], allIn_eq_true.2 fun l _ hl => ?_⟩, hB0.ok⟩,
    hB1.ok⟩, allIn_eq_true.2 fun x _ hx => ?_⟩
  · rw [cGens_size] at hl
    have hm := cGens_mem l hl
    have hg := cgL_lt _ hm
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, cB_iff hg]
    refine ⟨⟨hg, cg_O0 hm⟩, ?_⟩
    unfold pMaps
    refine allIn_eq_true.2 fun y _ hy => ?_
    rw [beq_iff_eq, letters_get hl, ap_tab hg hy]
    refine Bool.eq_iff_iff.2 ?_
    rw [cB_iff (Fin.isLt _), cB_iff hy, fp_of, tau_O0_iff hm]
  · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    have hO : pBit (pOf (pZero ()) (cData ())) x = true → fp x ∈ T0 := fun h =>
      O0_T0 ((cB_iff hx).1 h)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_cases h : pBit (pOf (pZero ()) (cData ())) x = true
      · refine Or.inr (inTreeB_of_reach (by norm_num) (by norm_num) lv9_32 letters_lt ?_)
        have hd : domO H x = true := (memS_O0 hx).2 ((cB_iff hx).1 h)
        obtain ⟨h1, h2⟩ := covK_spec f_cov hx hd
        have hr := forest_reach (nodes_of f_tree) _ (Nat.zero_le _) h1
        rwa [root_eq root_28_0, h2] at hr
      · exact Or.inl (Bool.eq_false_iff.2 h)
    · by_cases h : pBit (pOf (pZero ()) (trData ())) x = true
      · by_cases hc : pBit (pOf (pZero ()) (cData ())) x = true
        · exact Or.inl (Or.inr hc)
        refine Or.inr (inTreeB_of_reach (by norm_num) (by decide) lv9_32 letters_lt ?_)
        have hd : domR H x = true := by
          unfold domR
          rw [bAnd_eq, Bool.and_eq_true, Bool.not_eq_true', memS_T0 hx, ← tB_iff hx, h,
            ← Bool.not_eq_true, memS_O0 hx, ← cB_iff hx]
          exact ⟨rfl, hc⟩
        obtain ⟨h1, h2⟩ := covK_spec g_cov hx hd
        have hr := forest_reach (nodes_of g_tree) _ (Nat.zero_le _) h1
        rwa [root_eq root_32_0, h2] at hr
      · exact Or.inl (Or.inl (Bool.eq_false_iff.2 h))
    · by_cases h : pBit (pOf (pZero ()) (cData ())) x = true
      · exact Or.inr ((tB_iff hx).2 (hO h))
      · exact Or.inl (Bool.eq_false_iff.2 h)

theorem tb2_mono : ∀ i < 1080, tb H 2 0 ≤ tb H 2 i := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ i ih =>
    intro hi
    exact (ih (by omega)).trans (o_spec.2.1 i hi).le

theorem cData0 : tb H 2 0 = 0 := by
  have hd := dom_ok
  simp only [bAnd_eq, Bool.and_eq_true] at hd
  have h0 : fp 0 ∈ O0 := (memS_O0 (by norm_num)).1 hd.2.2.2.2.1
  have e := O0_idx h0
  rw [fp_val (by norm_num)] at e
  have hlt := mem_O0.1 h0
  rw [fp_val (by norm_num)] at hlt
  have h1 := tb2_mono _ hlt
  have e' : tb H 2 (tb H 3 0) = 0 := by
    have := congrArg Fin.val e
    rwa [fp_val (o_spec.1 _ hlt).1] at this
  omega

theorem cData_get0 : (cData ())[0]! = 0 := by
  rw [cData_eq, hList_get _ _ _ (by norm_num), cData0]

noncomputable abbrev CT : Array ℕ × Array ℕ :=
  commTreeP orbLit (dTable orbLit) (genTables orbLit (-2)) (pZero ()) (cData ())

theorem ct_facts : CT.2.size = CT.1.size ∧ 0 < CT.1.size ∧ CT.1[0]! = (cData ())[0]! ∧
    (∀ k < CT.1.size, CT.1[k]! ∈ cData ()) ∧
    (∀ i < CT.1.size, ∀ j < CT.1.size, CT.1[i]! = CT.1[j]! → i = j) ∧
    (∀ k, 0 < k → k < CT.1.size → CT.2[k]! < k ∧
      tauAct orbLit (dTable orbLit) (genTables orbLit (-2)) CT.1[CT.2[k]!]! CT.1[k]! = CT.1[k]!) ∧
    ∀ k < CT.1.size, ∀ y ∈ cData (),
      tauAct orbLit (dTable orbLit) (genTables orbLit (-2)) CT.1[k]! y = y →
        ∃ j < CT.1.size, CT.1[j]! = y :=
  commTreeP_spec orbLit (dTable orbLit) (genTables orbLit (-2)) size_pZero pBit_pZero
    (by rw [cData_eq, hList_size]; norm_num) cData_lt

theorem tb36_ct : ∀ j < 1080, ∃ i < CT.1.size, CT.1[i]! = tb H 36 j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    obtain ⟨h1, h2, -, h4, h5⟩ := ctK_spec h_tree (Nat.zero_le j) (by omega : j < 0 + 1080)
    by_cases h0 : j = 0
    · subst h0
      refine ⟨0, ct_facts.2.1, ?_⟩
      rw [ct_facts.2.2.1, cData_get0, root_eq root_36_0]
    · obtain ⟨hr, hc⟩ := h5 h0
      obtain ⟨i, hi, ei⟩ := ih _ hr (by omega)
      have hmem : tb H 36 j ∈ cData () := (cData_mem h1).2 (by rw [mem_O0, fp_val h1]; exact h2)
      have hilt : CT.1[i]! < 31671 := cData_lt _ (ct_facts.2.2.2.1 i hi)
      refine ct_facts.2.2.2.2.2.2 i hi _ hmem ?_
      rw [tauAct_cJ hilt h1, ei]
      exact hc

theorem cData_ct {x : ℕ} (hx : x ∈ cData ()) : ∃ i < CT.1.size, CT.1[i]! = x := by
  have hlt := cData_lt x hx
  have hd : domO H x = true := (memS_O0 hlt).2 ((cData_mem hlt).1 hx)
  obtain ⟨h1, h2⟩ := covK_spec h_cov hlt hd
  obtain ⟨i, hi, e⟩ := tb36_ct _ h1
  exact ⟨i, hi, by rw [e, h2]⟩

theorem ct_size : CT.1.size = 1080 := by
  have hA : ((Finset.range CT.1.size).image fun k => CT.1[k]!).card = CT.1.size := by
    rw [Finset.card_image_of_injOn (fun i hi j hj e => ct_facts.2.2.2.2.1 i
      (Finset.mem_range.1 (Finset.mem_coe.1 hi)) j (Finset.mem_range.1 (Finset.mem_coe.1 hj)) e),
      Finset.card_range]
  have hB : ((Finset.range 1080).image fun l => tb H 2 l).card = 1080 := by
    rw [Finset.card_image_of_injOn (fun i hi j hj e => by
      have := congrArg (tb H 3) e
      rwa [(o_spec.1 i (Finset.mem_range.1 (Finset.mem_coe.1 hi))).2,
        (o_spec.1 j (Finset.mem_range.1 (Finset.mem_coe.1 hj))).2] at this), Finset.card_range]
  have he : ((Finset.range CT.1.size).image fun k => CT.1[k]!) =
      (Finset.range 1080).image fun l => tb H 2 l := by
    ext y
    rw [Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have h := ct_facts.2.2.2.1 k (Finset.mem_range.1 hk)
      rw [cData_eq, mem_hList_arr] at h
      obtain ⟨l, hl, e⟩ := h
      exact ⟨l, Finset.mem_range.2 hl, e⟩
    · rintro ⟨l, hl, rfl⟩
      have h : tb H 2 l ∈ cData () := by
        rw [cData_eq, mem_hList_arr]
        exact ⟨l, Finset.mem_range.1 hl, rfl⟩
      obtain ⟨i, hi, e⟩ := cData_ct h
      exact ⟨i, Finset.mem_range.2 hi, e⟩
  rw [← hA, he, hB]

theorem cB_mem {x : ℕ} (hx : x ∈ cData ()) : pBit (pOf (pZero ()) (cData ())) x = true := by
  rw [pBit_pOf0 cData_lt, Array.contains_iff_mem]
  exact hx

theorem zero_O0 : fp 0 ∈ O0 := by
  have hd := dom_ok
  simp only [bAnd_eq, Bool.and_eq_true] at hd
  exact (memS_O0 (by norm_num)).1 hd.2.2.2.2.1

theorem comm_ok : trCommOK orbLit (dTable orbLit) (genTables orbLit (-2)) (pOf (pZero ()) (cData ()))
    CT.1 CT.2 = true := by
  unfold trCommOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨ct_size, ct_facts.1.trans ct_size⟩, by rw [ct_facts.2.2.1, cData_get0]⟩,
    (cB_iff (by norm_num)).2 zero_O0⟩, allIn_eq_true.2 fun k hk1 hk => ?_⟩,
    Array.all_eq_true'.2 fun x hx => ?_⟩
  · rw [← ct_size] at hk
    obtain ⟨p1, p2⟩ := ct_facts.2.2.2.2.2.1 k (by omega) hk
    have hm := ct_facts.2.2.2.1 k hk
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq, beq_iff_eq, bne_iff_ne]
    refine ⟨⟨⟨⟨p1, cData_lt _ hm⟩, cB_mem hm⟩, p2⟩, fun e => ?_⟩
    have := ct_facts.2.2.2.2.1 _ (by omega) k hk e
    omega
  · obtain ⟨i, hi, e⟩ := cData_ct hx
    rw [Array.contains_iff_mem, ← e, getElem!_pos CT.1 i hi]
    exact Array.getElem_mem hi

theorem orb_cg {f : Fin 31671} (hf : f ∉ T0) : f ∈ Orb tau (ptSet cgL) (fp 2) := by
  have hd := tc_iff.2 hf
  obtain ⟨h1, h2⟩ := covK_spec b_cov f.isLt hd
  have h := orb_node (gens_ok cg_eq cg_lt) nodesB h2 (Nat.zero_le _) h1
  rwa [root_eq root_12_0] at h

theorem cl_O0 {g : Equiv.Perm (Fin 31671)} (hg : g ∈ Subgroup.closure (tau '' ptSet cgL)) :
    g • O0 = O0 :=
  TSys.fix_closure (fun s hs => by
    rw [← fp_of s]
    exact tau_O0 hs) hg

theorem dom_wit {f : ℕ} (hf : f < 31671) (hT : fp f ∉ T0) :
    (∃ x ∈ cData (), tauAct orbLit (dTable orbLit) (genTables orbLit (-2)) x f = f) ∧
      ∃ x ∈ cData (), tauAct orbLit (dTable orbLit) (genTables orbLit (-2)) x f ≠ f := by
  obtain ⟨g, hg, hgf⟩ := orb_cg hT
  have hgA : g ∈ A0 := tsys.closure_le _ hg
  have hd := dom_ok
  simp only [bAnd_eq, Bool.and_eq_true] at hd
  obtain ⟨-, -, -, h37, -, h0⟩ := hd
  have e37 : tau (fp 37) (fp 2) = fp 2 := by
    rw [← cJ_tau (by norm_num) (by norm_num), Nat.eq_of_beq_eq_true h37]
  have n0 : tau (fp 0) (fp 2) ≠ fp 2 := by
    rw [← cJ_tau (by norm_num) (by norm_num)]
    intro e
    have := congrArg Fin.val e
    rw [fp_val (CertificateChecks.KernelFi23C.cJ_lt (by norm_num) (by norm_num)),
      fp_val (by norm_num)] at this
    rw [Bool.not_eq_true'] at h0
    exact Nat.ne_of_beq_eq_false h0 this
  have hO : ∀ y : Fin 31671, y ∈ O0 → (g y).val ∈ cData () := fun y hy => by
    rw [cData_mem (Fin.isLt _), fp_of, ← cl_O0 hg, ← Equiv.Perm.smul_def]
    exact Finset.smul_mem_smul_finset hy
  have hconj : ∀ y : Fin 31671, tau (g y) (fp f) = g (tau y (fp 2)) := fun y => by
    rw [tsys.conj g hgA, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hgf, perm_inv_apply]
  refine ⟨⟨(g (fp 37)).val, hO _ (cg_O0 (by decide)), ?_⟩, ⟨(g (fp 0)).val,
    hO _ zero_O0, ?_⟩⟩
  · rw [tauAct_eq (Fin.isLt _) hf, fp_of, hconj, e37, hgf, fp_val hf]
  · rw [tauAct_eq (Fin.isLt _) hf, fp_of, hconj]
    intro e
    apply n0
    apply g.injective
    apply Fin.ext
    rw [e, hgf, fp_val hf]

noncomputable abbrev DW : Array ℕ := Array.ofFn (n := 31671) fun f =>
  if pBit (pOf (pZero ()) (trData ())) f.val then 0
  else domWit orbLit (dTable orbLit) (genTables orbLit (-2)) (cData ()) f.val

noncomputable abbrev NW : Array ℕ := Array.ofFn (n := 31671) fun f =>
  if pBit (pOf (pZero ()) (trData ())) f.val then 0
  else ncWit orbLit (dTable orbLit) (genTables orbLit (-2)) (cData ()) f.val

theorem dom_ok' : trDomOK orbLit (dTable orbLit) (genTables orbLit (-2)) (pOf (pZero ()) (cData ()))
    (pOf (pZero ()) (trData ())) DW NW = true := by
  unfold trDomOK
  refine allIn_eq_true.2 fun f _ hf => ?_
  rw [Bool.or_eq_true]
  by_cases hb : pBit (pOf (pZero ()) (trData ())) f = true
  · exact Or.inl hb
  right
  have hT := (tB_false hf).1 (Bool.eq_false_iff.2 hb)
  obtain ⟨hd, hn⟩ := dom_wit hf hT
  obtain ⟨d1, d2⟩ := domWit_spec hd
  obtain ⟨n1, n2⟩ := ncWit_spec hn
  have eD : DW[f]! = domWit orbLit (dTable orbLit) (genTables orbLit (-2)) (cData ()) f := by
    rw [getElem!_pos _ f (by simpa using hf), Array.getElem_ofFn]
    dsimp only
    rw [if_neg hb]
  have eN : NW[f]! = ncWit orbLit (dTable orbLit) (genTables orbLit (-2)) (cData ()) f := by
    rw [getElem!_pos _ f (by simpa using hf), Array.getElem_ofFn]
    dsimp only
    rw [if_neg hb]
  rw [eD, eN]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq]
  have n1lt := cData_lt _ n1
  exact ⟨⟨⟨⟨⟨cData_lt _ d1, cB_mem d1⟩, d2⟩, n1lt⟩,
    (tB_iff n1lt).2 (O0_T0 ((cData_mem n1lt).1 n1))⟩, n2⟩

theorem cs_ok' : trCsOK orbLit (dTable orbLit) (genTables orbLit (-2)) (pOf (pZero ()) (cData ()))
    (pOf (pZero ()) (trData ())) = true := by
  have hc := cs_pts
  unfold domR at hc
  simp only [bAnd_eq, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hc
  have hw := presO (w := [92, 71]) (ltr_of (by decide)) cs_ok
  rw [wP_cons, wP_cons, wP_nil, mul_one, lP_pt (by norm_num), lP_pt (by norm_num), mul_smul] at hw
  have h7192 : tau (fp 71) • O0 = tau (fp 92) • O0 := by
    rw [← tsys.τ_τ (fp 92) (tau (fp 71) • O0), hw]
  have nO : ∀ y, y < 31671 → memS H 2 1080 y = false → pBit (pOf (pZero ()) (cData ())) y = false :=
    fun y hy h => (cB_false hy).2 fun hm => by
      rw [← memS_O0 hy, h] at hm
      exact Bool.false_ne_true hm
  have e71 : CFSG.Sporadic.Fi23.Native.csV () = 71 := rfl
  have e92 : CFSG.Sporadic.Fi23.Native.csW () = 92 := rfl
  unfold trCsOK
  rw [e71, e92]
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨by decide, by norm_num⟩, by norm_num⟩, (tB_iff (by norm_num)).2
    ((memS_T0 (by norm_num)).1 a1)⟩, nO 71 (by norm_num) a2⟩, (tB_iff (by norm_num)).2
    ((memS_T0 (by norm_num)).1 b1)⟩, nO 92 (by norm_num) b2⟩, allIn_eq_true.2 fun y _ hy => ?_⟩
  rw [beq_iff_eq, tauAct_eq (by norm_num) hy, tauAct_eq (by norm_num) hy]
  refine Bool.eq_iff_iff.2 ?_
  rw [cB_iff (Fin.isLt _), cB_iff (Fin.isLt _), fp_of, fp_of, ← mem_tau, ← mem_tau, h7192]

theorem maps_of {T : Table} {g : Equiv.Perm (Fin 31671)} (hT : Rep 31671 T g) {k j : ℕ}
    (h : vS j = g • vS k) : pMaps T orb.sets[k]! orb.sets[j]! = true := by
  unfold pMaps
  refine allIn_eq_true.2 fun x _ hx => ?_
  have hTx : ap T x = (g (fp x)).val := by
    rw [hT x hx, idx_of_lt _ hx, fp_eq hx]
    rfl
  rw [beq_iff_eq, hTx]
  refine Bool.eq_iff_iff.2 ?_
  rw [mem_vS (Fin.isLt _), mem_vS hx, fp_of, h, ← Equiv.Perm.smul_def,
    Finset.smul_mem_smul_finset_iff]

theorem orbit_ok : trOrbitOK orbLit.alpha orbLit.beta (pZero ()) (pOf (pZero ()) (trData ())) orb 3 =
    true := by
  unfold trOrbitOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  obtain ⟨c1, c2, c3⟩ := closed
  refine ⟨⟨⟨⟨⟨⟨⟨⟨size_eq, c1.trans size_eq⟩, c2.trans size_eq⟩, orb_facts.2.2.1.trans size_eq⟩,
    orb_facts.2.2.2.1.trans size_eq⟩, allIn_eq_true.2 fun x _ _ => by rw [beq_iff_eq, orb_facts.2.1]⟩,
    parAll_eq_true_of fun k hk => ?_⟩, allIn_eq_true.2 fun k hk1 hk => ?_⟩,
    parAll_eq_true_of fun k hk => ?_⟩
  · have hk' : k < orb.sets.size := by rw [size_eq]; exact hk
    obtain ⟨h1, h2⟩ := pa_vS k hk'
    obtain ⟨h3, h4⟩ := pb_vS k hk'
    rw [size_eq] at h1 h3
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨⟨⟨h1, h3⟩, maps_of rep_alpha h2⟩, maps_of rep_beta h4⟩
  · have hk' : k < orb.sets.size := by rw [size_eq]; exact hk
    obtain ⟨hp, hl⟩ := orb_facts.2.2.2.2.2.2.2.1 k (by omega) hk'
    have hpk : ap orb.par k < orb.sets.size := by omega
    rw [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      beq_iff_eq, beq_iff_eq, beq_iff_eq, beq_iff_eq]
    refine ⟨hp, ?_⟩
    rcases hl with ⟨l1, e⟩ | ⟨l2, e⟩
    · obtain ⟨a1, a2, -⟩ := c3 _ hpk
      exact Or.inl ⟨l1, orb_facts.2.2.2.2.1 _ a1 _ hk' (a2.symm.trans e.symm)⟩
    · obtain ⟨-, -, b1, b2⟩ := c3 _ hpk
      exact Or.inr ⟨l2, orb_facts.2.2.2.2.1 _ b1 _ hk' (b2.symm.trans e.symm)⟩
  · have hk' : k < orb.sets.size := by rw [size_eq]; exact hk
    rw [beq_iff_eq]
    unfold trFind
    rw [pKey_canon (canon_vS hk), orb_facts.2.2.2.2.2.1 k hk']
    rfl

end

end CertificateChecks.KernelFi23T

end
