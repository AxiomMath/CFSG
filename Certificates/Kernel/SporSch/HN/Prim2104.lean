
module

public import Certificates.Kernel.SporSch.HN.Prim2104K
public import Certificates.Kernel.SporSch.HN.Pt2109
public import CFSG.Certificates.Kernel.SporSch.HNXSubSound
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public import CFSG.Sporadic.Th.TableSpec
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.HNPrim2104

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS CFSG.KS.SporSch CFSG.KS.SporSch.HNXP
open CFSG.KS.HNArr CFSG.KC.VecK CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th
open CFSG.ONSchreier.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.HNArrS CertificateChecks.KernelSporSch.HNPt2103 Finset Matrix

local notation "UT" => CFSG.KD.HNPrim.UT
local notation "TX" => CFSG.KD.LgHNX.TX

noncomputable abbrev u1 (i : ℕ) : ℕ := rf UT 0 21 i
noncomputable abbrev u2 (i : ℕ) : ℕ := rf UT 21 21 i
noncomputable abbrev lab (i : ℕ) : ℕ := rf UT 42 4 i
noncomputable abbrev dep (i : ℕ) : ℕ := rf UT 46 8 i
noncomputable abbrev par (i : ℕ) : ℕ := rf UT 54 21 i
noncomputable abbrev plet (i : ℕ) : ℕ := rf UT 75 1 i

noncomputable abbrev rep (j : ℕ) : ℕ := fldW CFSG.KD.HNPrim.REPS (21 * j) 21

theorem chunks {Q : ℕ → Prop} (h : ∀ k < 379, ∀ j < 47, Q (Nat.add (47 * k) j)) :
    ∀ b < 17813, Q b := by
  intro b hb
  have := h (b / 47) (by omega) (b % 47) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (47 * (b / 47)) (b % 47) = b := Nat.div_add_mod b 47
  rw [e] at this
  exact this

theorem split_pt {i : ℕ} (hi : i < nPts) : ∃ b r, b < 17813 ∧ r < hnxC b ∧ i = 64 * b + r := by
  obtain ⟨e, hb, hr⟩ := leaf_split hi
  exact ⟨_, _, hb, hr, e⟩

theorem orb_at {i : ℕ} (hi : i < nPts) :
    orbRec UT CFSG.KD.HNPrim.REPS i (getRec UT 76 i) = true := by
  obtain ⟨b, r, hb, hr, rfl⟩ := split_pt hi
  have hl := chunks (Q := fun b => orbLeaf UT CFSG.KD.HNPrim.REPS b = true)
    (fun k hk j hj => allN_spec (orb_all k hk) j hj) b hb
  have h := orbLeaf_sound hl r hr
  rw [← getRec76_leaf UT b r (Nat.lt_of_lt_of_le hr (hnxC_le b))] at h
  exact h

theorem facts {i : ℕ} (hi : i < nPts) :
    u1 i < nPts ∧ u2 i < nPts ∧ lab i < 12 ∧ lab (u1 i) = lab i ∧ lab (u2 i) = lab i ∧
    rep (lab i) ≤ i ∧ (dep i = 0 → i = rep (lab i)) ∧
    (dep i ≠ 0 → par i < nPts ∧ dep (par i) + 1 = dep i ∧ rf UT (21 * plet i) 21 (par i) = i) :=
  orbRec_sound (orb_at hi)

theorem runProg_keep {G : Type*} [Group G] (k : ℕ) : ∀ (regs : ℕ → G) (prog : List (ℕ × ℕ × ℕ)),
    (∀ t ∈ prog, t.2.2 ≠ k) → runProg regs prog k = regs k
  | _, [], _ => rfl
  | regs, (a, b, c) :: rest, h => by
    rw [runProg, runProg_keep k _ rest (fun t ht => h t (List.mem_cons_of_mem _ ht)),
      Function.update_of_ne (h _ List.mem_cons_self).symm]

theorem hJ1_eq : hJ1 = aJ := by
  change runProg initJ Data.subgroupProgram 1 = aJ
  rw [runProg_keep 1 initJ _ (by decide)]
  rfl

theorem gi_aJ {i : ℕ} (hi : i < nPts) : gi aJ i = qv TX 0 i := by
  have hs : alphaT.size = nPts := hnsBase.alpha_size
  rw [← arrJ_get aJ hi, ← natTab_alpha, natTab_get (by omega)]
  change ap (hnsData.orbit ()).alpha i = _
  rw [HNXCert.hns_orbit]
  exact ((HNXP.orbit_facts HNXCert.hns_bind).2.2.2 i hi).2.1

theorem u1_eq {i : ℕ} (hi : i < nPts) : u1 i = qv TX 0 i := by
  obtain ⟨b, r, hb, hr, rfl⟩ := split_pt hi
  have hl := chunks (Q := fun b => eqLeaf TX UT b = true)
    (fun k hk j hj => allN_spec (eq_all k hk) j hj) b hb
  have hr64 : r < 64 := Nat.lt_of_lt_of_le hr (hnxC_le b)
  rw [u1, rf_leaf UT b r 0 21 hr64 (by norm_num), qv0_leaf TX b r hr64]
  exact eqLeaf_sound hl r hr

theorem gi_h1 {i : ℕ} (hi : i < nPts) : gi hJ1 i = u1 i := by
  rw [hJ1_eq, gi_aJ hi, u1_eq hi]

theorem gi_h2 {i : ℕ} (hi : i < nPts) : gi hJ2 i = u2 i := by
  have hu := (facts hi).2.1
  obtain ⟨b, r, hb, hr, rfl⟩ := split_pt hi
  have hl := chunks (Q := fun b => imgLeaf TX UT CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M
      CFSG.KD.HNPrim.TR1 CFSG.KD.OrdHN.ONE 21 b = true)
    (fun k hk j hj => allN_spec (img_all k hk) j hj) b hb
  rw [← Nat.eq_of_beq_eq_true tr_R1, ← Nat.eq_of_beq_eq_true tr_one] at hl
  have hv := imgLeaf_sound (W := CFSG.KD.HNPt.R 1) consts_parts.1 (R_canon (by norm_num)) hb hl r hr
  have hr64 : r < 64 := Nat.lt_of_lt_of_le hr (hnxC_le b)
  have hg : genJ 1 = hJ2 := by rw [genJ, if_pos (by norm_num), sL1]
  refine PK_injective _ (gi_lt _ hi) _ hu ?_
  rw [PK_gi _ hi, PK_eq hi, PK_eq hu, ← hg, ← R_mat (by norm_num), u2,
    rf_leaf UT b r 21 21 hr64 (by norm_num), hv]

noncomputable abbrev L2 : Array Table := #[toTable (arrJ hJ1), toTable (arrJ hJ2)]

theorem L2_0 : L2[0]! = toTable (arrJ hJ1) := by
  simp only [L2, List.getElem!_toArray, List.getElem!_cons_zero]

theorem L2_1 : L2[1]! = toTable (arrJ hJ2) := by
  simp only [L2, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem L2_ap {l x : ℕ} (hl : l ∈ (#[0, 1] : Array ℕ))
    (hx : x < nPts) : ap L2[l]! x = rf UT (21 * l) 21 x := by
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · rw [L2_0, HNPt2109.ap_toTable hx, gi_h1 hx]
  · rw [L2_1, HNPt2109.ap_toTable hx, gi_h2 hx]

theorem lab_rep : ∀ j < 12, lab (rep j) = j := by
  intro j hj
  exact Nat.eq_of_beq_eq_true (allN_spec lab_reps j hj)

theorem reps_eq : ∀ j < 12, rep j = Data.subgroupOrbitReps.toArray[j]! := by decide +kernel

theorem rep_lt : ∀ j < 12, rep j < nPts := by decide +kernel

theorem plet_cases (i : ℕ) : plet i = 0 ∨ plet i = 1 := by
  have := fldW_lt (getRec UT 76 i) 75 1
  change plet i < 2 at this
  omega

theorem reach_iff {j : ℕ} (hj : j < 12) (q : ℕ) :
    Reach (· ∈ (#[0, 1] : Array ℕ)) (fun l x => ap L2[l]! x) (rep j) q ↔ q < nPts ∧ lab q = j := by
  constructor
  · intro h
    induction h with
    | root => exact ⟨rep_lt j hj, lab_rep j hj⟩
    | @step p l _ hl ih =>
      obtain ⟨hp, hpl⟩ := ih
      rw [L2_ap hl hp]
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hl
      obtain ⟨f1, f2, -, f4, f5, -⟩ := facts hp
      rcases hl with rfl | rfl
      · exact ⟨f1, f4.trans hpl⟩
      · exact ⟨f2, f5.trans hpl⟩
  · rintro ⟨hq, hql⟩
    suffices key : ∀ d, ∀ q < nPts, dep q = d → lab q = j →
        Reach (· ∈ (#[0, 1] : Array ℕ)) (fun l x => ap L2[l]! x) (rep j) q from
      key _ q hq rfl hql
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro q hq hd hl
      obtain ⟨-, -, -, -, -, -, h0, h1⟩ := facts hq
      rcases Nat.eq_zero_or_pos (dep q) with hd0 | hd0
      · rw [h0 hd0, hl]
        exact Reach.root
      · obtain ⟨hp, hdp, hpq⟩ := h1 (by omega)
        obtain ⟨-, -, -, g4, g5, -⟩ := facts hp
        have hlv : plet q ∈ (#[0, 1] : Array ℕ) := by
          rcases plet_cases q with e | e <;> rw [e] <;> simp
        have hlp : lab (par q) = j := by
          rcases plet_cases q with e | e
          · rw [e] at hpq
            rw [← g4, ← hl]
            exact congrArg lab hpq
          · rw [e] at hpq
            rw [← g5, ← hl]
            exact congrArg lab hpq
        have hr := ih (dep (par q)) (by omega) (par q) hp rfl hlp
        have := Reach.step (f := fun l x => ap L2[l]! x) hr hlv
        rw [L2_ap hlv hp, hpq] at this
        exact this

theorem L2_lt : ∀ l ∈ (#[0, 1] : Array ℕ), ∀ x < nPts,
    ap L2[l]! x < nPts := by
  intro l hl x hx
  rw [L2_ap hl hx]
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact (facts hx).1
  · exact (facts hx).2.1

noncomputable abbrev TB (j : ℕ) : Tree := treeBFS nPts (rep j) L2 #[0, 1]

theorem tree_spec' {j : ℕ} (hj : j < 12) :
    BFSSpec nPts (rep j) L2 #[0, 1] (TB j) :=
  treeBFS_spec (by norm_num) (rep_lt j hj) (fun l hl => by
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> norm_num) L2_lt

theorem mem_tree {j : ℕ} (hj : j < 12) (q : ℕ) :
    (∃ t < (TB j).pts.size, ap (TB j).pts t = q) ↔ q < nPts ∧ lab q = j := by
  rw [← (tree_spec' hj).facts.reach_iff, reach_iff hj]

theorem leaf_cnt (b : ℕ) : cntLeaf UT b = ∑ r ∈ range (hnxC b), 2 ^ (21 * lab (64 * b + r)) := by
  rw [cntLeaf_eq]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [lab, rf_leaf UT b r 42 4 (Nat.lt_of_lt_of_le (Finset.mem_range.1 hr) (hnxC_le b))
    (by norm_num)]

theorem cntSum_of {k lo' n' : ℕ} (h : CFSG.KD.HNXK.cntOk k = true) (h1 : 2256 * k = lo')
    (h2 : CFSG.KD.HNXK.primLen k = n') : cntSum UT lo' n' = CFSG.KD.HNXK.PRIMC k := by
  subst h1 h2
  exact Nat.eq_of_beq_eq_true h

theorem cnt_add {a n v u : ℕ} (h : cntSum UT a n = v) (hu : ∑ b ∈ range a, cntLeaf UT b = u) :
    ∑ b ∈ range (a + n), cntLeaf UT b = u + v := by
  rw [Finset.sum_range_add, hu, ← h, cntSum_eq]

theorem cnt_total : ∑ b ∈ range 17813, cntLeaf UT b = CFSG.KD.HNPrim.SIZES := by
  have z : ∑ b ∈ range 0, cntLeaf UT b = 0 := rfl
  have s0 := cnt_add (cntSum_of CFSG.KD.HNXK.N.c0 (lo' := 0) (n' := 2256) (by decide) (by decide)) z
  have s1 := cnt_add (cntSum_of CFSG.KD.HNXK.N.c1 (lo' := 0 + 2256) (n' := 2256) (by decide)
    (by decide)) s0
  have s2 := cnt_add (cntSum_of CFSG.KD.HNXK.N.c2 (lo' := 0 + 2256 + 2256) (n' := 2256) (by decide)
    (by decide)) s1
  have s3 := cnt_add (cntSum_of CFSG.KD.HNXK.N.c3 (lo' := 0 + 2256 + 2256 + 2256) (n' := 2256)
    (by decide) (by decide)) s2
  have s4 := cnt_add (cntSum_of CFSG.KD.HNXK.N.c4 (lo' := 0 + 2256 + 2256 + 2256 + 2256)
    (n' := 2256) (by decide) (by decide)) s3
  have s5 := cnt_add (cntSum_of CFSG.KD.HNXK.N.c5 (lo' := 0 + 2256 + 2256 + 2256 + 2256 + 2256)
    (n' := 2256) (by decide) (by decide)) s4
  have s6 := cnt_add (cntSum_of CFSG.KD.HNXK.N.c6
    (lo' := 0 + 2256 + 2256 + 2256 + 2256 + 2256 + 2256) (n' := 2256) (by decide) (by decide)) s5
  have s7 := cnt_add (cntSum_of CFSG.KD.HNXK.N.c7
    (lo' := 0 + 2256 + 2256 + 2256 + 2256 + 2256 + 2256 + 2256) (n' := 2021) (by decide)
    (by decide)) s6
  exact s7.trans (by decide +kernel)

noncomputable abbrev cls (j : ℕ) : Finset ℕ := (range nPts).filter fun q => lab q = j

theorem lab_lt {q : ℕ} (hq : q ∈ range nPts) : lab q ∈ range 12 :=
  Finset.mem_range.2 (facts (Finset.mem_range.1 hq)).2.2.1

theorem card_class {j : ℕ} (hj : j < 12) : (cls j).card = fldW CFSG.KD.HNPrim.SIZES (21 * j) 21 := by
  have hS : ∑ i ∈ range nPts, 2 ^ (21 * lab i) = ∑ k ∈ range 12, (cls k).card * 2 ^ (21 * k) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := lab) (t := range 12) fun q hq => lab_lt hq]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => 2 ^ (21 * k)) fun q hq => by
      rw [(Finset.mem_filter.1 hq).2], Finset.sum_const, smul_eq_mul]
  have htot : ∑ i ∈ range nPts, 2 ^ (21 * lab i) = CFSG.KD.HNPrim.SIZES := by
    rw [← cnt_total, ← sum_leaves]
    exact Finset.sum_congr rfl fun b _ => (leaf_cnt b).symm
  have hlt : ∀ k < 12, (cls k).card < 2 ^ 21 := fun k _ =>
    Nat.lt_of_le_of_lt ((Finset.card_filter_le _ _).trans (Finset.card_range _).le) (by norm_num)
  rw [fldW_eq, ← htot, hS]
  exact ((digit21 (fun k => (cls k).card) 12 hlt).2 j hj).symm

theorem sizes_eq : ∀ j < 12, fldW CFSG.KD.HNPrim.SIZES (21 * j) 21 = Data.subgroupOrbitSizes[j]! := by
  decide +kernel

theorem tree_size {j : ℕ} (hj : j < 12) :
    (TB j).pts.size = Data.subgroupOrbitSizes[j]! := by
  rw [← sizes_eq j hj, ← card_class hj]
  have H := (tree_spec' hj).facts
  have himg : (range (TB j).pts.size).image (ap (TB j).pts) = cls j := by
    ext q
    rw [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    simp only [Finset.mem_range]
    exact mem_tree hj q
  rw [← himg, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb e
  rw [← H.ix_pt a (Finset.mem_range.1 (Finset.mem_coe.1 ha)),
    ← H.ix_pt b (Finset.mem_range.1 (Finset.mem_coe.1 hb)), e]

theorem forIn_yield_inv {α β : Type} (l0 : List α) (R : List α → β → Prop) (g : α → β → β)
    (hg : ∀ pre a b, a ∈ l0 → R pre b → R (pre ++ [a]) (g a b)) :
    ∀ (l pre : List α) (b : β), (∀ a ∈ l, a ∈ l0) → R pre b →
      R (pre ++ l) (forIn (m := Id) l b fun a b => pure (ForInStep.yield (g a b)))
  | [], pre, b, _, h => by
    rw [List.append_nil, List.forIn_nil]
    exact h
  | a :: l, pre, b, hl, h => by
    rw [List.forIn_cons]
    have := forIn_yield_inv l0 R g hg l (pre ++ [a]) (g a b) (fun x hx => hl x (by simp [hx]))
      (hg pre a b (hl a (by simp)) h)
    rw [List.append_assoc, List.singleton_append] at this
    exact this

theorem forIn_range_yield {β : Type} (N : Nat) (R : List Nat → β → Prop) (g : Nat → β → β)
    (init : β) (h0 : R [] init) (hg : ∀ pre j b, j < N → R pre b → R (pre ++ [j]) (g j b)) :
    R (List.range' 0 N) (forIn (m := Id) [0:N] init fun j b => pure (ForInStep.yield (g j b))) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hs : ([0:N] : Std.Legacy.Range).size = N := by simp [Std.Legacy.Range.size]
  rw [hs]
  have := forIn_yield_inv (List.range' 0 N) R g
    (fun pre a b ha hR => hg pre a b (by have := List.mem_range'_1.1 ha; omega) hR)
    (List.range' 0 N) [] init (fun a ha => ha) h0
  rw [List.nil_append] at this
  exact this

theorem subLabels_eq (n : Nat) (S : Array Tree) :
    subLabels n S = (forIn (m := Id) [0:S.size] (Array.replicate n S.size) fun j labs =>
      pure (ForInStep.yield (Id.run (forIn (m := Id) [0:S[j]!.pts.size] labs fun k labs' =>
        pure (ForInStep.yield (labs'.set! (ap S[j]!.pts k) j)))))) := rfl

theorem subLabels_spec {n : Nat} {S : Array Tree} {lbl : Nat → Nat}
    (hlt : ∀ j < S.size, ∀ t < S[j]!.pts.size, ap S[j]!.pts t < n)
    (hlbl : ∀ j < S.size, ∀ t < S[j]!.pts.size, lbl (ap S[j]!.pts t) = j)
    (hcov : ∀ p < n, ∃ j < S.size, ∃ t < S[j]!.pts.size, ap S[j]!.pts t = p) :
    ∀ p < n, (subLabels n S)[p]! = lbl p := by
  let C : List Nat → Nat → Prop := fun pre p =>
    ∃ j ∈ pre, j < S.size ∧ ∃ t < S[j]!.pts.size, ap S[j]!.pts t = p
  have key := forIn_range_yield S.size
    (fun pre (labs : Array Nat) => labs.size = n ∧ ∀ p < n, C pre p → labs[p]! = lbl p)
    (fun j labs => Id.run (forIn (m := Id) [0:S[j]!.pts.size] labs fun k labs' =>
      pure (ForInStep.yield (labs'.set! (ap S[j]!.pts k) j))))
    (Array.replicate n S.size) ⟨by simp, fun p _ ⟨j, hj, _⟩ => by simp at hj⟩
    (fun pre j labs hj ⟨hs, hold⟩ => by
      have inner := forIn_range_yield S[j]!.pts.size
        (fun pre' (labs' : Array Nat) => labs'.size = n ∧ ∀ p < n,
          (C pre p ∨ ∃ t ∈ pre', ap S[j]!.pts t = p) → labs'[p]! = lbl p)
        (fun k labs' => labs'.set! (ap S[j]!.pts k) j) labs
        ⟨hs, fun p hp hc => by
          rcases hc with hc | ⟨t, ht, _⟩
          · exact hold p hp hc
          · simp at ht⟩
        (fun pre' t labs' ht ⟨hs', h'⟩ => by
          refine ⟨by rw [Array.size_set!, hs'], fun p hp hc => ?_⟩
          by_cases e : ap S[j]!.pts t = p
          · subst e
            rw [Array.getElem!_set!_self _ _ _ (by rw [hs']; exact hlt j hj t ht), hlbl j hj t ht]
          · rw [Array.getElem!_set!_ne _ _ _ _ e]
            refine h' p hp ?_
            rcases hc with hc | ⟨t', ht', e'⟩
            · exact Or.inl hc
            · rcases List.mem_append.1 ht' with h2 | h2
              · exact Or.inr ⟨t', h2, e'⟩
              · have : t' = t := by simpa using h2
                subst this
                exact absurd e' e)
      refine ⟨inner.1, fun p hp ⟨j', hj', hj's, t, ht, e⟩ => inner.2 p hp ?_⟩
      rcases List.mem_append.1 hj' with h2 | h2
      · exact Or.inl ⟨j', h2, hj's, t, ht, e⟩
      · have : j' = j := by simpa using h2
        subst this
        exact Or.inr ⟨t, List.mem_range'_1.2 ⟨by omega, by omega⟩, e⟩)
  intro p hp
  rw [subLabels_eq]
  obtain ⟨j, hj, t, ht, e⟩ := hcov p hp
  exact key.2 p hp ⟨j, List.mem_range'_1.2 ⟨by omega, by omega⟩, hj, t, ht, e⟩

noncomputable abbrev TS : Array Tree :=
  Data.subgroupOrbitReps.toArray.map fun r => treeBFS nPts r L2 #[0, 1]

theorem TS_size : TS.size = 12 := by simp [TS, Data.subgroupOrbitReps]

theorem TS_get {j : ℕ} (hj : j < 12) : TS[j]! = TB j := by
  have hj' : j < Data.subgroupOrbitReps.toArray.size := by simp [Data.subgroupOrbitReps]; omega
  rw [getElem!_pos TS j (by rw [TS_size]; exact hj), Array.getElem_map,
    ← getElem!_pos Data.subgroupOrbitReps.toArray j hj', ← reps_eq j hj]

theorem TS_mem {j : ℕ} (hj : j < 12) (q : ℕ) :
    (∃ t < TS[j]!.pts.size, ap TS[j]!.pts t = q) ↔ q < nPts ∧ lab q = j := by
  rw [TS_get hj]
  exact mem_tree hj q

theorem labs_eq : ∀ p < nPts, (subLabels nPts TS)[p]! = lab p := by
  refine subLabels_spec (fun j hj t ht => ?_) (fun j hj t ht => ?_) (fun p hp => ?_)
  · rw [TS_size] at hj
    exact ((TS_mem hj _).1 ⟨t, ht, rfl⟩).1
  · rw [TS_size] at hj
    exact ((TS_mem hj _).1 ⟨t, ht, rfl⟩).2
  · have hl := (facts hp).2.2.1
    obtain ⟨t, ht, e⟩ := (TS_mem hl p).2 ⟨hp, rfl⟩
    exact ⟨lab p, by rw [TS_size]; exact hl, t, ht, e⟩

theorem pos_of_mem {j : ℕ} (hj : j < 12) {q : ℕ}
    (hq : ∃ t < TS[j]!.pts.size, ap TS[j]!.pts t = q) :
    ap TS[j]!.pos q < TS[j]!.pts.size ∧ ap TS[j]!.pts (ap TS[j]!.pos q) = q := by
  obtain ⟨t, ht, rfl⟩ := hq
  have H := (tree_spec' hj).facts
  rw [TS_get hj] at ht ⊢
  rw [H.ix_pt t ht]
  exact ⟨ht, rfl⟩

theorem rec_zero' : u1 0 = 0 ∧ u2 0 = 0 :=
  ⟨Nat.eq_of_beq_eq_true rec_zero1, Nat.eq_of_beq_eq_true rec_zero2⟩

@[expose] def mSum (L : List ℕ) (mask : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if mask.testBit k then mSum L mask k + L[k]! else mSum L mask k

theorem fold_mSum (L : List ℕ) (mask : ℕ) : ∀ k,
    Nat.fold k (fun i _ acc => if mask.testBit i then acc + L[i]! else acc) 0 = mSum L mask k
  | 0 => by rw [Nat.fold_zero]; rfl
  | k + 1 => by
    rw [Nat.fold_succ, fold_mSum L mask k]
    rfl

theorem divOK_ok : divOK nPts Data.subgroupOrbitSizes = true := by
  have key : ∀ m < 2048, (!(1140000 % mSum Data.subgroupOrbitSizes (2 * m + 1) 12 == 0) ||
      2 * m + 1 == 1 || 2 * m + 1 == 2 ^ 12 - 1) = true := by decide +kernel
  unfold divOK
  rw [allIn_eq_true]
  intro m _ hm
  have e : maskSum Data.subgroupOrbitSizes (2 * m + 1) = mSum Data.subgroupOrbitSizes (2 * m + 1) 12 :=
    fold_mSum _ _ 12
  rw [e]
  exact key m (by simpa [Data.subgroupOrbitSizes] using hm)

theorem subChecksH_ok :
    subChecksH nPts (toTable (arrJ hJ1)) (toTable (arrJ hJ2)) = true := by
  have hlab := labs_eq
  unfold subChecksH
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, divOK_ok⟩
  · rw [beq_iff_eq, HNPt2109.ap_toTable (x := 0) (by norm_num), gi_h1 (i := 0) (by norm_num)]
    exact rec_zero'.1
  · rw [beq_iff_eq, HNPt2109.ap_toTable (x := 0) (by norm_num), gi_h2 (i := 0) (by norm_num)]
    exact rec_zero'.2
  · rw [beq_iff_eq, HNPt2109.toTable_size, arrJ_size]
  · rw [beq_iff_eq, HNPt2109.toTable_size, arrJ_size]
  · rfl
  · rw [beq_iff_eq]
    refine List.ext_getElem (by simp [Data.subgroupOrbitSizes, Data.subgroupOrbitReps])
      fun j h1 h2 => ?_
    have hj : j < 12 := by simpa [Data.subgroupOrbitReps] using h1
    rw [List.getElem_map, Array.getElem_toList, ← getElem!_pos TS j (by rw [TS_size]; exact hj),
      TS_get hj, tree_size hj, getElem!_pos _ j h2]
  · rw [allIn_eq_true]
    intro j _ hj
    rw [Bool.and_eq_true, decide_eq_true_eq, ← reps_eq j hj, TS_get hj]
    exact ⟨rep_lt j hj, (tree_spec' hj).ok⟩
  · rw [allIn_eq_true]
    intro p _ hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [hlab p hp]
    have hl := (facts hp).2.2.1
    obtain ⟨a, b⟩ := pos_of_mem hl ((TS_mem hl p).2 ⟨hp, rfl⟩)
    exact ⟨⟨hl, a⟩, b⟩
  · rw [allIn_eq_true]
    intro j _ hj
    rw [allIn_eq_true]
    intro k _ hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, beq_eq_false_iff_ne]
    by_cases hjk : j = k
    · exact Or.inl hjk
    · refine Or.inr ?_
      by_cases h1 : ap TS[j]!.pos Data.subgroupOrbitReps.toArray[k]! < TS[j]!.pts.size
      · refine Or.inr fun h2 => hjk ?_
        have hm : ∃ t < TS[j]!.pts.size, ap TS[j]!.pts t = Data.subgroupOrbitReps.toArray[k]! :=
          ⟨_, h1, h2⟩
        rw [← reps_eq k hk, TS_mem hj] at hm
        exact hm.2.symm.trans (lab_rep k hk)
      · exact Or.inl h1
  · rw [allIn_eq_true]
    intro j _ hj
    rw [allIn_eq_true]
    intro t _ ht
    simp only [decide_eq_true_eq]
    obtain ⟨hq, hlq⟩ := (TS_mem hj _).1 ⟨t, ht, rfl⟩
    rw [← reps_eq j hj]
    have h := (facts hq).2.2.2.2.2.1
    rw [hlq] at h
    exact h

theorem primChecks_ok : primChecks (hnsData.orbit ()) = true := by
  have hreg := (progRegs_arrJ _ _ _ prog_lt (initRegs_get rfl rfl).1 (initRegs_get rfl rfl).2).1
  unfold primChecks
  try dsimp only
  rw [hns_n, natTab_alpha, natTab_beta, hreg, regs_get (k := 1) (by omega),
    regs_get (k := 2) (by omega)]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨trivial, ?_⟩, subChecksH_ok⟩
  rw [allIn_eq_true]
  intro i _ hi
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [arrJ_get _ hi, arrJ_get _ hi]
  exact ⟨gi_lt _ hi, gi_lt _ hi⟩

end CertificateChecks.KernelSporSch.HNPrim2104

end
