module

public import Certificates.Kernel.Sporadic.ONVs.Checks
public import Certificates.Kernel.Sporadic.ONC.Lines
public import CFSG.Certificates.Kernel.Spor.ONVsSound
public import CFSG.Sporadic.ON.Primitive

public section

namespace CertificateChecks.KernelSpor.ONVs

open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.Perm.Native
open CFSG.KS.PEnum CertificateChecks.KernelSpor
open CFSG.KS.ON (tab)
open CFSG.KS.ONVs (wordL wAt wAt_eq vs_sound)

attribute [-instance] ONC.idxAction0

theorem ap_letters {l : ℕ} (hl : l < 8) {x : ℕ} (hx : x < nPts) :
    ap CFSG.Sporadic.ON.letters[l]! x = ONC.LJ l x :=
  ONC.letters_LJ.2 l hl x hx

theorem letters_size_eq : CFSG.Sporadic.ON.letters.size = 8 := ONC.letters_size

theorem idx_pairG {l : ℕ} (hl : l < 8) {x : ℕ} (hx : x < nPts) :
    idx nPts (pairG gs l) x = ONC.LJ l x := by
  rw [← rep_pairG_all l (by rw [letters_size_eq]; exact hl) x hx]
  exact ap_letters hl hx

theorem pairG_mem {l : ℕ} (hl : l < 6) : pairG gs l ∈ lvl 1 := by
  have h0 : ap CFSG.Sporadic.ON.letters[l]! chainBase[0]! = chainBase[0]! := by
    rw [chainBase_zero, ap_letters (by omega) (by decide)]
    exact (vs_sound ONVs.vs_ok).1 l hl
  exact lG_mem ((mem_levelLetters_succ (i := 0)).2
    ⟨mem_levelLetters_zero.2 (by rw [letters_size_eq]; omega), h0⟩)

@[expose] noncomputable def wordE (w : List ℕ) : J := w.foldl (fun g l => pairG gs l * g) 1

theorem idx_foldl : ∀ (w : List ℕ) (g : J), (∀ l ∈ w, l < 8) → ∀ x < nPts,
    idx nPts (w.foldl (fun g l => pairG gs l * g) g) x =
      w.foldl (fun x l => ONC.LJ l x) (idx nPts g x)
  | [], _, _, _, _ => rfl
  | l :: w, g, hw, x, hx => by
    rw [List.foldl_cons, List.foldl_cons,
      idx_foldl w _ (fun l' h => hw l' (List.mem_cons_of_mem _ h)) x hx, idx_mul,
      idx_pairG (hw l (List.mem_cons.2 (Or.inl rfl))) (idx_lt g hx)]

theorem mem_lvl_foldl : ∀ (w : List ℕ) (g : J), (∀ l ∈ w, l < 6) → g ∈ lvl 1 →
    w.foldl (fun g l => pairG gs l * g) g ∈ lvl 1
  | [], _, _, hg => hg
  | l :: w, g, hw, hg => by
    rw [List.foldl_cons]
    exact mem_lvl_foldl w _ (fun l' h => hw l' (List.mem_cons_of_mem _ h))
      ((lvl 1).mul_mem (pairG_mem (hw l (List.mem_cons.2 (Or.inl rfl)))) hg)

@[expose] noncomputable def gw (k : ℕ) : J := wordE (wordL (OVS.D k))

theorem gw_mem {k : ℕ} (hk : k < 39) : gw k ∈ lvl 1 :=
  mem_lvl_foldl _ _ ((vs_sound ONVs.vs_ok).2.1 k hk) (lvl 1).one_mem

theorem idx_gw {k : ℕ} (hk : k < 39) {x : ℕ} (hx : x < nPts) :
    idx nPts (gw k) x = wAt ONC.LJ (OVS.D k) x := by
  have hl := (vs_sound ONVs.vs_ok).2.1 k hk
  rw [gw, wordE, idx_foldl _ _ (fun l h => by have := hl l h; omega) x hx, idx_one, wAt_eq]

theorem gw_smul {k : ℕ} (hk : k < 39) (p : Fin nPts) :
    (gw k • p).val = wAt ONC.LJ (OVS.D k) p.val := by
  rw [smul_val_eq_idx, idx_gw hk p.isLt]

theorem negF_val (k : Fin nPts) : (negF k).val = tab ONW2.NEG k.val := ONC.negN_ap k.isLt

theorem lineF_val (k : Fin nPts) : (lineF k).val = r32 ONC.LF k.val :=
  ONC.lineT_facts.2 k.val k.isLt

theorem repF_ne (j : Fin nLines) : repF j ≠ negF (repF j) := by
  intro h
  have h1 := congrArg Fin.val h
  have hr : (repF j).val = r32 ONC.RP j.val := ONC.reps_ap j.isLt
  rw [negF_val, hr] at h1
  exact absurd h1 (ne_of_lt (ONC.rp_pt j.isLt).2.2.1)

noncomputable abbrev lroot (i : Fin 5) : Fin nLines := ⟨subRoots[i.val]!, (subFacts i.isLt).r_lt⟩

theorem subLab_lroot (i : Fin 5) : subLab (lroot i) = i :=
  (subLab_eq_iff i _).2 (MulAction.mem_orbit_self _)

theorem card_orbit_lroot (i : Fin 5) :
    (MulAction.orbit (lvl 1) (lroot i)).ncard = subSizesF i := by
  classical
  have hset : MulAction.orbit (lvl 1) (lroot i) =
      ↑(Finset.univ.filter (fun p : Fin nLines => subLab p = i)) := by
    ext p
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact (subLab_eq_iff i p).symm
  rw [hset, Set.ncard_coe_finset, card_subLab, subSizes_getElem]

@[expose] noncomputable def cl (p : Fin nPts) : Fin 5 := subLab (lineF p)

theorem cl_smul {h : J} (hh : h ∈ lvl 1) (p : Fin nPts) : cl (h • p) = cl p := by
  unfold cl
  rw [lineF_smul]
  exact subLab_inv h hh _

theorem cl_neg (p : Fin nPts) : cl (negF p) = cl p := by
  unfold cl
  rw [lineF_negF]

theorem cl_of {p : Fin nPts} {i : Fin 5} (h : (lineF p).val = subRoots[i.val]!) : cl p = i := by
  have e : lineF p = lroot i := Fin.ext h
  unfold cl
  rw [e]
  exact subLab_lroot i

theorem exists_of_cl {p q : Fin nPts} (h : cl p = cl q) :
    ∃ g ∈ lvl 1, g • p = q ∨ g • p = negF q := by
  obtain ⟨g, hg, e⟩ := subLab_orb _ _ h
  refine ⟨g, hg, ?_⟩
  rw [← lineF_smul, lineF_eq_iff] at e
  rcases e with e | e
  · exact Or.inl e.symm
  · right
    rw [e, negF_negF]

@[expose] def Sw (p : Fin nPts) : Prop := ∃ s ∈ lvl 1, s • p = negF p

theorem Sw.smul {p : Fin nPts} (hp : Sw p) {u : J} (hu : u ∈ lvl 1) : Sw (u • p) := by
  obtain ⟨s, hs, e⟩ := hp
  refine ⟨u * s * u⁻¹, (lvl 1).mul_mem ((lvl 1).mul_mem hu hs) ((lvl 1).inv_mem hu), ?_⟩
  rw [mul_smul, mul_smul, inv_smul_smul, e, smul_negF]

theorem Sw.neg {p : Fin nPts} (hp : Sw p) : Sw (negF p) := by
  obtain ⟨s, hs, e⟩ := hp
  exact ⟨s, hs, by rw [smul_negF, e]⟩

theorem sw_of_cl {r : Fin nPts} (hr : Sw r) {p : Fin nPts} (h : cl r = cl p) : Sw p := by
  obtain ⟨g, hg, e | e⟩ := exists_of_cl h
  · rw [← e]
    exact hr.smul hg
  · have := (hr.smul hg).neg
    rwa [e, negF_negF] at this

theorem exists_of_cl_sw {p q : Fin nPts} (h : cl p = cl q) (hq : Sw q) :
    ∃ g ∈ lvl 1, g • p = q := by
  obtain ⟨g, hg, e | e⟩ := exists_of_cl h
  · exact ⟨g, hg, e⟩
  · obtain ⟨s, hs, es⟩ := hq
    refine ⟨s⁻¹ * g, (lvl 1).mul_mem ((lvl 1).inv_mem hs) hg, ?_⟩
    rw [mul_smul, e, ← es, inv_smul_smul]

theorem sw_word {k a : ℕ} (hk : k < 39) (ha : a < nPts)
    (h : wAt ONC.LJ (OVS.D k) a = tab ONW2.NEG a) : Sw ⟨a, ha⟩ :=
  ⟨gw k, gw_mem hk, Fin.ext (by rw [gw_smul hk, negF_val]; exact h)⟩

theorem sw_of_ne {q : Fin nPts} (h0 : cl q ≠ 0) (h3 : cl q ≠ 3) : Sw q := by
  obtain ⟨-, -, -, -, h5, h6, -, h8, h9, h10, h11, -, -⟩ := vs_sound ONVs.vs_ok
  have hi : ∀ i : Fin 5, i ≠ 0 → i ≠ 3 → i = 1 ∨ i = 2 ∨ i = 4 := by decide
  rcases hi _ h0 h3 with hq | hq | hq
  · refine sw_of_cl (sw_word (k := 0) (a := 2) (by norm_num) (by decide) h9) ?_
    rw [hq]
    exact cl_of (by rw [lineF_val]; exact h5)
  · refine sw_of_cl (sw_word (k := 1) (a := 6) (by norm_num) (by decide) h10) ?_
    rw [hq]
    exact cl_of (by rw [lineF_val]; exact h6)
  · refine sw_of_cl (sw_word (k := 2) (a := 56) (by norm_num) (by decide) h11) ?_
    rw [hq]
    exact cl_of (by rw [lineF_val]; exact h8)

theorem cl_root : cl root = 0 := by
  unfold cl
  rw [lineF_root]
  exact subLab_line0

theorem negF_root : negF root = ⟨1, by decide⟩ :=
  Fin.ext (by rw [negF_val]; exact (vs_sound ONVs.vs_ok).2.2.1)

theorem negF_root_ne : negF root ≠ root := by
  rw [negF_root]
  decide

theorem cl_zero {p : Fin nPts} : cl p = 0 ↔ p = root ∨ p = negF root := by
  constructor
  · intro h
    obtain ⟨g, hg, e | e⟩ := exists_of_cl (h.trans cl_root.symm)
    · left
      calc p = g⁻¹ • (g • p) := (inv_smul_smul g p).symm
        _ = g⁻¹ • root := by rw [e]
        _ = root := lvl_one_fix ((lvl 1).inv_mem hg)
    · right
      calc p = g⁻¹ • (g • p) := (inv_smul_smul g p).symm
        _ = g⁻¹ • negF root := by rw [e]
        _ = negF root := by rw [smul_negF, lvl_one_fix ((lvl 1).inv_mem hg)]
  · rintro (rfl | rfl)
    · exact cl_root
    · rw [cl_neg, cl_root]

noncomputable abbrev v20 : Fin nPts := ⟨20, by decide⟩

@[expose] def In20 (p : Fin nPts) : Prop := ∃ h ∈ lvl 1, h • v20 = p

theorem In20.smul {p : Fin nPts} (hp : In20 p) {u : J} (hu : u ∈ lvl 1) : In20 (u • p) := by
  obtain ⟨h, hh, e⟩ := hp
  exact ⟨u * h, (lvl 1).mul_mem hu hh, by rw [mul_smul, e]⟩

theorem lineF_v20 : lineF v20 = lroot 3 :=
  Fin.ext (by rw [lineF_val]; exact (vs_sound ONVs.vs_ok).2.2.2.2.2.2.1)

theorem cl_v20 : cl v20 = 3 := by
  unfold cl
  rw [lineF_v20]
  exact subLab_lroot 3

theorem in20_or {p : Fin nPts} (hp : cl p = 3) : In20 p ∨ In20 (negF p) := by
  obtain ⟨g, hg, e | e⟩ := exists_of_cl (cl_v20.trans hp.symm)
  · exact Or.inl ⟨g, hg, e⟩
  · exact Or.inr ⟨g, hg, e⟩

theorem key_eq {k : ℕ} (hk : k < 39) :
    CFSG.KS.ONVs.key ONC.LJ (OVS.D k) = idx nPts (gw k) 2 * 245520 + idx nPts (gw k) 4 := by
  change wAt ONC.LJ (OVS.D k) 2 * 245520 + wAt ONC.LJ (OVS.D k) 4 = _
  rw [idx_gw hk (by decide), idx_gw hk (by decide)]

theorem gw_inj {i j : ℕ} (hi : i < 36) (hj : j < 36) (h : gw (3 + i) = gw (3 + j)) : i = j := by
  have hkey := (vs_sound ONVs.vs_ok).2.2.2.2.2.2.2.2.2.2.2.2
  have e : CFSG.KS.ONVs.key ONC.LJ (OVS.D (3 + i)) = CFSG.KS.ONVs.key ONC.LJ (OVS.D (3 + j)) := by
    rw [key_eq (by omega), key_eq (by omega), h]
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd e (ne_of_lt (hkey i hi j hj hij))
  · exact hij
  · exact absurd e (ne_of_gt (hkey j hj i hi hij))

theorem card_stab_lroot : Nat.card (MulAction.stabilizer (lvl 1) (lroot 3)) = 36 := by
  have h := Subgroup.card_mul_index (MulAction.stabilizer (lvl 1) (lroot 3))
  rw [MulAction.index_stabilizer, card_orbit_lroot, card_lvl_one] at h
  have e : subSizesF 3 = 52136 := rfl
  rw [e] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))

theorem card_stab_v20 [Finite (lvl 1)] : 36 ≤ Nat.card (MulAction.stabilizer (lvl 1) v20) := by
  have hfix := (vs_sound ONVs.vs_ok).2.2.2.2.2.2.2.2.2.2.2.1
  let φ : Fin 36 → MulAction.stabilizer (lvl 1) v20 := fun k =>
    ⟨⟨gw (3 + k.val), gw_mem (by omega)⟩, by
      rw [MulAction.mem_stabilizer_iff]
      exact Fin.ext (by
        change (gw (3 + k.val) • v20).val = 20
        rw [gw_smul (by omega)]
        exact hfix k.val k.isLt)⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have e := congrArg (fun x : MulAction.stabilizer (lvl 1) v20 => ((x : lvl 1) : J)) hab
    exact Fin.ext (gw_inj a.isLt b.isLt e)
  have := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_fin] at this

theorem not_in20_neg : ¬ In20 (negF v20) := by
  rintro ⟨h, hh, e⟩
  have : Finite (lvl 1) := Nat.finite_of_card_ne_zero (by rw [card_lvl_one]; norm_num)
  have hle : MulAction.stabilizer (lvl 1) v20 ≤ MulAction.stabilizer (lvl 1) (lroot 3) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def] at hg ⊢
    rw [← lineF_v20, ← lineF_smul, hg]
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [card_stab_lroot]; exact card_stab_v20)
  have hmem : (⟨h, hh⟩ : lvl 1) ∈ MulAction.stabilizer (lvl 1) (lroot 3) := by
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    change h • lroot 3 = lroot 3
    rw [← lineF_v20, ← lineF_smul, e, lineF_negF]
  rw [← heq, MulAction.mem_stabilizer_iff, Subgroup.smul_def] at hmem
  have h1 := congrArg Fin.val (e.symm.trans hmem)
  rw [negF_val] at h1
  have h2 := (vs_sound ONVs.vs_ok).2.2.2.1
  change tab ONW2.NEG 20 = 20 at h1
  omega

theorem not_in20_neg_of {p : Fin nPts} (hp : In20 p) : ¬ In20 (negF p) := by
  rintro ⟨h, hh, e⟩
  obtain ⟨k, hk, ek⟩ := hp
  apply not_in20_neg
  refine ⟨k⁻¹ * h, (lvl 1).mul_mem ((lvl 1).inv_mem hk) hh, ?_⟩
  rw [mul_smul, e, ← ek, ← smul_negF, inv_smul_smul]

@[expose] def T (i : Fin 5) (b : Bool) : Fin 7 :=
  ![bif b then 0 else 1, 2, 3, bif b then 4 else 5, 6] i

theorem T_inj : ∀ i j b c, T i b = T j c → i = j ∧ ((i = 0 ∨ i = 3) → b = c) := by decide

@[expose] def fl (p : Fin nPts) : Prop := if cl p = 0 then p = root else In20 p

noncomputable instance fl_dec : DecidablePred fl := fun _ => Classical.propDecidable _

@[expose] noncomputable def vf (p : Fin nPts) : Fin 7 := T (cl p) (decide (fl p))

theorem fl_zero {p : Fin nPts} (h : cl p = 0) : fl p ↔ p = root := by
  unfold fl
  rw [if_pos h]

theorem fl_ne {p : Fin nPts} (h : cl p ≠ 0) : fl p ↔ In20 p := by
  unfold fl
  rw [if_neg h]

theorem fl_smul {h : J} (hh : h ∈ lvl 1) (p : Fin nPts) : fl (h • p) ↔ fl p := by
  by_cases h0 : cl p = 0
  · rw [fl_zero h0, fl_zero ((cl_smul hh p).trans h0)]
    constructor
    · intro e
      calc p = h⁻¹ • (h • p) := (inv_smul_smul h p).symm
        _ = h⁻¹ • root := by rw [e]
        _ = root := lvl_one_fix ((lvl 1).inv_mem hh)
    · intro e
      rw [e, lvl_one_fix hh]
  · rw [fl_ne h0, fl_ne (by rw [cl_smul hh]; exact h0)]
    constructor
    · intro e
      have := e.smul ((lvl 1).inv_mem hh)
      rwa [inv_smul_smul] at this
    · intro e
      exact e.smul hh

theorem vf_eq_iff (p q : Fin nPts) : vf p = vf q ↔ ∃ h ∈ lvl 1, h • p = q := by
  constructor
  · intro hpq
    obtain ⟨hc, hb⟩ := T_inj _ _ _ _ hpq
    by_cases h0 : cl p = 0
    · have hf : fl p ↔ fl q := decide_eq_decide.1 (hb (Or.inl h0))
      rw [fl_zero h0, fl_zero (hc ▸ h0)] at hf
      have e : p = q := by
        rcases cl_zero.1 h0 with hp | hp <;> rcases cl_zero.1 (hc ▸ h0) with hq | hq
        · rw [hp, hq]
        · exact absurd (hf.1 hp) (by rw [hq]; exact negF_root_ne)
        · exact absurd (hf.2 hq) (by rw [hp]; exact negF_root_ne)
        · rw [hp, hq]
      exact ⟨1, (lvl 1).one_mem, by rw [one_smul, e]⟩
    by_cases h3 : cl p = 3
    · have hf : fl p ↔ fl q := decide_eq_decide.1 (hb (Or.inr h3))
      rw [fl_ne h0, fl_ne (hc ▸ h0)] at hf
      by_cases hp : In20 p
      · obtain ⟨a, ha, rfl⟩ := hp
        obtain ⟨b, hb', rfl⟩ := hf.1 ⟨a, ha, rfl⟩
        exact ⟨b * a⁻¹, (lvl 1).mul_mem hb' ((lvl 1).inv_mem ha), by
          rw [mul_smul, inv_smul_smul]⟩
      · have hp' := (in20_or h3).resolve_left hp
        have hq' := (in20_or (hc ▸ h3)).resolve_left (fun h => hp (hf.2 h))
        obtain ⟨a, ha, ea⟩ := hp'
        obtain ⟨b, hb', eb⟩ := hq'
        refine ⟨b * a⁻¹, (lvl 1).mul_mem hb' ((lvl 1).inv_mem ha), ?_⟩
        apply (negF_negF _).symm.trans
        rw [← smul_negF, ← ea, mul_smul, inv_smul_smul, eb, negF_negF]
    · exact exists_of_cl_sw hc (sw_of_ne (hc ▸ h0) (hc ▸ h3))
  · rintro ⟨h, hh, rfl⟩
    unfold vf
    rw [cl_smul hh]
    congr 1
    exact decide_eq_decide.2 (fl_smul hh p).symm

theorem card_cl (i : Fin 5) :
    (Finset.univ.filter fun p : Fin nPts => cl p = i).card = 2 * subSizesF i := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := lineF)
    (t := Finset.univ.filter fun l : Fin nLines => subLab l = i) (fun p hp => by
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hp ⊢
      exact hp)]
  have hfib : ∀ l ∈ Finset.univ.filter (fun l : Fin nLines => subLab l = i),
      ((Finset.univ.filter fun p : Fin nPts => cl p = i).filter fun p => lineF p = l).card =
        2 := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    have e : ((Finset.univ.filter fun p : Fin nPts => cl p = i).filter fun p => lineF p = l) =
        {repF l, negF (repF l)} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨-, hp⟩
        exact (lineF_eq_iff (repF l) p).1 (by rw [lineF_repF, hp])
      · intro hp
        have hl' : lineF p = l := by
          rcases hp with rfl | rfl
          · exact lineF_repF l
          · rw [lineF_negF, lineF_repF]
        refine ⟨?_, hl'⟩
        unfold cl
        rw [hl']
        exact hl
    rw [e, Finset.card_pair (repF_ne l)]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, card_subLab, subSizes_getElem,
    mul_comm]

theorem filter_vf_cl {k : Fin 7} {i : Fin 5} (hk : ∀ b, T i b = k)
    (hk' : ∀ j b, T j b = k → j = i) :
    (Finset.univ.filter fun p : Fin nPts => vf p = k) =
      Finset.univ.filter fun p : Fin nPts => cl p = i := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact hk' _ _
  · intro h
    unfold vf
    rw [h]
    exact hk _

theorem card_vf_cl {k : Fin 7} {i : Fin 5} (hk : ∀ b, T i b = k)
    (hk' : ∀ j b, T j b = k → j = i) :
    (Finset.univ.filter fun p : Fin nPts => vf p = k).card = 2 * subSizesF i := by
  rw [filter_vf_cl hk hk', card_cl]

theorem vf_root : vf root = 0 := by
  unfold vf
  rw [cl_root]
  have : decide (fl root) = true := decide_eq_true ((fl_zero cl_root).2 rfl)
  rw [this]
  rfl

theorem vf_negRoot : vf (negF root) = 1 := by
  unfold vf
  have h0 : cl (negF root) = 0 := by rw [cl_neg, cl_root]
  rw [h0]
  have : decide (fl (negF root)) = false :=
    decide_eq_false (fun h => negF_root_ne ((fl_zero h0).1 h))
  rw [this]
  rfl

theorem vf_zero_iff (p : Fin nPts) : vf p = 0 ↔ p = root := by
  constructor
  · intro h
    have hT : ∀ i b, T i b = 0 → i = 0 ∧ b = true := by decide
    obtain ⟨h0, hb⟩ := hT _ _ h
    exact (fl_zero h0).1 (of_decide_eq_true hb)
  · rintro rfl
    exact vf_root

theorem vf_one_iff (p : Fin nPts) : vf p = 1 ↔ p = negF root := by
  constructor
  · intro h
    have hT : ∀ i b, T i b = 1 → i = 0 ∧ b = false := by decide
    obtain ⟨h0, hb⟩ := hT _ _ h
    have hf : ¬ fl p := of_decide_eq_false hb
    rw [fl_zero h0] at hf
    exact (cl_zero.1 h0).resolve_left hf
  · rintro rfl
    exact vf_negRoot

theorem vf_four_iff (p : Fin nPts) : vf p = 4 ↔ cl p = 3 ∧ In20 p := by
  have hT : ∀ i b, T i b = 4 ↔ i = 3 ∧ b = true := by decide
  unfold vf
  rw [hT]
  constructor
  · rintro ⟨h3, hb⟩
    exact ⟨h3, (fl_ne (by rw [h3]; decide)).1 (of_decide_eq_true hb)⟩
  · rintro ⟨h3, hp⟩
    exact ⟨h3, decide_eq_true ((fl_ne (by rw [h3]; decide)).2 hp)⟩

theorem vf_five_iff (p : Fin nPts) : vf p = 5 ↔ cl p = 3 ∧ ¬ In20 p := by
  have hT : ∀ i b, T i b = 5 ↔ i = 3 ∧ b = false := by decide
  unfold vf
  rw [hT]
  constructor
  · rintro ⟨h3, hb⟩
    exact ⟨h3, fun h => of_decide_eq_false hb ((fl_ne (by rw [h3]; decide)).2 h)⟩
  · rintro ⟨h3, hp⟩
    exact ⟨h3, decide_eq_false (fun h => hp ((fl_ne (by rw [h3]; decide)).1 h))⟩

@[expose] noncomputable def negE : Fin nPts ≃ Fin nPts := ⟨negF, negF, negF_negF, negF_negF⟩

theorem card_vf_four_five :
    (Finset.univ.filter fun p : Fin nPts => vf p = 4).card =
      (Finset.univ.filter fun p : Fin nPts => vf p = 5).card := by
  have e : (Finset.univ.filter fun p : Fin nPts => vf p = 5) =
      (Finset.univ.filter fun p : Fin nPts => vf p = 4).map negE.toEmbedding := by
    ext q
    rw [Finset.mem_map_equiv]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, vf_four_iff, vf_five_iff]
    change cl q = 3 ∧ ¬ In20 q ↔ cl (negF q) = 3 ∧ In20 (negF q)
    rw [cl_neg]
    constructor
    · rintro ⟨h3, hq⟩
      exact ⟨h3, (in20_or h3).resolve_left hq⟩
    · rintro ⟨h3, hq⟩
      refine ⟨h3, fun h => ?_⟩
      have := not_in20_neg_of hq
      rw [negF_negF] at this
      exact this h
  rw [e, Finset.card_map]

theorem card_vf_four : (Finset.univ.filter fun p : Fin nPts => vf p = 4).card = 52136 := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
    fun p : Fin nPts => cl p = 3) (fun p => In20 p)
  rw [card_cl] at h
  have e4 : (Finset.univ.filter fun p : Fin nPts => cl p = 3).filter (fun p => In20 p) =
      Finset.univ.filter fun p : Fin nPts => vf p = 4 := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, vf_four_iff]
  have e5 : (Finset.univ.filter fun p : Fin nPts => cl p = 3).filter (fun p => ¬ In20 p) =
      Finset.univ.filter fun p : Fin nPts => vf p = 5 := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, vf_five_iff]
  rw [e4, e5, ← card_vf_four_five] at h
  have e : subSizesF 3 = 52136 := rfl
  rw [e] at h
  omega

theorem card_vf (i : Fin 7) : (Finset.univ.filter fun p : Fin nPts => vf p = i).card =
    ![1, 1, 11172, 117306, 52136, 52136, 12768] i := by
  fin_cases i
  · have e : (Finset.univ.filter fun p : Fin nPts => vf p = 0) = {root} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, vf_zero_iff]
    simp only [Fin.zero_eta, Fin.isValue] at e ⊢
    rw [e, Finset.card_singleton]
    rfl
  · have e : (Finset.univ.filter fun p : Fin nPts => vf p = 1) = {negF root} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, vf_one_iff]
    simp only [Fin.mk_one, Fin.isValue] at e ⊢
    rw [e, Finset.card_singleton]
    rfl
  · exact (card_vf_cl (k := 2) (i := 1) (by decide) (by decide)).trans rfl
  · exact (card_vf_cl (k := 3) (i := 2) (by decide) (by decide)).trans rfl
  · exact card_vf_four
  · exact card_vf_four_five.symm.trans card_vf_four
  · exact (card_vf_cl (k := 6) (i := 4) (by decide) (by decide)).trans rfl

theorem vs_orbits : ∃ f : Fin nPts → Fin 7,
    (∀ p q, f p = f q ↔ ∃ h ∈ lvl 1, h • p = q) ∧
    (∀ i, (Finset.univ.filter (fun p => f p = i)).card =
      ![1, 1, 11172, 117306, 52136, 52136, 12768] i) ∧
    f root = 0 ∧ f ⟨1, by norm_num⟩ = 1 :=
  ⟨vf, vf_eq_iff, card_vf, vf_root, by rw [← negF_root]; exact vf_negRoot⟩

end CertificateChecks.KernelSpor.ONVs

end
