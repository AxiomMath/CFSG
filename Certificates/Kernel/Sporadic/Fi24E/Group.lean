
module

public import Certificates.Kernel.Sporadic.Fi24E.CheckSg
public import Certificates.Kernel.Sporadic.Fi24E.CheckCv
public import Certificates.Kernel.Sporadic.Fi24E.CheckFx
public import Certificates.Kernel.Sporadic.Fi24Oct.Group
public import CFSG.Certificates.Kernel.Spor.Fi24ESound
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24ECardBase
public import CFSG.Sporadic.Fi24.Fi24EFacts
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.KD.Fi24E.Group

open CFSG.Sporadic.Fi24 (R cls bbar bbarPt bbar_comm Fi24EFacts)
open CFSG.KC CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Oct CFSG.KC.Fi24E CFSG.KS.Fi24ThreeO CFSG.KS.Fi24Oct
  CFSG.KS.Fi24E CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24Oct CFSG.KD.Fi24ThreeO.Group
  CFSG.KD.Fi24E
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three (wordElt)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Fi24K (fi24EB comm_of_mem_closure comm_fi24EB
  fi24EB_comm comm_cls_of_smul le_card_fi24EB)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] CFSG.Sporadic.Fi24.rAction

theorem p1_lt : p1 < 306936 := by decide +kernel

theorem p2_lt : p2 < 306936 := by decide +kernel

@[expose] noncomputable def P1 : Fin 306936 := ⟨p1, p1_lt⟩

@[expose] noncomputable def P2 : Fin 306936 := ⟨p2, p2_lt⟩

theorem wcs_eq : wcs = (List.range 24).map wc := by decide +kernel

theorem mem_wcs {w : List ℕ} (hw : w ∈ wcs) : ∃ i : Fin 24, w = wc i.val := by
  rw [wcs_eq, List.mem_map] at hw
  obtain ⟨n, hn, rfl⟩ := hw
  exact ⟨⟨n, List.mem_range.1 hn⟩, rfl⟩

theorem wc_mem (i : Fin 24) : wc i.val ∈ wcs := by
  rw [wcs_eq]
  exact List.mem_map.2 ⟨i.val, List.mem_range.2 i.isLt, rfl⟩

theorem rec_eq (a b : List ℕ) : ∀ l : List (List ℕ),
    List.rec (motive := fun _ => List (List ℕ)) [a, b] (fun w _ ih => dW w :: ih) l =
      l.map dW ++ [a, b]
  | [] => rfl
  | w :: l => by
    change dW w :: List.rec (motive := fun _ => List (List ℕ)) [a, b]
      (fun w _ ih => dW w :: ih) l = _
    rw [rec_eq a b l]
    rfl

theorem cw_eq : cw = wcs.map dW ++ [c1, c2] := rec_eq c1 c2 wcs

theorem recF_eq : ∀ l : List ℕ,
    List.rec (motive := fun _ => List (List ℕ)) List.nil
      (fun i _ ih => prodC [wc (nat_lit 0), wc i] :: ih) l = l.map fun i => prodC [wc 0, wc i]
  | [] => rfl
  | i :: l => by
    change prodC [wc 0, wc i] :: List.rec (motive := fun _ => List (List ℕ)) List.nil
      (fun i _ ih => prodC [wc (nat_lit 0), wc i] :: ih) l = _
    rw [recF_eq l]
    rfl

theorem fcs_eq : fcs = fI.map fun i => prodC [wc 0, wc i] := recF_eq fI

theorem fI_lt : ∀ i ∈ fI, i < 24 := by decide +kernel

theorem pp_length : (pp.map Prod.fst).length = 4 := by decide +kernel

theorem sig1_eq : sig1 = 1024 := by decide +kernel

theorem z_eq : CFSG.KD.Fi24E.z = 504 := by decide +kernel

theorem cP_c1_root : cP NW NT [0] 0 = p1 := by decide +kernel

theorem cP_c2_root : cP NW NT [3] 0 = p2 := by decide +kernel

abbrev Acts (g : R) (cs : List ℕ) : Prop := ∀ x : Fin 306936, (g • x).val = cP NW NT cs x.val

theorem acts_one : Acts 1 [] := fun x => by
  rw [one_smul]
  rfl

theorem Acts.mul {g h : R} {cs ds : List ℕ} (hg : Acts g cs) (hh : Acts h ds) :
    Acts (g * h) (cs ++ ds) := fun x => by
  rw [mul_smul, hg, hh, cP_append]

theorem acts_flatten {S : Set R} {ws : List (List ℕ)} (hS : ∀ w ∈ ws, ∃ g ∈ S, Acts g w) :
    ∀ l : List (List ℕ), (∀ w ∈ l, w ∈ ws) → ∃ g ∈ Subgroup.closure S, Acts g l.flatten
  | [], _ => ⟨1, one_mem _, acts_one⟩
  | w :: l, hl => by
    obtain ⟨g, hg, hgw⟩ := hS w (hl w List.mem_cons_self)
    obtain ⟨h, hh, hhl⟩ := acts_flatten hS l fun w' hw' => hl w' (List.mem_cons_of_mem _ hw')
    refine ⟨g * h, mul_mem (Subgroup.subset_closure hg) hh, ?_⟩
    rw [List.flatten_cons]
    exact hgw.mul hhl

theorem acts_inW {S : Set R} {ws : List (List ℕ)} (hS : ∀ w ∈ ws, ∃ g ∈ S, Acts g w)
    {v : List ℕ} (hv : InW ws v) : ∃ g ∈ Subgroup.closure S, Acts g v := by
  obtain ⟨l, hl, rfl⟩ := hv
  exact acts_flatten hS l hl

@[expose] noncomputable def sigF : Finset (Fin 306936) :=
  Finset.univ.filter fun x => ∀ i : Fin 24, (bbar i • x = x ↔ bbar i • P1 = P1)

@[expose] noncomputable def stabB : Subgroup R := fi24EB ⊓ MulAction.stabilizer R P1

open scoped Classical in
@[expose] noncomputable def orbF : Finset (Fin 306936) :=
  Finset.univ.filter fun x => ∃ b ∈ fi24EB, b • P1 = x

variable (hB : Bridge)
include hB

theorem acts_bbar (i : Fin 24) : Acts (bbar i) (dW (wc i.val)) :=
  CFSG.KD.Fi24Oct.Group.cls_bbar_val hB i

theorem acts_c1 : Acts (cls P1) c1 := fun k => by
  have e : wordElt [0] • CFSG.Sporadic.Fi24.root = P1 :=
    Fin.ext (by rw [root_val [0] hB (by decide)]; exact cP_c1_root)
  rw [← e]
  exact cls_word hB (W := [0]) (by decide) k

theorem acts_c2 : Acts (cls P2) c2 := fun k => by
  have e : wordElt [3] • CFSG.Sporadic.Fi24.root = P2 :=
    Fin.ext (by rw [root_val [3] hB (by decide)]; exact cP_c2_root)
  rw [← e]
  exact cls_word hB (W := [3]) (by decide) k

theorem acts_members : ∀ w ∈ wcs.map dW, ∃ g ∈ Set.range bbar, Acts g w := by
  intro w hw
  obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
  obtain ⟨i, rfl⟩ := mem_wcs hw'
  exact ⟨bbar i, ⟨i, rfl⟩, acts_bbar hB i⟩

theorem acts_vC (v : ℕ) : ∃ g ∈ fi24EB, Acts g (vC wcs v) :=
  acts_inW (acts_members hB) (vC_inW wcs v)

theorem acts_cw : ∀ w ∈ cw, ∃ g ∈ Set.range bbar ∪ {cls P1, cls P2}, Acts g w := by
  intro w hw
  rw [cw_eq, List.mem_append] at hw
  rcases hw with hw | hw
  · obtain ⟨g, hg, hgw⟩ := acts_members hB w hw
    exact ⟨g, Or.inl hg, hgw⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨cls P1, Or.inr (Set.mem_insert _ _), acts_c1 hB⟩
    · exact ⟨cls P2, Or.inr (Set.mem_insert_of_mem _ rfl), acts_c2 hB⟩

theorem sig_iff (x y : Fin 306936) :
    (∀ w ∈ wcs, (cP NW NT (dW w) x.val = x.val ↔ cP NW NT (dW w) y.val = y.val)) ↔
      ∀ i : Fin 24, (bbar i • x = x ↔ bbar i • y = y) := by
  constructor
  · intro h i
    have e := h _ (wc_mem i)
    rw [← acts_bbar hB, ← acts_bbar hB, ← Fin.ext_iff, ← Fin.ext_iff] at e
    exact e
  · intro h w hw
    obtain ⟨i, rfl⟩ := mem_wcs hw
    rw [← acts_bbar hB, ← acts_bbar hB, ← Fin.ext_iff, ← Fin.ext_iff]
    exact h i

omit hB in
theorem smul_comm_of {k g : R} (hc : k * g = g * k) (x : Fin 306936) : k • g • x = g • k • x := by
  rw [← mul_smul, hc, mul_smul]

theorem acts_pair (i : Fin 24) : Acts (bbar 0 * bbar i) (prodC [wc 0, wc i.val]) := fun x => by
  rw [cP_prodC, cP_prodC, mul_smul, acts_bbar hB 0, acts_bbar hB i]
  rfl

theorem fixPairs (q : Fin 306936) (hq : ∀ i, (bbar 0 * bbar i) • q = q) : ∃ k, bbarPt k = q := by
  have hfx : fixAllOK NW NT fcs (plOf pts) = true := Ck.fx_t
  have hm := fixAllOK_spec CFSG.KD.Fi24ThreeO.vn hfx q.isLt fun cs hcs => by
    rw [fcs_eq, List.mem_map] at hcs
    obtain ⟨i, hi, rfl⟩ := hcs
    rw [← acts_pair hB ⟨i, fI_lt i hi⟩, hq]
  obtain ⟨n, hn, hnq⟩ := List.mem_iff_getElem.1 ((testBit_plOf _ _).1 hm)
  have hn24 : n < 24 := hn
  refine ⟨⟨n, hn24⟩, Fin.ext ?_⟩
  change CFSG.Sporadic.Fi24.Native.bbarData[n]! = q.val
  rw [← CFSG.KD.Fi24Oct.Group.pts_eq n hn24, nthO_eq pts n hn, hnq]

theorem acts_z : Acts (bbar 0 * bbar 3 * bbar 13 * bbar 15) zc := fun x => by
  have e : zc = dW (wc 0) ++ (dW (wc 3) ++ (dW (wc 13) ++ (dW (wc 15) ++ []))) := prodC_eq _
  rw [e, cP_append, cP_append, cP_append, cP_append, mul_smul, mul_smul, mul_smul,
    acts_bbar hB 0, acts_bbar hB 3, acts_bbar hB 13, acts_bbar hB 15]
  rfl

theorem fixZ : Nat.card {k : Fin 306936 // (bbar 0 * bbar 3 * bbar 13 * bbar 15) • k = k} =
    504 := by
  have hzz : Fi24FixP.fixOK (plC NW NT) zc CFSG.KD.Fi24E.z = true := Ck.zz_t
  have h := fixOK_cP_spec CFSG.KD.Fi24ThreeO.vn hzz
  rw [z_eq] at h
  rw [← h, Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.card_map Fin.valEmbedding]
  refine congrArg Finset.card ?_
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply, Finset.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.isLt, by rw [← acts_z hB, hy]⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, Fin.ext (by rw [acts_z hB]; exact h), rfl⟩

theorem eq_one_of_fix {k : R} (hb : ∀ i, k * bbar i = bbar i * k) (h1 : k • P1 = P1)
    (h2 : k • P2 = P2) : k = 1 := by
  have hS : ∀ y ∈ Set.range bbar ∪ {cls P1, cls P2}, k * y = y * k := by
    rintro y (⟨i, rfl⟩ | hy)
    · exact hb i
    · rcases hy with rfl | hy
      · exact comm_cls_of_smul h1
      · rw [Set.mem_singleton_iff.1 hy]
        exact comm_cls_of_smul h2
  apply CFSG.Sporadic.Fi24.eq_one_of_smul_eq
  intro x
  have hcv : covW NW NT cw cov (plOf [p1]) 0 = true := Ck.cv_t
  rcases covW_spec CFSG.KD.Fi24ThreeO.vn hcv x.isLt with h | ⟨v, hv, hx⟩
  · exact absurd h (by rw [Nat.zero_testBit]; decide)
  · obtain ⟨g, hg, hgv⟩ := acts_inW (acts_cw hB) hv
    have hp : g • x = P1 := Fin.ext (by
      rw [hgv]
      exact List.mem_singleton.1 ((testBit_plOf _ _).1 hx))
    apply MulAction.injective g
    change g • k • x = g • x
    rw [← smul_comm_of (comm_of_mem_closure hS hg), hp, h1]

theorem pass_of {k : R} (hb : ∀ i, k * bbar i = bbar i * k) (h1 : k • P1 = P1) :
    ∃ v, ((k • P2).val, v) ∈ pp := by
  have hsg : sigOK NW NT wcs p1 p2 c1 tv pp sig1 = true := Ck.sg_t
  refine (sigOK_spec CFSG.KD.Fi24ThreeO.vn p1_lt p2_lt hsg).2.1 _ (k • P2).isLt ?_ ?_
  · refine (sig_iff hB (k • P2) P2).2 fun i => ?_
    rw [← smul_comm_of (hb i), smul_left_cancel_iff]
  · intro t _
    obtain ⟨u, hu, hut⟩ := acts_vC hB t
    have hc1 := comm_cls_of_smul h1
    have key : ∀ y : Fin 306936, FX NW NT c1 y.val ↔ cls P1 • y = y := fun y => by
      rw [FX, ← acts_c1 hB, ← Fin.ext_iff]
      exact ⟨fun h => h.2, fun h => ⟨y.isLt, h⟩⟩
    have hp2 : p2 = P2.val := rfl
    rw [← hut, hp2, ← hut, key, key, smul_comm_of (comm_fi24EB hb hu).symm,
      ← smul_comm_of hc1, smul_left_cancel_iff]

theorem card_sigF : sigF.card = 1024 := by
  have hsg : sigOK NW NT wcs p1 p2 c1 tv pp sig1 = true := Ck.sg_t
  have h := (sigOK_spec CFSG.KD.Fi24ThreeO.vn p1_lt p2_lt hsg).1
  rw [sig1_eq] at h
  rw [← h, ← Finset.card_map Fin.valEmbedding]
  refine congrArg Finset.card ?_
  ext x
  simp only [sigF, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply, Finset.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.isLt, (sig_iff hB y P1).2 hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, (sig_iff hB ⟨x, hx⟩ P1).1 h, rfl⟩

theorem mem_sigF {h : R} (hb : ∀ i, h * bbar i = bbar i * h) : h • P1 ∈ sigF := by
  simp only [sigF, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i
  rw [← smul_comm_of (hb i), smul_left_cancel_iff]

theorem card_stabB_le : Nat.card stabB ≤ 4 := by
  have hB' : ∀ e : stabB, (e : R) ∈ fi24EB := fun e => (Subgroup.mem_inf.1 e.2).1
  have hfix : ∀ e : stabB, (e : R) • P1 = P1 := fun e =>
    MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 e.2).2
  let f : stabB → (pp.map Prod.fst).toFinset := fun e =>
    ⟨((e : R) • P2).val, List.mem_toFinset.2 (by
      obtain ⟨v, hv⟩ := pass_of hB (fi24EB_comm (hB' e)) (hfix e)
      exact List.mem_map.2 ⟨_, hv, rfl⟩)⟩
  have hf : Function.Injective f := by
    intro e e' hee
    have hv : (e : R) • P2 = (e' : R) • P2 := Fin.ext (congrArg Subtype.val hee)
    have h1 : (e : R)⁻¹ * e' = 1 := by
      refine eq_one_of_fix hB (fun i => Commute.mul_left
        (fi24EB_comm (fi24EB.inv_mem (hB' e)) i) (fi24EB_comm (hB' e') i)) ?_ ?_
      · rw [mul_smul, hfix e', inv_smul_eq_iff, hfix e]
      · rw [mul_smul, ← hv, inv_smul_smul]
    exact Subtype.ext (inv_mul_eq_one.1 h1)
  calc Nat.card stabB ≤ Nat.card (pp.map Prod.fst).toFinset := Nat.card_le_card_of_injective f hf
    _ ≤ 4 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, ← pp_length]
      exact List.toFinset_card_le _

theorem orbF_sub : orbF ⊆ sigF := by
  intro x hx
  simp only [orbF, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  exact mem_sigF hB (fi24EB_comm hb)

theorem card_orbF : orbF.card = 1024 ∧ Nat.card fi24EB = 4096 := by
  have hcard := CFSG.Perm.card_eq_orbit_mul fi24EB stabB P1 inf_le_left
    (fun l hl => MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hl).2)
    (fun h hh hfix => Subgroup.mem_inf.2 ⟨hh, hfix⟩)
  have horb : Nat.card (MulAction.orbit fi24EB P1) = orbF.card := by
    have hset : MulAction.orbit fi24EB P1 = (orbF : Set (Fin 306936)) := by
      ext x
      simp only [orbF, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
        MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨⟨b, hb⟩, rfl⟩
        exact ⟨b, hb, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨⟨b, hb⟩, rfl⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hle : orbF.card ≤ 1024 := card_sigF hB ▸ Finset.card_le_card (orbF_sub hB)
  have hge := le_card_fi24EB
  have hst := card_stabB_le hB
  rw [hcard, horb] at hge ⊢
  interval_cases hs : Nat.card stabB <;> omega

theorem cent {h : R} (hb : ∀ i, h * bbar i = bbar i * h) : h ∈ fi24EB := by
  have hin : h • P1 ∈ orbF := by
    by_contra hn
    have hsub : orbF ⊆ sigF.erase (h • P1) := fun x hx =>
      Finset.mem_erase.2 ⟨fun e => hn (e ▸ hx), orbF_sub hB hx⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (mem_sigF hB hb), card_sigF hB, (card_orbF hB).1] at this
    omega
  simp only [orbF, Finset.mem_filter, Finset.mem_univ, true_and] at hin
  obtain ⟨y, hy, hyh⟩ := hin
  have hb₁ : ∀ i, y⁻¹ * h * bbar i = bbar i * (y⁻¹ * h) := fun i =>
    Commute.mul_left (fi24EB_comm (fi24EB.inv_mem hy) i) (hb i)
  have hf₁ : (y⁻¹ * h) • P1 = P1 := by rw [mul_smul, ← hyh, inv_smul_smul]
  obtain ⟨v, hv⟩ := pass_of hB hb₁ hf₁
  have hsg : sigOK NW NT wcs p1 p2 c1 tv pp sig1 = true := Ck.sg_t
  obtain ⟨hv1, hv2⟩ := (sigOK_spec CFSG.KD.Fi24ThreeO.vn p1_lt p2_lt hsg).2.2 _ hv
  obtain ⟨e, he, het⟩ := acts_vC hB v
  have he1 : e • P1 = P1 := Fin.ext (by rw [het]; exact hv1)
  have he2 : e • P2 = (y⁻¹ * h) • P2 := Fin.ext (by rw [het]; exact hv2)
  have h₂ : e⁻¹ * (y⁻¹ * h) = 1 := by
    refine eq_one_of_fix hB (fun i => Commute.mul_left (fi24EB_comm (fi24EB.inv_mem he) i)
      (hb₁ i)) ?_ ?_
    · rw [mul_smul, hf₁, inv_smul_eq_iff, he1]
    · rw [mul_smul, ← he2, inv_smul_smul]
  have e' : h = y * e := by
    rw [inv_mul_eq_one.1 h₂, mul_inv_cancel_left]
  rw [e']
  exact fi24EB.mul_mem hy he

theorem facts_of : Fi24EFacts :=
  ⟨fun _ hb => cent hB hb, (card_orbF hB).2, fixPairs hB, fixZ hB⟩

end CFSG.KD.Fi24E.Group

end
