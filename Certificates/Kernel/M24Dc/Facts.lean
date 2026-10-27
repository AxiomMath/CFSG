
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Facts
import Certificates.Kernel.M24Dc.Final
import Certificates.Kernel.M24Dc.Idx3
import Certificates.Kernel.M24Dc.E64Final
import Certificates.Kernel.M24Dc.T3J4
import Certificates.Kernel.M24Dc.KG7249
import CFSG.Certificates.Kernel.M24QSpan
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Dc
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Base
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
import CFSG.Quasithin.EmptyFaithful.S151S9TM24Base
import CFSG.Quasithin.EmptyFaithful.S151S9TLat
import CFSG.Blueprint.NativeSporadic
import CFSG.Quasithin.Vol2.KGFactE64M24Base
import CFSG.Quasithin.Vol2.Ch12Sec5KGM24Base
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Base

set_option maxRecDepth 100000

namespace CFSG.KD.M24Dc

open CFSG.Quasithin.H13.S125KG.M24

theorem kg7249K :
    chkXK () = true ∧ chkAlphaK () = true ∧ chkKK () = true ∧ chkQK () = true ∧
      chkVWK () = true ∧ latCheckK () = true :=
  ⟨chkXK_ok, chkAlphaK_ok, chkKK_ok, chkQK_of_chkQF chkQF_ok, chkVWK_ok, latCheckK_ok⟩

end CFSG.KD.M24Dc

namespace CertificateChecks.M24F

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m24a m24b card_M24 m24_hyp)
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.S151S9T (m24Incl m24Wit Idx3Wit idx3Model_of_lat_incl m24_centre)

theorem m24_spec : M24LatSpec :=
  ⟨M24K.m24K_membersOK CFSG.KD.M24Dc.facts, M24K.m24K_stab CFSG.KD.M24Dc.facts,
    M24K.m24K_comp CFSG.KD.M24Dc.facts, M24K.m24K_o2OK CFSG.KD.M24Dc.facts,
    CFSG.KD.M24Dc.facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1, CFSG.KD.M24Dc.facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

section Lat

variable [M24Lat]

theorem incl_iff {j jj : ℕ} (hj : j < 13) (hjj : jj < 13) :
    m24Ctx.Y j ≤ m24Ctx.Y jj ↔ jj ∈ m24Incl[j]! := by
  rw [m24Ctx.Y_le_iff (by rw [m24_J]; exact hj) (by rw [m24_J]; exact hjj)]
  exact CFSG.KD.M24Dc.m24K_check.2 j hj jj hjj

theorem incl : M24InclFact := fun j hj jj hjj => incl_iff hj hjj

theorem idx3 : M24Idx3Fact := by
  intro _
  obtain ⟨z₀, hz2, hZ, hzT⟩ := m24_centre
  have hok : m24Wit.Ok 24 m24Ctx.A.act m24Ctx.Δ m24Ctx.D (tab 24 z₀).toArray := by
    rw [hzT]
    exact CFSG.KD.M24Dc.m24K_check.1
  have hL : m24Ctx.D.Om.map (fun o => o.lbl.size) =
      #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9] := m24_Om_map
  have hN : m24Ctx.D.O.lbl.size = 239085 := m24_O_size
  have hfin : ∀ j < 13, (#[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9] : Array ℕ)[j]! = 3 →
      j ≠ 8 → ¬ m24Wit.czv[j]! = true → 1 ∉ m24Incl[j]! := by decide
  refine idx3Model_of_lat_incl m24Ctx m24_S_sylow hz2 hZ m24Wit hok hL (q := 1) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_
  · decide
  · decide
  · rw [hN]
    decide
  · decide
  · decide
  · rw [hN]
    decide
  · exact (incl_iff (by decide) (by decide)).mpr (by decide)
  · intro j hj hj3 hne
    have hj13 : j < 13 := by simpa using hj
    by_cases hc : m24Wit.czv[j]! = true
    · exact Or.inl hc
    · exact Or.inr fun hle => hfin j hj13 hj3 hne hc ((incl_iff hj13 (by decide)).mp hle)

theorem cen : M24CenFact := by
  intro _ z₀ hz
  obtain ⟨z₁, -, hZ, hzT⟩ := m24_centre
  have e : z₀ = z₁ := CFSG.Quasithin.H13.S125KG.M24.eq_of_tab_eq (by
    have h := congrArg Array.toList (hz.trans hzT.symm)
    simpa using h)
  subst e
  have hok : m24Wit.Ok 24 m24Ctx.A.act m24Ctx.Δ m24Ctx.D (tab 24 z₀).toArray := by
    rw [hzT]
    exact CFSG.KD.M24Dc.m24K_check.1
  have hz₀ : z₀ ∈ CFSG.Quasithin.centerOf m24Ctx.S := hZ ▸ Subgroup.mem_zpowers z₀
  exact ((Idx3Wit.sound m24Ctx hz₀ m24Wit hok).2 4 (by rw [m24_J]; norm_num)).mp (by decide)

open CFSG.Quasithin.H13.KGInsp CFSG.Quasithin.H13.KGE64 in
theorem e64 : M24E64Fact := by
  intro _ j hj
  have hj13 : j < 13 := by omega
  have hjJ : j < m24Ctx.J := by rw [m24_J]; exact hj13
  have hodd : m24Ctx.D.Om[j]!.lbl.size % 2 = 1 := by
    change m24LatK.Om[j]!.lbl.size % 2 = 1
    rw [m24_Om_size j hj13]
    rcases hj with rfl | rfl | rfl | rfl <;> rfl
  have h49 : ¬ 49 ∣ Nat.card (m24Ctx.Y j) := by
    rw [m24_member_card j hj13]
    rcases hj with rfl | rfl | rfl | rfl <;> decide
  have hLt : (m24LatK.sTabs ++ m24LatK.mt[j]!).toArray =
      (genTabs 24 (m24Ctx.sg ++ m24Ctx.gens j)).toArray := by
    rw [m24Ctx.Y_letters hjJ]
    rfl
  have hB : ∀ b ∈ List.range 24, b < 24 := fun b hb => List.mem_range.mp hb
  have hcert : m24E64K := CFSG.KD.M24Dc.e64K
  unfold m24E64K at hcert
  have ho2 := m24_o2_card j hj13
  rcases hj with rfl | rfl | rfl | rfl
  · refine member_ok_of_check m24Ctx hjJ hodd h49 hB base_of_faithful _ (fun x hx => hx)
      _ (by rw [hLt, genTabs_size]) (by rw [hLt]; exact genTabs_hel _) m24E64Y1 m24E64O1
      (by rw [ho2]; rfl) hcert.1
  · refine member_ok_of_check m24Ctx hjJ hodd h49 hB base_of_faithful _ (fun x hx => hx)
      _ (by rw [hLt, genTabs_size]) (by rw [hLt]; exact genTabs_hel _) m24E64Y2 m24E64O2
      (by rw [ho2]; rfl) hcert.2.1
  · refine member_ok_of_check m24Ctx hjJ hodd h49 hB base_of_faithful _ (fun x hx => hx)
      _ (by rw [hLt, genTabs_size]) (by rw [hLt]; exact genTabs_hel _) m24E64Y4 m24E64O4
      (by rw [ho2]; rfl) hcert.2.2.1
  · refine member_ok_of_check m24Ctx hjJ hodd h49 hB base_of_faithful _ (fun x hx => hx)
      _ (by rw [hLt, genTabs_size]) (by rw [hLt]; exact genTabs_hel _) m24E64Y6 m24E64O6
      (by rw [ho2]; rfl) hcert.2.2.2

open CFSG.Quasithin.H13.KGT3J4 in
theorem tab_y : (tab 24 (wordElt m24a m24b t3yWord)).toArray = t3yTab := by
  have hel : ∀ l < (#[m24a, m24b] : Array ↥CFSG.Blueprint.NativeSporadic.M24).size,
      (#[m24ta.toArray, m24tb.toArray] : Array (Array ℕ)).getD l #[] =
        (tab 24 ((#[m24a, m24b] : Array ↥CFSG.Blueprint.NativeSporadic.M24).getD l 1)).toArray := by
    intro l hl
    have hl' : l < 2 := by simpa using hl
    interval_cases l
    · exact m24_ta.symm
    · exact m24_tb.symm
  have hw : ∀ l ∈ t3yWord, l < 2 := by decide +kernel
  exact (wordTabA_eq (n := 24) #[m24a, m24b] #[m24ta.toArray, m24tb.toArray] hel t3yWord
    fun l hl => by simpa using hw l hl).symm

open CFSG.Quasithin.H13.KGT3J4 in
theorem t3j4 : M24T3J4Fact := by
  intro _ c hc j hj hcard hmem
  have hjJ : j < m24Ctx.J := by rw [m24_J]; exact hj
  have hsize : m24LatK.Om[j]!.lbl.size = 9 := by
    have h1 := m24Ctx.Y_card hjJ
    rw [hcard] at h1
    have hk : m24Ctx.k = 10 := rfl
    rw [hk] at h1
    have h2 : m24Ctx.D.Om[j]!.lbl.size = 9 := by omega
    exact h2
  set y := wordElt m24a m24b t3yWord
  obtain ⟨x, hx, hlab⟩ := (m24Ctx.Y_mem_iff hjJ _).mp hmem
  have key : codeSetAct 24 t3yTab m24LatK.Om[j]!.lbl[x]! = codeSetAct 24 t3cTab t3yLab := by
    have e1 := lab_mul m24Ctx.hlaw m24Ctx.hΔ y (y⁻¹ * c * y)
    have e2 := lab_mul m24Ctx.hlaw m24Ctx.hΔ c y
    have e3 : y * (y⁻¹ * c * y) = c * y := by group
    have hct : (tab 24 c).toArray = t3cTab := by rw [hc]; rfl
    have hly : lab 24 m24Ctx.A m24Ctx.Δ y = t3yLab := by
      change m24Ctx.A.act (tab 24 y).toArray m24Ctx.Δ = _
      rw [tab_y]
      rfl
    rw [e3, e2, hlab, tab_y, hly, hct] at e1
    exact e1.symm
  have hgens := CFSG.KD.M24Dc.t3j4K j hj hsize ⟨x, hx, key⟩
  exact (m24Ctx.Y_le_iff hjJ (by rw [m24_J]; norm_num)).mpr hgens

open CFSG.Quasithin.H13.S125KG.M24

theorem mem_Y_iff_inYK {j : ℕ} (hj : j < 13) (w : List ℕ) :
    elt w ∈ m24Ctx.Y j ↔ inYK j w = true := by
  have hJ : j < m24Ctx.J := by rw [m24_J]; exact hj
  rw [m24Ctx.Y_mem_iff hJ]
  change (∃ x < m24LatK.Om[j]!.lbl.size,
      lab 24 (codeSetLab 24) m24Delta (elt w) = m24LatK.Om[j]!.lbl[x]!) ↔ _
  rw [lab_elt, inYK, Array.contains_iff_mem, Array.mem_iff_getElem]
  constructor
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, by rw [e, getElem!_pos _ x hx]⟩
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, by rw [getElem!_pos _ x hx, e]⟩

theorem mem_S_iff (w : List ℕ) : elt w ∈ m24Ctx.S ↔ labW w = m24Delta := by
  change elt w ∈ stab m24Ctx.hlaw m24Ctx.hΔ ↔ _
  rw [mem_stab]
  exact (lab_elt w).symm ▸ Iff.rfl

theorem gens_eq {j : ℕ} {w : List ℕ} (h : m24LatK.mw[j]! = [w]) :
    m24Ctx.gens j = [elt w] := by
  change (m24LatK.mw[j]!).map (wordElt m24a m24b) = _
  rw [h]
  rfl

theorem ne_one_of_wTab {w : List ℕ} (h : wTab w ≠ List.range 24) : elt w ≠ 1 :=
  fun e => h (by rw [← tab_elt, e, tab_one])

theorem not_mem_of_inYK {j : ℕ} (hj : j < 13) {w : List ℕ} (h : inYK j w = false) :
    elt w ∉ m24Ctx.Y j := fun hm => by
  rw [mem_Y_iff_inYK hj, h] at hm
  exact Bool.false_ne_true hm

theorem x_facts : inYK 7 xw = true ∧
    wTab (xw ++ xw ++ xw) = List.range 24 ∧ wTab xw ≠ List.range 24 := by
  have h := CFSG.KD.M24Dc.kg7249K.1
  simp only [chkXK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    and_assoc] at h
  exact h

theorem alpha_facts :
    inYK 2 (invW y3w ++ xw ++ y3w) = false ∧ inYK 2 ([0] ++ xw ++ [0]) = false := by
  have h := CFSG.KD.M24Dc.kg7249K.2.1
  simp only [chkAlphaK, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h

theorem k_facts : inYK 2 k1w = true ∧ inYK 2 k2w = true ∧
    wTab k1w = wTab (commW (kWord c1v) (kWord c1u)) ∧
    wTab k2w = wTab (commW (kWord c2v) (kWord c2u)) ∧
    labW (w6w ++ invW (kWord kw6)) = m24Delta := by
  have h := CFSG.KD.M24Dc.kg7249K.2.2.1
  simp only [chkKK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem q_facts : (∀ q ∈ qws, inYK 2 q = true) ∧
    (∀ q ∈ qws, wTab q ∈ qTabs) ∧ List.range 24 ∈ qTabs ∧ qTabs.Nodup ∧
    (∀ f ∈ qTabs, ∀ f' ∈ qTabs, compTab f f' ∈ qTabs) ∧
    (∀ t ∈ nTabs, ∀ f ∈ qTabs, ∃ f' ∈ qTabs, compTab t f = compTab f' t) := by
  have h := CFSG.KD.M24Dc.kg7249K.2.2.2.1
  simp only [chkQK, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, decide_eq_true_eq,
    List.any_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem vw_facts : inYK 2 vw = true ∧ inYK 2 ww = true ∧
    wTab (vw ++ vw ++ vw ++ vw ++ vw ++ vw ++ vw) = List.range 24 ∧ wTab vw ≠ List.range 24 ∧
    wTab (ww ++ ww ++ ww) = List.range 24 ∧ wTab ww ≠ List.range 24 ∧
    ∀ f ∈ qTabs, f = List.range 24 ∨
      (compTab (wTab vw) f ≠ compTab f (wTab vw) ∧ compTab (wTab ww) f ≠ compTab f (wTab ww)) := by
  have h := CFSG.KD.M24Dc.kg7249K.2.2.2.2.1
  simp only [chkVWK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne, List.all_eq_true, and_assoc] at h
  exact h

theorem lat_facts : m24LatK.sTabs = m24STabs ∧
    m24LatK.mw[2]! = [w2w] ∧ m24LatK.mw[3]! = [y3w] ∧ m24LatK.mw[6]! = [w6w] := by
  have h := CFSG.KD.M24Dc.kg7249K.2.2.2.2.2
  simp only [latCheckK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.all_eq_true,
    and_assoc] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem exists_qSub : ∃ Q : Subgroup Γ, ∀ g : Γ, g ∈ Q ↔ tab 24 g ∈ qTabs := by
  obtain ⟨-, -, h1, -, hmul, -⟩ := q_facts
  have hmul' : ∀ x y : Γ, tab 24 x ∈ qTabs → tab 24 y ∈ qTabs → tab 24 (x * y) ∈ qTabs :=
    fun x y hx hy => by rw [tab_mul]; exact hmul _ hx _ hy
  have hone : tab 24 (1 : Γ) ∈ qTabs := by rw [tab_one]; exact h1
  have hpow : ∀ x : Γ, tab 24 x ∈ qTabs → ∀ n : ℕ, tab 24 (x ^ n) ∈ qTabs := by
    intro x hx n
    induction n with
    | zero => rw [pow_zero]; exact hone
    | succ n ih => rw [pow_succ]; exact hmul' _ _ ih hx
  have hinv : ∀ x : Γ, tab 24 x ∈ qTabs → tab 24 x⁻¹ ∈ qTabs := by
    intro x hx
    have e : x ^ (Nat.card Γ - 1) = x⁻¹ := eq_inv_of_mul_eq_one_left (by
      rw [← pow_succ, Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one'])
    rw [← e]
    exact hpow x hx _
  let Q : Subgroup Γ :=
    { carrier := {g | tab 24 g ∈ qTabs}
      mul_mem' := fun {x y} hx hy => hmul' x y hx hy
      one_mem' := hone
      inv_mem' := fun {x} hx => hinv x hx }
  exact ⟨Q, fun _ => Iff.rfl⟩

theorem card_qSub {Q : Subgroup Γ} (hQ : ∀ g : Γ, g ∈ Q ↔ tab 24 g ∈ qTabs) :
    Nat.card Q = 64 := by
  classical
  have hbij : Function.Bijective
      (fun g : Q => (⟨tab 24 g, (hQ g).mp g.2⟩ : {f // f ∈ qTabs})) := by
    constructor
    · intro g g' h
      exact Subtype.ext (eq_of_tab_eq (congrArg Subtype.val h))
    · rintro ⟨f, hf⟩
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hf
      exact ⟨⟨elt p, (hQ _).mpr (by rw [tab_elt]; exact hf)⟩, Subtype.ext (tab_elt p)⟩
  rw [Nat.card_eq_of_bijective _ hbij,
    Nat.card_congr (Equiv.subtypeEquivRight fun f => (List.mem_toFinset (l := qTabs)).symm),
    Nat.card_eq_finsetCard, List.toFinset_card_of_nodup q_facts.2.2.2.1]
  change (qProds.map wTab).length = 64
  rw [List.length_map, qProds, length_foldr]
  rfl

theorem qSub_le {Q : Subgroup Γ} (hQ : ∀ g : Γ, g ∈ Q ↔ tab 24 g ∈ qTabs) :
    Q ≤ m24Ctx.Y 2 := by
  intro g hg
  obtain ⟨p, hp, hpg⟩ := List.mem_map.mp ((hQ g).mp hg)
  have e : elt p = g := eq_of_tab_eq (by rw [tab_elt, hpg])
  rw [← e]
  exact elt_mem_of_mem_foldr qws
    (fun q hq => (mem_Y_iff_inYK (by norm_num) q).mpr (q_facts.1 q hq)) p hp

theorem Y2_le_normalizer {Q : Subgroup Γ} (hQ : ∀ g : Γ, g ∈ Q ↔ tab 24 g ∈ qTabs) :
    m24Ctx.Y 2 ≤ Subgroup.normalizer (Q : Set Γ) := by
  obtain ⟨hsT, hmw2, -⟩ := lat_facts
  have key : ∀ x : Γ, tab 24 x ∈ nTabs → x ∈ Subgroup.normalizer (Q : Set Γ) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    obtain ⟨f', hf', he⟩ := q_facts.2.2.2.2.2 _ hx _ ((hQ g).mp hg)
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hf'
    have e : x * g = elt p * x := eq_of_tab_eq (by rw [tab_mul, tab_mul, tab_elt]; exact he)
    rw [e, mul_inv_cancel_right]
    exact (hQ _).mpr (by rw [tab_elt]; exact hf')
  change Subgroup.closure {x | x ∈ m24Ctx.sg ++ m24Ctx.gens 2} ≤ _
  rw [Subgroup.closure_le]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · apply key
    have h1 : (tab 24 x).toArray ∈ m24Ctx.D.sTabs := by
      rw [← m24Ctx.hsg]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    have h2 : (tab 24 x).toArray ∈ m24LatK.sTabs := h1
    rw [hsT] at h2
    exact List.mem_append_left _ (List.mem_map.mpr ⟨_, h2, by simp⟩)
  · rw [gens_eq hmw2, List.mem_singleton] at hx
    rw [hx]
    apply key
    rw [tab_elt]
    exact List.mem_append_right _ (List.mem_singleton_self _)

theorem kg : M24KGFact := by
  intro _
  obtain ⟨hx7, hx3, hx1⟩ := x_facts
  obtain ⟨hα3, hαa⟩ := alpha_facts
  obtain ⟨hk1, hk2, hc1, hc2, hw6⟩ := k_facts
  obtain ⟨hv2, hw2, hv7, hv1, hw3, hw1, hfree⟩ := vw_facts
  obtain ⟨-, -, hmw3, hmw6⟩ := lat_facts
  obtain ⟨Q, hQ⟩ := exists_qSub
  refine ⟨⟨(mem_Y_iff_inYK (by norm_num) _).mpr hx7, elt_eq_one hx3, ne_one_of_wTab hx1⟩,
    ⟨not_mem_of_inYK (by norm_num) hα3, not_mem_of_inYK (by norm_num) hαa⟩,
    ⟨(mem_Y_iff_inYK (by norm_num) _).mpr hk1, (mem_Y_iff_inYK (by norm_num) _).mpr hk2,
      eq_of_tab_eq (by rw [tab_elt, tab_elt]; exact hc1),
      eq_of_tab_eq (by rw [tab_elt, tab_elt]; exact hc2), (mem_S_iff _).mpr hw6⟩,
    ⟨Q, card_qSub hQ, qSub_le hQ, Y2_le_normalizer hQ, fun g hg => ?_⟩,
    ⟨(mem_Y_iff_inYK (by norm_num) _).mpr hv2, (mem_Y_iff_inYK (by norm_num) _).mpr hw2,
      elt_eq_one hv7, ne_one_of_wTab hv1, elt_eq_one hw3, ne_one_of_wTab hw1⟩,
    gens_eq hmw3, gens_eq hmw6⟩
  rcases hfree _ ((hQ g).mp hg) with h3 | ⟨h3, h4⟩
  · exact Or.inl (eq_of_tab_eq (by rw [h3, tab_one]))
  · exact Or.inr ⟨fun he => h3 (by rw [← tab_elt, ← tab_mul, ← tab_mul, he]),
      fun he => h4 (by rw [← tab_elt, ← tab_mul, ← tab_mul, he])⟩

end Lat

end CertificateChecks.M24F

public section

namespace CertificateChecks.M24F

open CFSG.QuasithinUnique.Ch1.SporLat.M24

theorem facts :
    M24LatSpec ∧ M24InclFact ∧ M24Idx3Fact ∧ M24CenFact ∧ M24E64Fact ∧ M24T3J4Fact ∧
      M24KGFact := by
  have : M24Lat := ⟨m24_spec⟩
  exact ⟨m24_spec, fun {_} => incl, fun {_} => idx3, fun {_} => cen, fun {_} => e64,
    fun {_} => t3j4, fun {_} => kg⟩

end CertificateChecks.M24F
