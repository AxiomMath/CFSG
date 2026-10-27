module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24Check
public import CFSG.Sporadic.Schreier.M24
import Certificates.Kernel.M24Three.Checks
import Certificates.Kernel.M24Three.Checks2
import Certificates.Kernel.M24Three.Checks3
import CFSG.Certificates.Kernel.M24ThreeSound
import CFSG.Certificates.Kernel.M24ThreeWord
import CFSG.Certificates.Kernel.Spor.MulHSound
import CFSG.Certificates.Kernel.Spor.RecGroup
import CFSG.Certificates.Kernel.Spor.BaseMaskGlue
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Enum.ZCHSound
import CFSG.Certificates.Kernel.SporSch.ChainKPack
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Sporadic.SmallOddCore.CheckSpec
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.Facts
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Enum.ZChkISound
import CFSG.Certificates.Kernel.Spor.BaseMaskSound
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

set_option maxRecDepth 400000

namespace CFSG.KD.M24Three

open Subgroup CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Mathieu
open CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.KC.EnumSound CFSG.KC.OrbRow CFSG.KC.M24Three
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier

local notation "Pm" => Equiv.Perm (Fin 24)

abbrev Cn (P : ℕ) : Prop := canonK 24 5 (mask 5) (24 * 5) P = true

theorem band {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> simp_all

theorem band_iff (a b : Bool) : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> simp

theorem sz : szOK 24 5 = true := rfl

theorem cn_id : Cn idK := (CFSG.KC.BfsPin.PP.id sz).1

theorem cn_pc {P Q : ℕ} (hP : Cn P) (hQ : Cn Q) : Cn (pc P Q) :=
  CFSG.KC.BfsPin.canonK_pcomp hP hQ

theorem prep_id : PRep 24 5 idK (1 : Pm) := prep_pidn (by norm_num) (by norm_num)

theorem prep_pc {P Q : ℕ} {g h : Pm} (hP : PRep 24 5 P g) (hQ : PRep 24 5 Q h) :
    PRep 24 5 (pc P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem rep_iff {P : ℕ} {g : Pm} (hc : Cn P) :
    CFSG.Sporadic.Th.Rep 24 (tabT (unpack 24 5 P)) g ↔ PRep 24 5 P g := by
  constructor
  · intro h x
    have e := h x x.2
    rw [ap_tabT _ (unpack_lt hc), unpack_get x.2, idx_of_lt _ x.2] at e
    simpa using e
  · intro h i hi
    rw [ap_tabT _ (unpack_lt hc), unpack_get hi, idx_of_lt _ hi]
    simpa using h ⟨i, hi⟩

theorem eq_of_prep {P Q : ℕ} {g : Pm} (hP : Cn P) (hQ : Cn Q) (h1 : PRep 24 5 P g)
    (h2 : PRep 24 5 Q g) : P = Q :=
  CFSG.KS.RecGroup.eq_of_rep_eq hP hQ ((rep_iff hP).2 h1) ((rep_iff hQ).2 h2)

theorem uniq {P : ℕ} {g h : Pm} (hg : PRep 24 5 P g) (hh : PRep 24 5 P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem beq_of_one {P : ℕ} {g : Pm} (hc : Cn P) (hP : PRep 24 5 P g) (h : g = 1) :
    Nat.beq P idK = true := by
  rw [eq_of_prep hc cn_id (h ▸ hP) prep_id]
  exact Nat.beq_refl _

theorem one_of_beq {P : ℕ} {g : Pm} (hP : PRep 24 5 P g) (h : Nat.beq P idK = true) : g = 1 := by
  rw [Nat.eq_of_beq_eq_true h] at hP
  exact uniq hP prep_id

theorem beq_false_of_ne {P : ℕ} {g : Pm} (hP : PRep 24 5 P g) (h : g ≠ 1) :
    Nat.beq P idK = false := by
  cases hb : Nat.beq P idK
  · rfl
  · exact absurd (one_of_beq hP hb) h

theorem invK_spec {p q : ℕ} (h : invK p q = true) :
    Cn p ∧ Cn q ∧ permOK 24 5 (mask 5) (24 * 5) p q = true := by
  unfold invK at h
  obtain ⟨a, b⟩ := band h
  obtain ⟨c, d⟩ := band b
  exact ⟨a, c, d⟩

theorem pA : PRep 24 5 (GN 0) m24gA := by
  unfold PRep
  decide +kernel

theorem pB : PRep 24 5 (GN 1) m24gB := by
  unfold PRep
  decide +kernel

theorem el_parts : invK (GN 0) (GN 2) = true ∧ invK (GN 1) (GN 3) = true ∧
    ∀ j < 24, elK j = true := by
  have h := ch12613_el
  simp only [band_iff] at h
  exact ⟨h.1, h.2.1, allN_spec h.2.2⟩

theorem pAi : PRep 24 5 (GN 2) m24gA⁻¹ :=
  CFSG.KS.SporSch.MOC.prep_inv_of_permOK pA (invK_spec el_parts.1).2.2

theorem pBi : PRep 24 5 (GN 3) m24gB⁻¹ :=
  CFSG.KS.SporSch.MOC.prep_inv_of_permOK pB (invK_spec el_parts.2.1).2.2

noncomputable def eG (j : ℕ) : Pm := wC m24gA m24gB (WL j) (LN j)

theorem elK_spec {j : ℕ} (hj : j < 24) :
    (Cn (EL j) ∧ Cn (EI j) ∧ permOK 24 5 (mask 5) (24 * 5) (EL j) (EI j) = true) ∧
      EL j = wperm 24 5 (mask 5) (GN 0) (GN 1) (GN 2) (GN 3) (WL j) (LN j) := by
  have h := el_parts.2.2 j hj
  unfold elK at h
  obtain ⟨a, b⟩ := band h
  exact ⟨invK_spec a, Nat.eq_of_beq_eq_true b⟩

theorem pEL {j : ℕ} (hj : j < 24) : PRep 24 5 (EL j) (eG j) := by
  rw [(elK_spec hj).2]
  exact wperm_prep_code (by norm_num) (by norm_num) pA pAi pB pBi

theorem pEI {j : ℕ} (hj : j < 24) : PRep 24 5 (EI j) (eG j)⁻¹ :=
  CFSG.KS.SporSch.MOC.prep_inv_of_permOK (pEL hj) (elK_spec hj).1.2.2

theorem cEL {j : ℕ} (hj : j < 24) : Cn (EL j) := (elK_spec hj).1.1

theorem cEI {j : ℕ} (hj : j < 24) : Cn (EI j) := (elK_spec hj).1.2.1

theorem wC_memM (W len : ℕ) : wC m24gA m24gB W len ∈ NativeSporadic.M24 := by
  rw [m24_eq]
  exact wC_mem _ _ _ _

theorem eG_mem (j : ℕ) : eG j ∈ NativeSporadic.M24 := wC_memM _ _

theorem wp_eq (W L q : ℕ) (hq : q < 24) :
    wp W L q = (wC m24gA m24gB W L ⟨q, hq⟩ : ℕ) :=
  wpt_prep_code pA pAi pB pBi q hq

theorem wl_eq (W k : ℕ) : wl W k = W / 4 ^ k % 4 := by
  unfold wl
  change (W >>> (k <<< 1)) &&& 3 = _
  have e : k <<< 1 = 2 * k := by
    rw [Nat.shiftLeft_eq]
    ring
  rw [e, Nat.shiftRight_eq_div_pow, pow_mul]
  have := Nat.and_two_pow_sub_one_eq_mod (W / (2 ^ 2) ^ k) 2
  simpa using this

theorem wC_cons {c : ℕ} (hc : c < 4) (W : ℕ) :
    ∀ k, wC m24gA m24gB (c + 4 * W) (k + 1) = letC m24gA m24gB c * wC m24gA m24gB W k := by
  intro k
  induction k with
  | zero =>
    have e : wl (c + 4 * W) 0 = c := by
      rw [wl_eq]
      omega
    simp only [wC, e, one_mul, mul_one]
  | succ k ih =>
    have e : wl (c + 4 * W) (k + 1) = wl W k := by
      rw [wl_eq, wl_eq, pow_succ, mul_comm (4 ^ k) 4, ← Nat.div_div_eq_div_mul]
      congr 2
      omega
    rw [wC, ih, e, mul_assoc]
    rfl

theorem codeZ_lt (l : ℤ) : codeZ l < 4 := by
  unfold codeZ
  split_ifs <;> omega

theorem letC_0 {A : Type} [Group A] (ga gb : A) : letC ga gb 0 = ga := rfl
theorem letC_1 {A : Type} [Group A] (ga gb : A) : letC ga gb 1 = gb := rfl
theorem letC_2 {A : Type} [Group A] (ga gb : A) : letC ga gb 2 = ga⁻¹ := rfl
theorem letC_3 {A : Type} [Group A] (ga gb : A) : letC ga gb 3 = gb⁻¹ := rfl

theorem letC_code (l : ℤ) : letC m24gA m24gB (codeZ l) = letG l := by
  unfold codeZ letG
  by_cases h1 : l = 1
  · subst h1
    simpa using letC_0 m24gA m24gB
  by_cases h2 : l = 2
  · subst h2
    simpa using letC_1 m24gA m24gB
  by_cases h3 : l = -1
  · subst h3
    simpa using letC_2 m24gA m24gB
  · simp only [h1, h2, h3, ↓reduceIte]
    exact letC_3 _ _

theorem wC_code : ∀ w : List ℤ, wC m24gA m24gB (codeN w) (lenN w) = wordG letG w
  | [] => by simp [wC, wordG, lenN]
  | l :: w => by
    have e1 : codeN (l :: w) = codeZ l + 4 * codeN w := rfl
    have e2 : lenN (l :: w) = lenN w + 1 := rfl
    rw [e1, e2, wC_cons (codeZ_lt l), wC_code w, letC_code]
    simp [wordG]

theorem eG_word {j : ℕ} {w : List ℤ} (h : wdK j w = true) : eG j = wordG letG w := by
  unfold wdK at h
  obtain ⟨a, b⟩ := band h
  unfold eG
  rw [Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, wC_code]

theorem wd_parts : eG 0 = wordG letG xW ∧ eG 1 = wordG letG x2W ∧ eG 12 = wordG letG ra0W ∧
    eG 13 = wordG letG ra1W ∧ eG 14 = wordG letG ra2W ∧ eG 15 = wordG letG ha0W ∧
    eG 16 = wordG letG ha1W ∧ eG 17 = wordG letG ha2W ∧ eG 18 = wordG letG rb0W ∧
    eG 19 = wordG letG rb1W ∧ eG 20 = wordG letG rb2W ∧ eG 21 = wordG letG hb0W ∧
    eG 22 = wordG letG hb1W ∧ eG 23 = wordG letG hb2W := by
  have h := ch12613_wd
  simp only [band_iff] at h
  obtain ⟨h0, h1, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩ := h
  exact ⟨eG_word h0, eG_word h1, eG_word h12, eG_word h13, eG_word h14, eG_word h15,
    eG_word h16, eG_word h17, eG_word h18, eG_word h19, eG_word h20, eG_word h21, eG_word h22,
    eG_word h23⟩

theorem sbeq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem beq_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hc : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hc) h

theorem slices {K L cnt : ℕ} {P : ℕ → Prop} (hL : 0 < L) (hc : cnt ≤ K * L)
    (h : ∀ s < K, ∀ i, Nat.mul s L ≤ i → i < Nat.mul s L + L → i < cnt → P i) :
    ∀ i < cnt, P i := by
  intro i hi
  have h1 : i / L < K := (Nat.div_lt_iff_lt_mul hL).2 (lt_of_lt_of_le hi hc)
  refine h (i / L) h1 i ?_ ?_ hi
  · change i / L * L ≤ i
    exact Nat.div_mul_le_self i L
  · change i < i / L * L + L
    have e := Nat.div_add_mod i L
    have m := Nat.mod_lt i hL
    rw [mul_comm] at e
    linarith

theorem tabs2 {G : ℕ → ℕ} (hc : ∀ j < 2, Cn (G j)) :
    TabsOK 24 5 2 G #[tabT (unpack 24 5 (G 0)), tabT (unpack 24 5 (G 1))] := by
  refine ⟨rfl, fun j hj => ⟨?_, hc j hj⟩⟩
  interval_cases j <;> rfl

theorem get2 {G : ℕ → ℕ} {l : ℕ} (hl : l < 2) :
    (#[tabT (unpack 24 5 (G 0)), tabT (unpack 24 5 (G 1))] : Array Table)[l]! =
      tabT (unpack 24 5 (G l)) := by
  interval_cases l <;> rfl

theorem hRec_get {cnt k : ℕ} {T PL : ℕ → ℕ} (hk : k < cnt) :
    (hRec 24 5 cnt T PL).1[k]! = tabT (unpack 24 5 (T k)) := by
  unfold hRec
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem hRec_sz {cnt : ℕ} {T PL : ℕ → ℕ} : (hRec 24 5 cnt T PL).1.size = cnt := by
  simp [hRec]

theorem forall2_rec {cnt : ℕ} {T PL : ℕ → ℕ} {f : Fin cnt → Pm}
    (h : ∀ k : Fin cnt, CFSG.Sporadic.Th.Rep 24 (tabT (unpack 24 5 (T k))) (f k)) :
    List.Forall₂ (CFSG.Sporadic.Th.Rep 24) (hRec 24 5 cnt T PL).1.toList (List.ofFn f) := by
  unfold hRec
  rw [Array.toList_ofFn, List.forall₂_iff_get]
  refine ⟨by simp, fun i h1 h2 => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  exact h ⟨i, by simpa using h2⟩

theorem conj_rec {H : Subgroup Pm} {t : Pm} {cnt cap X : ℕ}
    {G GI T PL POS SRT SRI HS HSI : ℕ → ℕ} {g : ℕ → Pm}
    (hg : ∀ j < 2, Cn (G j) ∧ Cn (GI j) ∧ PRep 24 5 (G j) (g j) ∧ PRep 24 5 (GI j) (g j)⁻¹ ∧
      g j ∈ H)
    (hX : Cn X) (hXt : PRep 24 5 X t) (hh : penumHdK X cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK 24 5 (mask 5) (24 * 5) true G GI 2 cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK 24 5 (mask 5) cnt T HS HSI i = true) :
    ∃ s : Finset Pm, s.card = cnt ∧ ∀ y ∈ s, ∃ h ∈ H, h * t * h⁻¹ = y := by
  obtain ⟨-, ht, hd⟩ := conjH_sound sz (tabs2 fun j hj => (hg j hj).1)
    (tabs2 fun j hj => (hg j hj).2.1) rfl hh hp hs
  have hspec := conjTreeOK_spec H (gg := g) (fun l hl => by
      have hl2 : l < 2 := hl
      rw [get2 hl2, get2 hl2]
      exact ⟨(rep_iff (hg l hl2).1).2 (hg l hl2).2.2.1,
        (rep_iff (hg l hl2).2.1).2 (hg l hl2).2.2.2.1, (hg l hl2).2.2.2.2⟩)
    ((rep_iff hX).2 hXt) ht
  have hf : ∀ k : Fin cnt, ∃ c ∈ H, CFSG.Sporadic.Th.Rep 24 (tabT (unpack 24 5 (T k)))
      (c * t * c⁻¹) := fun k => by
    have := hspec k (by rw [hRec_sz]; exact k.2)
    rwa [hRec_get k.2] at this
  choose c hcH hcR using hf
  have hnd := nodup_of_hkeysDistinct (forall2_rec (PL := PL) hcR) hd
  refine ⟨(List.ofFn fun k => c k * t * (c k)⁻¹).toFinset, ?_, fun y hy => ?_⟩
  · rw [List.toFinset_card_of_nodup hnd, List.length_ofFn]
  · rw [List.mem_toFinset, List.mem_ofFn] at hy
    obtain ⟨k, rfl⟩ := hy
    exact ⟨c k, hcH k, rfl⟩

theorem mul_rec {H : Subgroup Pm} {cnt cap : ℕ} {G GI T PL POS SRT SRI HS HSI : ℕ → ℕ}
    {g : ℕ → Pm} (hG : ∀ j < 2, G j = pidn 24 5)
    (hg : ∀ j < 2, Cn (GI j) ∧ PRep 24 5 (GI j) (g j) ∧ g j ∈ H)
    (hh : penumHdK (pidn 24 5) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK 24 5 (mask 5) (24 * 5) true G GI 2 cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK 24 5 (mask 5) cnt T HS HSI i = true) :
    ∃ f : ℕ → Pm, (∀ i < cnt, PRep 24 5 (T i) (f i) ∧ f i ∈ H) ∧
      ∀ a < cnt, ∀ b < cnt, f a = f b → a = b := by
  obtain ⟨-, ht, hd⟩ := mulH_sound sz hG (tabs2 fun j hj => (hg j hj).1) hh hp hs
  have hspec := mulTreeOK_spec (by norm_num) H (gg := g) (fun l hl => by
      have hl2 : l < 2 := hl
      rw [get2 hl2]
      exact ⟨(rep_iff (hg l hl2).1).2 (hg l hl2).2.1, (hg l hl2).2.2⟩) ht
  have hf : ∀ k : Fin cnt, ∃ c ∈ H, CFSG.Sporadic.Th.Rep 24 (tabT (unpack 24 5 (T k))) c :=
    fun k => by
      have := hspec k (by rw [hRec_sz]; exact k.2)
      rwa [hRec_get k.2] at this
  choose c hcH hcR using hf
  have hnd := nodup_of_hkeysDistinct (forall2_rec (PL := PL) hcR) hd
  have hinj := List.nodup_ofFn.1 hnd
  refine ⟨fun i => if h : i < cnt then c ⟨i, h⟩ else 1, fun i hi => ?_, fun a ha b hb e => ?_⟩
  · simp only [dif_pos hi]
    exact ⟨(rep_iff (penumPt_specH (hp i hi)).1).1 (hcR ⟨i, hi⟩), hcH _⟩
  · simp only [dif_pos ha, dif_pos hb] at e
    exact congrArg Fin.val (hinj e)

theorem card_of_inj {C : Subgroup Pm} {f : ℕ → Pm} {cnt : ℕ} (hf : ∀ i < cnt, f i ∈ C)
    (hinj : ∀ a < cnt, ∀ b < cnt, f a = f b → a = b) :
    cnt ≤ Nat.card C ∧ (Nat.card C ≤ cnt → ∀ y ∈ C, ∃ i < cnt, f i = y) := by
  classical
  set s := (Finset.range cnt).image f
  have hs : s.card = cnt := by
    rw [Finset.card_image_of_injOn (fun a ha b hb e =>
      hinj a (by simpa using ha) b (by simpa using hb) e), Finset.card_range]
  have hsub : (s : Set Pm) ⊆ (C : Set Pm) := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy
    exact hf i (Finset.mem_range.1 hi)
  have hC : Nat.card C = (C : Set Pm).ncard := Nat.card_coe_set_eq (C : Set Pm)
  have hle : s.card ≤ Nat.card C := by
    rw [hC, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  refine ⟨hs ▸ hle, fun hge y hy => ?_⟩
  have heq : (s : Set Pm) = C := Set.eq_of_subset_of_ncard_le hsub
    (by rw [Set.ncard_coe_finset, hs, ← hC]; exact hge) (Set.toFinite _)
  have hy' : y ∈ (s : Set Pm) := by
    rw [heq]
    exact hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy'
  exact ⟨i, Finset.mem_range.1 hi, rfl⟩

noncomputable def tw (l q : ℕ) : Pm :=
  wC m24gA m24gB (TW (Nat.add (Nat.mul 24 l) q)) (TL (Nat.add (Nat.mul 24 l) q))

theorem tw_mem (l q : ℕ) : tw l q ∈ NativeSporadic.M24 := wC_memM _ _

theorem tw_at {l q b v : ℕ} (hb : b < 24)
    (h : Nat.beq (wp (TW (Nat.add (Nat.mul 24 l) q)) (TL (Nat.add (Nat.mul 24 l) q)) b) v = true) :
    ((tw l q ⟨b, hb⟩ : Fin 24) : ℕ) = v := by
  have e := Nat.eq_of_beq_eq_true h
  rw [wp_eq _ _ _ hb] at e
  exact e

theorem lv0_spec {l b : ℕ} (hb : b < 24) (h : allN 24 (lv0K l b) = true) (q : Fin 24) :
    tw l q ⟨b, hb⟩ = q := by
  have e := allN_spec h q q.2
  unfold lv0K at e
  simp only [sbeq] at e
  exact Fin.ext (tw_at hb e)

theorem lv1_spec {l b p : ℕ} (hb : b < 24) (hp : p < 24) (h : allN 24 (lv1K l b p) = true)
    (q : Fin 24) (hq : (q : ℕ) ≠ p) : tw l q ⟨b, hb⟩ = q ∧ tw l q ⟨p, hp⟩ = ⟨p, hp⟩ := by
  have e := allN_spec h q q.2
  unfold lv1K at e
  rw [beq_ne hq] at e
  dsimp only at e
  simp only [sbeq] at e
  obtain ⟨e1, e2⟩ := band e
  exact ⟨Fin.ext (tw_at hb e1), Fin.ext (tw_at hp e2)⟩

theorem lv2_spec {l b p p' : ℕ} (hb : b < 24) (hp : p < 24) (hp' : p' < 24)
    (h : allN 24 (lv2K l b p p') = true) (q : Fin 24) (hq : (q : ℕ) ≠ p) (hq' : (q : ℕ) ≠ p') :
    tw l q ⟨b, hb⟩ = q ∧ tw l q ⟨p, hp⟩ = ⟨p, hp⟩ ∧ tw l q ⟨p', hp'⟩ = ⟨p', hp'⟩ := by
  have e := allN_spec h q q.2
  unfold lv2K at e
  rw [beq_ne hq] at e
  dsimp only at e
  rw [beq_ne hq'] at e
  dsimp only at e
  simp only [sbeq] at e
  obtain ⟨e1, e2⟩ := band e
  obtain ⟨e2, e3⟩ := band e2
  exact ⟨Fin.ext (tw_at hb e1), Fin.ext (tw_at hp e2), Fin.ext (tw_at hp' e3)⟩

def bs (b0 b1 b2 : Fin 24) (i : ℕ) : Fin 24 :=
  if i = 0 then b0 else if i = 1 then b1 else b2

theorem chain_le {l1 l2 b0 b1 b2 : ℕ} (h0 : b0 < 24)
    (h1 : b1 < 24) (h2 : b2 < 24) (h10 : b1 ≠ b0)
    (c0 : allN 24 (lv0K 0 b0) = true) (c1 : allN 24 (lv1K l1 b1 b0) = true)
    (c2 : allN 24 (lv2K l2 b2 b0 b1) = true) :
    Nat.card (stabB NativeSporadic.M24 (bs ⟨b0, h0⟩ ⟨b1, h1⟩ ⟨b2, h2⟩) 3) ≤ 20160 := by
  have ne : (⟨b1, h1⟩ : Fin 24) ≠ ⟨b0, h0⟩ := fun h => h10 (congrArg Fin.val h)
  have key := card_stab3_le NativeSporadic.M24 (bs ⟨b0, h0⟩ ⟨b1, h1⟩ ⟨b2, h2⟩) Finset.univ
    (Finset.univ.erase ⟨b0, h0⟩) ((Finset.univ.erase ⟨b0, h0⟩).erase ⟨b1, h1⟩) ?_ ?_ ?_
  · rw [m24_card, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨ne, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at key
    omega
  · intro x _
    exact ⟨tw 0 x, ⟨tw_mem _ _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩, lv0_spec h0 c0 x⟩
  · intro x hx
    have hx0 : (x : ℕ) ≠ b0 := fun h => (Finset.mem_erase.1 hx).1 (Fin.ext h)
    obtain ⟨s1, s0⟩ := lv1_spec h1 h0 c1 x hx0
    refine ⟨tw l1 x, ⟨tw_mem _ _, fun t ht => ?_⟩, s1⟩
    have : t = 0 := by omega
    subst this
    exact s0
  · intro x hx
    obtain ⟨hx1, hx'⟩ := Finset.mem_erase.1 hx
    have hx0 : (x : ℕ) ≠ b0 := fun h => (Finset.mem_erase.1 hx').1 (Fin.ext h)
    have hx1' : (x : ℕ) ≠ b1 := fun h => hx1 (Fin.ext h)
    obtain ⟨s2, s0, s1⟩ := lv2_spec h2 h0 h1 c2 x hx0 hx1'
    refine ⟨tw l2 x, ⟨tw_mem _ _, fun t ht => ?_⟩, s2⟩
    interval_cases t
    · exact s0
    · exact s1

theorem pt_of {j i v : ℕ} (hj : j < 24) (hi : i < 24)
    (h : Nat.beq (pg 5 (mask 5) (EL j) i) v = true) : ((eG j ⟨i, hi⟩ : Fin 24) : ℕ) = v := by
  rw [← prep_at (pEL hj) hi]
  exact Nat.eq_of_beq_eq_true h

theorem fix3_mem {j b0 b1 b2 : ℕ} (hj : j < 24) (h0 : b0 < 24) (h1 : b1 < 24) (h2 : b2 < 24)
    (h : fix3K (EL j) b0 b1 b2 = true) :
    eG j ∈ stabB NativeSporadic.M24 (bs ⟨b0, h0⟩ ⟨b1, h1⟩ ⟨b2, h2⟩) 3 := by
  unfold fix3K at h
  obtain ⟨e0, e⟩ := band h
  obtain ⟨e1, e2⟩ := band e
  refine ⟨eG_mem j, fun t ht => ?_⟩
  interval_cases t
  · exact Fin.ext (pt_of hj h0 e0)
  · exact Fin.ext (pt_of hj h1 e1)
  · exact Fin.ext (pt_of hj h2 e2)

theorem comm_mem {i j : ℕ} (hi : i < 24) (hj : j < 24) (h : cmK (EL i) (EL j) = true) :
    eG i ∈ centralizer ({eG j} : Set Pm) := by
  rw [mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact (eq22_prep h (pEL hi) (pEL hj) (pEL hj) (pEL hi)).symm

theorem bind_parts :
    (OA.G 0 = EL 8 ∧ OA.G 1 = EL 9 ∧ OA.GI 0 = EI 8 ∧ OA.GI 1 = EI 9 ∧ OA.R = EL 0 ∧
      OA.cnt = 336 ∧ penumHdK OA.R OA.cnt 2000 OA.T OA.PL = true) ∧
    (OB.G 0 = EL 10 ∧ OB.G 1 = EL 11 ∧ OB.GI 0 = EI 10 ∧ OB.GI 1 = EI 11 ∧ OB.R = EL 1 ∧
      OB.cnt = 960 ∧ penumHdK OB.R OB.cnt 2000 OB.T OB.PL = true) ∧
    (CA.G 0 = pidn 24 5 ∧ CA.G 1 = pidn 24 5 ∧ CA.GI 0 = EL 4 ∧ CA.GI 1 = EL 5 ∧
      CA.R = pidn 24 5 ∧ CA.cnt = 1080 ∧ penumHdK CA.R CA.cnt 2000 CA.T CA.PL = true) ∧
    (CB.G 0 = pidn 24 5 ∧ CB.G 1 = pidn 24 5 ∧ CB.GI 0 = EL 6 ∧ CB.GI 1 = EL 7 ∧
      CB.R = pidn 24 5 ∧ CB.cnt = 504 ∧ penumHdK CB.R CB.cnt 2000 CB.T CB.PL = true) ∧
    (S.G 0 = pidn 24 5 ∧ S.G 1 = pidn 24 5 ∧ S.GI 0 = EL 2 ∧ S.GI 1 = EL 3 ∧
      S.R = pidn 24 5 ∧ S.cnt = 27 ∧ penumHdK S.R S.cnt 100 S.T S.PL = true) ∧
    SI 0 = EI 2 ∧ SI 1 = EI 3 := by
  have h := ch12613_bind
  simp only [band_iff] at h
  have E := @Nat.eq_of_beq_eq_true
  obtain ⟨-, a1, a2, a3, a4, a5, a6, a7, -, b1, b2, b3, b4, b5, b6, b7, -, c1, c2, c3, c4, c5,
    c6, c7, -, d1, d2, d3, d4, d5, d6, d7, -, e1, e2, e3, e4, e5, e6, e7, f1, f2⟩ := h
  exact ⟨⟨E a1, E a2, E a3, E a4, E a5, E a6, a7⟩, ⟨E b1, E b2, E b3, E b4, E b5, E b6, b7⟩,
    ⟨E c1, E c2, E c3, E c4, E c5, E c6, c7⟩, ⟨E d1, E d2, E d3, E d4, E d5, E d6, d7⟩,
    ⟨E e1, E e2, E e3, E e4, E e5, E e6, e7⟩, E f1, E f2⟩

theorem fix_parts : fix3K (EL 8) 0 3 5 = true ∧ fix3K (EL 9) 0 3 5 = true ∧
    fix3K (EL 10) 0 17 13 = true ∧ fix3K (EL 11) 0 17 13 = true ∧
    eG 0 0 = 3 ∧ eG 0 3 = 5 ∧ eG 1 0 = 17 ∧ eG 1 17 = 13 := by
  have h := ch12613_fix
  simp only [band_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, Fin.ext (pt_of (by norm_num) (by norm_num) h5),
    Fin.ext (pt_of (by norm_num) (by norm_num) h6), Fin.ext (pt_of (by norm_num) (by norm_num) h7),
    Fin.ext (pt_of (by norm_num) (by norm_num) h8)⟩

theorem comm_parts : cmK (EL 4) (EL 0) = true ∧ cmK (EL 5) (EL 0) = true ∧
    cmK (EL 15) (EL 0) = true ∧ cmK (EL 16) (EL 0) = true ∧ cmK (EL 17) (EL 0) = true ∧
    cmK (EL 6) (EL 1) = true ∧ cmK (EL 7) (EL 1) = true ∧ cmK (EL 21) (EL 1) = true ∧
    cmK (EL 22) (EL 1) = true ∧ cmK (EL 23) (EL 1) = true := by
  have h := ch12613_comm
  simp only [band_iff] at h
  exact h

theorem lv_parts : allN 24 (lv0K 0 0) = true ∧ allN 24 (lv1K 1 3 0) = true ∧
    allN 24 (lv2K 2 5 0 3) = true ∧ allN 24 (lv1K 3 17 0) = true ∧
    allN 24 (lv2K 4 13 0 17) = true := by
  have h := ch12613_lv
  simp only [band_iff] at h
  exact h

#kc_forall_tree oaE_all (fun s => oaE s = true) 6 CFSG.KD.M24Three.ch12613oaE_
#kc_forall_tree oaH_all (fun s => oaH s = true) 6 CFSG.KD.M24Three.ch12613oaH_
#kc_forall_tree obE_all (fun s => obE s = true) 15 CFSG.KD.M24Three.ch12613obE_
#kc_forall_tree obH_all (fun s => obH s = true) 15 CFSG.KD.M24Three.ch12613obH_
#kc_forall_tree caE_all (fun s => caE s = true) 18 CFSG.KD.M24Three.ch12613caE_
#kc_forall_tree caH_all (fun s => caH s = true) 18 CFSG.KD.M24Three.ch12613caH_
#kc_forall_tree cbE_all (fun s => cbE s = true) 9 CFSG.KD.M24Three.ch12613cbE_
#kc_forall_tree cbH_all (fun s => cbH s = true) 9 CFSG.KD.M24Three.ch12613cbH_
#kc_forall_tree cvA_all (fun s => cvA s = true) 18 CFSG.KD.M24Three.ch12613cvA_
#kc_forall_tree cvB_all (fun s => cvB s = true) 9 CFSG.KD.M24Three.ch12613cvB_

theorem oa_pt : ∀ i < OA.cnt, penumPtK 24 5 (mask 5) (24 * 5) true OA.G OA.GI 2 OA.cnt OA.T OA.PL
    OA.POS OA.SRT OA.SRI i = true :=
  slices (K := 6) (L := 56) (by norm_num) (by decide) fun s hs _ h1 h2 hi =>
    CFSG.KS.BaseMask.penumSl_spec (oaE_all s hs) h1 h2 hi

theorem oa_hs : ∀ i < OA.cnt, hsortPtK 24 5 (mask 5) OA.cnt OA.T OA.HS OA.HSI i = true :=
  slices (K := 6) (L := 56) (by norm_num) (by decide) fun s hs i h1 h2 hi =>
    slK_spec (oaH_all s hs) i h1 h2 hi

theorem ob_pt : ∀ i < OB.cnt, penumPtK 24 5 (mask 5) (24 * 5) true OB.G OB.GI 2 OB.cnt OB.T OB.PL
    OB.POS OB.SRT OB.SRI i = true :=
  slices (K := 15) (L := 64) (by norm_num) (by decide) fun s hs _ h1 h2 hi =>
    CFSG.KS.BaseMask.penumSl_spec (obE_all s hs) h1 h2 hi

theorem ob_hs : ∀ i < OB.cnt, hsortPtK 24 5 (mask 5) OB.cnt OB.T OB.HS OB.HSI i = true :=
  slices (K := 15) (L := 64) (by norm_num) (by decide) fun s hs i h1 h2 hi =>
    slK_spec (obH_all s hs) i h1 h2 hi

theorem ca_pt : ∀ i < CA.cnt, penumPtK 24 5 (mask 5) (24 * 5) true CA.G CA.GI 2 CA.cnt CA.T CA.PL
    CA.POS CA.SRT CA.SRI i = true :=
  slices (K := 18) (L := 60) (by norm_num) (by decide) fun s hs _ h1 h2 hi =>
    CFSG.KS.BaseMask.penumSl_spec (caE_all s hs) h1 h2 hi

theorem ca_hs : ∀ i < CA.cnt, hsortPtK 24 5 (mask 5) CA.cnt CA.T CA.HS CA.HSI i = true :=
  slices (K := 18) (L := 60) (by norm_num) (by decide) fun s hs i h1 h2 hi =>
    slK_spec (caH_all s hs) i h1 h2 hi

theorem cb_pt : ∀ i < CB.cnt, penumPtK 24 5 (mask 5) (24 * 5) true CB.G CB.GI 2 CB.cnt CB.T CB.PL
    CB.POS CB.SRT CB.SRI i = true :=
  slices (K := 9) (L := 56) (by norm_num) (by decide) fun s hs _ h1 h2 hi =>
    CFSG.KS.BaseMask.penumSl_spec (cbE_all s hs) h1 h2 hi

theorem cb_hs : ∀ i < CB.cnt, hsortPtK 24 5 (mask 5) CB.cnt CB.T CB.HS CB.HSI i = true :=
  slices (K := 9) (L := 56) (by norm_num) (by decide) fun s hs i h1 h2 hi =>
    slK_spec (cbH_all s hs) i h1 h2 hi

theorem s_pt : ∀ i < S.cnt, penumPtK 24 5 (mask 5) (24 * 5) true S.G S.GI 2 S.cnt S.T S.PL
    S.POS S.SRT S.SRI i = true := fun i hi =>
  CFSG.KS.BaseMask.penumSl_spec ch12613sE (Nat.zero_le i) (by omega) hi

theorem s_hs : ∀ i < S.cnt, hsortPtK 24 5 (mask 5) S.cnt S.T S.HS S.HSI i = true := fun i hi =>
  slK_spec ch12613sH i (Nat.zero_le i) (by omega) hi

theorem primes1080 {q : ℕ} (hq : q.Prime) (h : q ∣ 1080) (h3 : q ≠ 3) : q = 2 ∨ q = 5 := by
  rw [show (1080 : ℕ) = 2 ^ 3 * 3 ^ 3 * 5 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hq).1 h with h | h5
  · rcases (Nat.Prime.dvd_mul hq).1 h with h2 | h3'
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2))
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h3')) h3
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h5)

theorem primes504 {q : ℕ} (hq : q.Prime) (h : q ∣ 504) (h3 : q ≠ 3) : q = 2 ∨ q = 7 := by
  rw [show (504 : ℕ) = 2 ^ 3 * 3 ^ 2 * 7 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hq).1 h with h | h7
  · rcases (Nat.Prime.dvd_mul hq).1 h with h2 | h3'
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2))
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h3')) h3
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h7)

theorem ne_one_of {P : ℕ} {g : Pm} (hc : Cn P) (hP : PRep 24 5 P g) (h : Nat.beq P idK = false) :
    g ≠ 1 := fun e => by
  rw [beq_of_one hc hP e] at h
  exact absurd h (by decide)

theorem selK_true {e Y : ℕ} {y : Pm} (hc : Cn Y) (hY : PRep 24 5 Y y) (h1 : y ≠ 1)
    (hq : y ^ 2 = 1 ∨ (e = 0 ∧ y ^ 5 = 1) ∨ (e ≠ 0 ∧ y ^ 7 = 1)) : selK e Y = true := by
  unfold selK
  rw [beq_false_of_ne hY h1]
  dsimp only
  simp only [sbeq]
  have p2 := prep_pc hY hY
  have c2 := cn_pc hc hc
  cases hb : Nat.beq (pc Y Y) idK
  · dsimp only
    have p4 := prep_pc p2 p2
    have c4 := cn_pc c2 c2
    rcases hq with h2 | ⟨he, h5⟩ | ⟨he, h7⟩
    · exact absurd (beq_of_one c2 p2 (by rw [← pow_two]; exact h2)) (by rw [hb]; decide)
    · subst he
      change Nat.beq (pc (pc (pc Y Y) (pc Y Y)) Y) idK = true
      exact beq_of_one (cn_pc c4 hc) (prep_pc p4 hY) (by rw [← h5]; simp only [pow_succ, pow_zero, one_mul, mul_assoc])
    · rw [beq_ne he]
      dsimp only
      exact beq_of_one (cn_pc c4 (cn_pc c2 hc)) (prep_pc p4 (prep_pc p2 hY))
        (by rw [← h7]; simp only [pow_succ, pow_zero, one_mul, mul_assoc])
  · rfl

theorem ord3 {Y : ℕ} {y : Pm} (hc : Cn Y) (hY : PRep 24 5 Y y) (h : ord3K Y = true) :
    orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold ord3K at h
  cases hb : Nat.beq Y idK
  · rw [hb] at h
    dsimp only at h
    have e := one_of_beq (prep_pc hY (prep_pc hY hY)) h
    exact orderOf_eq_prime (by rw [pow_three]; exact e) (ne_one_of hc hY hb)
  · rw [hb] at h
    dsimp only at h
    exact absurd h (by decide)

theorem wit_z {r h : ℕ} (hr : r < 24) (hh : h < 24) :
    Cn (pc (EL r) (pc (EL h) (pc (EL r) (EI h)))) ∧
      PRep 24 5 (pc (EL r) (pc (EL h) (pc (EL r) (EI h))))
        (eG r * (eG h * eG r * (eG h)⁻¹)) := by
  refine ⟨cn_pc (cEL hr) (cn_pc (cEL hh) (cn_pc (cEL hr) (cEI hh))), ?_⟩
  have e : eG r * (eG h * eG r * (eG h)⁻¹) = eG r * (eG h * (eG r * (eG h)⁻¹)) := by group
  rw [e]
  exact prep_pc (pEL hr) (prep_pc (pEL hh) (prep_pc (pEL hr) (pEI hh)))

theorem wit0 {r h : ℕ} (hr : r < 24) (hh : h < 24) (hw : wit3K r h 0 = true) :
    3 ∣ orderOf (eG r * (eG h * eG r * (eG h)⁻¹)) := by
  unfold wit3K at hw
  simp only [sbeq] at hw
  change ord3K _ = true at hw
  rw [ord3 (wit_z hr hh).1 (wit_z hr hh).2 hw]

theorem wit1 {r h : ℕ} (hr : r < 24) (hh : h < 24) (hw : wit3K r h 1 = true) :
    3 ∣ orderOf (eG r * (eG h * eG r * (eG h)⁻¹)) := by
  unfold wit3K at hw
  simp only [sbeq] at hw
  change ord3K (pw5 _) = true at hw
  obtain ⟨c, p⟩ := wit_z hr hh
  set z := eG r * (eG h * eG r * (eG h)⁻¹)
  have p5 : PRep 24 5 (pw5 (pc (EL r) (pc (EL h) (pc (EL r) (EI h))))) (z ^ 5) := by
    have e : z ^ 5 = z * (z * (z * (z * z))) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e]
    exact prep_pc p (prep_pc p (prep_pc p (prep_pc p p)))
  have c5 : Cn (pw5 (pc (EL r) (pc (EL h) (pc (EL r) (EI h))))) :=
    cn_pc c (cn_pc c (cn_pc c (cn_pc c c)))
  have h5 := ord3 c5 p5 hw
  exact h5 ▸ orderOf_pow_dvd 5

theorem wit_parts : 3 ∣ orderOf (eG 12 * (eG 15 * eG 12 * (eG 15)⁻¹)) ∧
    3 ∣ orderOf (eG 13 * (eG 16 * eG 13 * (eG 16)⁻¹)) ∧
    3 ∣ orderOf (eG 14 * (eG 17 * eG 14 * (eG 17)⁻¹)) ∧
    3 ∣ orderOf (eG 18 * (eG 21 * eG 18 * (eG 21)⁻¹)) ∧
    3 ∣ orderOf (eG 19 * (eG 22 * eG 19 * (eG 22)⁻¹)) ∧
    3 ∣ orderOf (eG 20 * (eG 23 * eG 20 * (eG 23)⁻¹)) := by
  have h := ch12613_wit3
  simp only [band_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨wit0 (by norm_num) (by norm_num) h1, wit0 (by norm_num) (by norm_num) h2,
    wit1 (by norm_num) (by norm_num) h3, wit0 (by norm_num) (by norm_num) h4,
    wit0 (by norm_num) (by norm_num) h5, wit0 (by norm_num) (by norm_num) h6⟩

theorem wd2_parts : eG 2 = wordG letG s1W ∧ eG 3 = wordG letG s2W ∧ eG 4 = wordG letG ca1W ∧
    eG 5 = wordG letG ca2W ∧ eG 6 = wordG letG cb1W ∧ eG 7 = wordG letG cb2W := by
  have h := ch12613_wd2
  simp only [band_iff] at h
  obtain ⟨h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨eG_word h2, eG_word h3, eG_word h4, eG_word h5, eG_word h6, eG_word h7⟩

theorem hA_le :
    Nat.card (stabB NativeSporadic.M24 (bs ⟨0, by norm_num⟩ ⟨3, by norm_num⟩ ⟨5, by norm_num⟩) 3)
      ≤ 20160 :=
  chain_le (by norm_num) (by norm_num) (by norm_num) (by norm_num) lv_parts.1 lv_parts.2.1
    lv_parts.2.2.1

theorem centHA_le :
    Nat.card ↥(stabB NativeSporadic.M24 (bs ⟨0, by norm_num⟩ ⟨3, by norm_num⟩ ⟨5, by norm_num⟩) 3 ⊓
      centralizer ({eG 0} : Set Pm)) ≤ 60 := by
  obtain ⟨⟨g0, g1, gi0, gi1, hR, hc, hh⟩, -⟩ := bind_parts
  have hgen : ∀ j < 2, Cn (OA.G j) ∧ Cn (OA.GI j) ∧ PRep 24 5 (OA.G j) (eG (8 + j)) ∧
      PRep 24 5 (OA.GI j) (eG (8 + j))⁻¹ ∧ eG (8 + j) ∈
        stabB NativeSporadic.M24 (bs ⟨0, by norm_num⟩ ⟨3, by norm_num⟩ ⟨5, by norm_num⟩) 3 := by
    intro j hj
    interval_cases j
    · rw [g0, gi0]
      exact ⟨cEL (by norm_num), cEI (by norm_num), pEL (by norm_num), pEI (by norm_num),
        fix3_mem (by norm_num) _ _ _ fix_parts.1⟩
    · rw [g1, gi1]
      exact ⟨cEL (by norm_num), cEI (by norm_num), pEL (by norm_num), pEI (by norm_num),
        fix3_mem (by norm_num) _ _ _ fix_parts.2.1⟩
  have hX : Cn OA.R := by
    rw [hR]
    exact cEL (by norm_num)
  have hXt : PRep 24 5 OA.R (eG 0) := by
    rw [hR]
    exact pEL (by norm_num)
  obtain ⟨s, hs, hsy⟩ := conj_rec hgen hX hXt hh oa_pt oa_hs
  have key := card_conj_mul_le _ (eG 0) s hsy
  rw [hs, hc] at key
  have := hA_le
  omega

theorem centA_le :
    Nat.card ↥(NativeSporadic.M24 ⊓ centralizer ({eG 0} : Set Pm)) ≤ 1080 := by
  obtain ⟨-, -, -, -, x0, x3, -, -⟩ := fix_parts
  have hS : (Finset.univ.filter fun q : Fin 24 => pg 5 (mask 5) (EL 0) q ≠ q).card = 18 := by
    decide +kernel
  have key := card_cent_le NativeSporadic.M24
    (stabB NativeSporadic.M24 (bs ⟨0, by norm_num⟩ ⟨3, by norm_num⟩ ⟨5, by norm_num⟩) 3) (eG 0) 0
    (Finset.univ.filter fun q : Fin 24 => pg 5 (mask 5) (EL 0) q ≠ q) (fun g hg => ?_)
    (fun g hg hb => ?_)
  · rw [hS] at key
    have := centHA_le
    omega
  · have hm := cent_apply_supp (mem_inf.1 hg).2 (b := 0) (by rw [x0]; decide)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [pEL (j := 0) (by norm_num) (g 0)]
    exact fun h => hm (Fin.ext h)
  · obtain ⟨f0, f1, f2⟩ := cent_fix3 (mem_inf.1 hg).2 hb
    rw [x0] at f1 f2
    rw [x3] at f2
    refine ⟨(mem_inf.1 hg).1, fun t ht => ?_⟩
    interval_cases t
    · exact f0
    · exact f1
    · exact f2

theorem recA (H : Subgroup Pm) (h4 : eG 4 ∈ H) (h5 : eG 5 ∈ H) : ∃ f : ℕ → Pm,
    (∀ i < 1080, PRep 24 5 (CA.T i) (f i) ∧ f i ∈ H) ∧
      ∀ a < 1080, ∀ b < 1080, f a = f b → a = b := by
  obtain ⟨-, -, ⟨g0, g1, gi0, gi1, hR, hc, hh⟩, -⟩ := bind_parts
  have hG : ∀ j < 2, CA.G j = pidn 24 5 := fun j hj => by
    interval_cases j
    · exact g0
    · exact g1
  have hgen : ∀ j < 2, Cn (CA.GI j) ∧ PRep 24 5 (CA.GI j) (eG (4 + j)) ∧ eG (4 + j) ∈ H := by
    intro j hj
    interval_cases j
    · rw [gi0]
      exact ⟨cEL (by norm_num), pEL (by norm_num), h4⟩
    · rw [gi1]
      exact ⟨cEL (by norm_num), pEL (by norm_num), h5⟩
  rw [hR] at hh
  have := mul_rec hG hgen hh ca_pt ca_hs
  rw [hc] at this
  exact this

theorem cA4 : eG 4 ∈ NativeSporadic.M24 ⊓ centralizer ({eG 0} : Set Pm) :=
  mem_inf.2 ⟨eG_mem _, comm_mem (by norm_num) (by norm_num) comm_parts.1⟩

theorem cA5 : eG 5 ∈ NativeSporadic.M24 ⊓ centralizer ({eG 0} : Set Pm) :=
  mem_inf.2 ⟨eG_mem _, comm_mem (by norm_num) (by norm_num) comm_parts.2.1⟩

theorem cardA :
    Nat.card ↥(NativeSporadic.M24 ⊓ centralizer ({eG 0} : Set Pm)) = 1080 := by
  obtain ⟨f, hf, hinj⟩ := recA _ cA4 cA5
  exact le_antisymm centA_le (card_of_inj (fun i hi => (hf i hi).2) hinj).1

theorem centA_eq :
    closure ({eG 4, eG 5} : Set Pm) = NativeSporadic.M24 ⊓ centralizer ({eG 0} : Set Pm) := by
  have hle : closure ({eG 4, eG 5} : Set Pm) ≤ NativeSporadic.M24 ⊓ centralizer ({eG 0} : Set Pm) :=
    (closure_le _).2 (Set.insert_subset_iff.2 ⟨cA4, Set.singleton_subset_iff.2 cA5⟩)
  obtain ⟨f, hf, hinj⟩ := recA (closure ({eG 4, eG 5} : Set Pm))
    (subset_closure (Set.mem_insert _ _)) (subset_closure (Set.mem_insert_of_mem _ rfl))
  exact Subgroup.eq_of_le_of_card_ge hle
    (cardA.trans_le (card_of_inj (fun i hi => (hf i hi).2) hinj).1)

theorem cvA_at {i : ℕ} (hi : i < 1080) : cvAK i = true := by
  have h := allBlk_spec (cvA_all (i / 60) (by change i / 60 < 18; omega)) (i % 60) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (i / 60) 60) (i % 60) = i := by
    change i / 60 * 60 + i % 60 = i
    omega
  rwa [e] at h

theorem rowA {j : ℕ} (hj : j < 3) : ∃ r ∈ [ra0W, ra1W, ra2W], eG (Nat.add 12 j) = wordG letG r := by
  obtain ⟨-, -, e12, e13, e14, -⟩ := wd_parts
  interval_cases j
  · exact ⟨ra0W, by simp, e12⟩
  · exact ⟨ra1W, by simp, e13⟩
  · exact ⟨ra2W, by simp, e14⟩

theorem coverA (y : Pm)
    (hy : y ∈ NativeSporadic.M24 ⊓ centralizer ({eG 0} : Set Pm))
    (hq : (orderOf y).Prime) (hq3 : orderOf y ≠ 3) : ∃ r ∈ [ra0W, ra1W, ra2W],
      ∃ c ∈ NativeSporadic.M24 ⊓ centralizer ({eG 0} : Set Pm), y = c * wordG letG r * c⁻¹ := by
  obtain ⟨f, hf, hinj⟩ := recA _ cA4 cA5
  obtain ⟨-, -, ⟨-, -, -, -, -, hc, -⟩, -⟩ := bind_parts
  obtain ⟨i, hi, rfl⟩ := (card_of_inj (fun i hi => (hf i hi).2) hinj).2 cardA.le y hy
  have hdvd : orderOf (f i) ∣ 1080 := by
    rw [← cardA, ← Subgroup.orderOf_mk (f i) hy]
    exact orderOf_dvd_natCard _
  have h1 : f i ≠ 1 := fun e => by
    rw [e, orderOf_one] at hq
    exact Nat.not_prime_one hq
  have hsel : selK 0 (CA.T i) = true := by
    refine selK_true (penumPt_specH (ca_pt i (by rw [hc]; exact hi))).1 (hf i hi).1 h1 ?_
    rcases primes1080 hq hdvd hq3 with h | h
    · exact Or.inl (by rw [← h]; exact pow_orderOf_eq_one _)
    · exact Or.inr (Or.inl ⟨rfl, by rw [← h]; exact pow_orderOf_eq_one _⟩)
  have h := cvA_at hi
  unfold cvAK at h
  simp only [sbeq] at h
  rw [hsel] at h
  dsimp only at h
  obtain ⟨hj, h⟩ := band h
  obtain ⟨hk, he⟩ := band h
  generalize Nat.land (CvA i) 65535 = j at hj he
  generalize Nat.shiftRight (CvA i) 16 = k at hk he
  rw [Nat.blt_eq] at hj hk
  rw [hc] at hk
  obtain ⟨r, hr, er⟩ := rowA hj
  have e := eq22_prep he (hf i hi).1 (hf k hk).1 (hf k hk).1
    (pEL (j := Nat.add 12 j) (by simp only [Nat.add_eq]; omega))
  refine ⟨r, hr, f k, (hf k hk).2, ?_⟩
  rw [← er, ← e, mul_inv_cancel_right]

theorem hB_le :
    Nat.card (stabB NativeSporadic.M24 (bs ⟨0, by norm_num⟩ ⟨17, by norm_num⟩ ⟨13, by norm_num⟩) 3)
      ≤ 20160 :=
  chain_le (by norm_num) (by norm_num) (by norm_num) (by norm_num) lv_parts.1 lv_parts.2.2.2.1
    lv_parts.2.2.2.2

theorem centHB_le :
    Nat.card ↥(stabB NativeSporadic.M24 (bs ⟨0, by norm_num⟩ ⟨17, by norm_num⟩ ⟨13, by norm_num⟩) 3 ⊓
      centralizer ({eG 1} : Set Pm)) ≤ 21 := by
  obtain ⟨-, ⟨g0, g1, gi0, gi1, hR, hc, hh⟩, -⟩ := bind_parts
  have hgen : ∀ j < 2, Cn (OB.G j) ∧ Cn (OB.GI j) ∧ PRep 24 5 (OB.G j) (eG (10 + j)) ∧
      PRep 24 5 (OB.GI j) (eG (10 + j))⁻¹ ∧ eG (10 + j) ∈
        stabB NativeSporadic.M24 (bs ⟨0, by norm_num⟩ ⟨17, by norm_num⟩ ⟨13, by norm_num⟩) 3 := by
    intro j hj
    interval_cases j
    · rw [g0, gi0]
      exact ⟨cEL (by norm_num), cEI (by norm_num), pEL (by norm_num), pEI (by norm_num),
        fix3_mem (by norm_num) _ _ _ fix_parts.2.2.1⟩
    · rw [g1, gi1]
      exact ⟨cEL (by norm_num), cEI (by norm_num), pEL (by norm_num), pEI (by norm_num),
        fix3_mem (by norm_num) _ _ _ fix_parts.2.2.2.1⟩
  have hX : Cn OB.R := by
    rw [hR]
    exact cEL (by norm_num)
  have hXt : PRep 24 5 OB.R (eG 1) := by
    rw [hR]
    exact pEL (by norm_num)
  obtain ⟨s, hs, hsy⟩ := conj_rec hgen hX hXt hh ob_pt ob_hs
  have key := card_conj_mul_le _ (eG 1) s hsy
  rw [hs, hc] at key
  have := hB_le
  omega

theorem centB_le :
    Nat.card ↥(NativeSporadic.M24 ⊓ centralizer ({eG 1} : Set Pm)) ≤ 504 := by
  obtain ⟨-, -, -, -, -, -, x0, x17⟩ := fix_parts
  have hS : (Finset.univ.filter fun q : Fin 24 => pg 5 (mask 5) (EL 1) q ≠ q).card = 24 := by
    decide +kernel
  have key := card_cent_le NativeSporadic.M24
    (stabB NativeSporadic.M24 (bs ⟨0, by norm_num⟩ ⟨17, by norm_num⟩ ⟨13, by norm_num⟩) 3) (eG 1)
    0 (Finset.univ.filter fun q : Fin 24 => pg 5 (mask 5) (EL 1) q ≠ q) (fun g hg => ?_)
    (fun g hg hb => ?_)
  · rw [hS] at key
    have := centHB_le
    omega
  · have hm := cent_apply_supp (mem_inf.1 hg).2 (b := 0) (by rw [x0]; decide)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [pEL (j := 1) (by norm_num) (g 0)]
    exact fun h => hm (Fin.ext h)
  · obtain ⟨f0, f1, f2⟩ := cent_fix3 (mem_inf.1 hg).2 hb
    rw [x0] at f1 f2
    rw [x17] at f2
    refine ⟨(mem_inf.1 hg).1, fun t ht => ?_⟩
    interval_cases t
    · exact f0
    · exact f1
    · exact f2

theorem recB (H : Subgroup Pm) (h6 : eG 6 ∈ H) (h7 : eG 7 ∈ H) : ∃ f : ℕ → Pm,
    (∀ i < 504, PRep 24 5 (CB.T i) (f i) ∧ f i ∈ H) ∧
      ∀ a < 504, ∀ b < 504, f a = f b → a = b := by
  obtain ⟨-, -, -, ⟨g0, g1, gi0, gi1, hR, hc, hh⟩, -⟩ := bind_parts
  have hG : ∀ j < 2, CB.G j = pidn 24 5 := fun j hj => by
    interval_cases j
    · exact g0
    · exact g1
  have hgen : ∀ j < 2, Cn (CB.GI j) ∧ PRep 24 5 (CB.GI j) (eG (6 + j)) ∧ eG (6 + j) ∈ H := by
    intro j hj
    interval_cases j
    · rw [gi0]
      exact ⟨cEL (by norm_num), pEL (by norm_num), h6⟩
    · rw [gi1]
      exact ⟨cEL (by norm_num), pEL (by norm_num), h7⟩
  rw [hR] at hh
  have := mul_rec hG hgen hh cb_pt cb_hs
  rw [hc] at this
  exact this

theorem cB6 : eG 6 ∈ NativeSporadic.M24 ⊓ centralizer ({eG 1} : Set Pm) :=
  mem_inf.2 ⟨eG_mem _, comm_mem (by norm_num) (by norm_num) comm_parts.2.2.2.2.2.1⟩

theorem cB7 : eG 7 ∈ NativeSporadic.M24 ⊓ centralizer ({eG 1} : Set Pm) :=
  mem_inf.2 ⟨eG_mem _, comm_mem (by norm_num) (by norm_num) comm_parts.2.2.2.2.2.2.1⟩

theorem cardB :
    Nat.card ↥(NativeSporadic.M24 ⊓ centralizer ({eG 1} : Set Pm)) = 504 := by
  obtain ⟨f, hf, hinj⟩ := recB _ cB6 cB7
  exact le_antisymm centB_le (card_of_inj (fun i hi => (hf i hi).2) hinj).1

theorem cvB_at {i : ℕ} (hi : i < 504) : cvBK i = true := by
  have h := allBlk_spec (cvB_all (i / 56) (by change i / 56 < 9; omega)) (i % 56) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (i / 56) 56) (i % 56) = i := by
    change i / 56 * 56 + i % 56 = i
    omega
  rwa [e] at h

theorem rowB {j : ℕ} (hj : j < 3) : ∃ r ∈ [rb0W, rb1W, rb2W], eG (Nat.add 18 j) = wordG letG r := by
  obtain ⟨-, -, -, -, -, -, -, -, e18, e19, e20, -⟩ := wd_parts
  interval_cases j
  · exact ⟨rb0W, by simp, e18⟩
  · exact ⟨rb1W, by simp, e19⟩
  · exact ⟨rb2W, by simp, e20⟩

theorem coverB (y : Pm)
    (hy : y ∈ NativeSporadic.M24 ⊓ centralizer ({eG 1} : Set Pm))
    (hq : (orderOf y).Prime) (hq3 : orderOf y ≠ 3) : ∃ r ∈ [rb0W, rb1W, rb2W],
      ∃ c ∈ NativeSporadic.M24 ⊓ centralizer ({eG 1} : Set Pm), y = c * wordG letG r * c⁻¹ := by
  obtain ⟨f, hf, hinj⟩ := recB _ cB6 cB7
  obtain ⟨-, -, -, ⟨-, -, -, -, -, hc, -⟩, -⟩ := bind_parts
  obtain ⟨i, hi, rfl⟩ := (card_of_inj (fun i hi => (hf i hi).2) hinj).2 cardB.le y hy
  have hdvd : orderOf (f i) ∣ 504 := by
    rw [← cardB, ← Subgroup.orderOf_mk (f i) hy]
    exact orderOf_dvd_natCard _
  have h1 : f i ≠ 1 := fun e => by
    rw [e, orderOf_one] at hq
    exact Nat.not_prime_one hq
  have hsel : selK 1 (CB.T i) = true := by
    refine selK_true (penumPt_specH (cb_pt i (by rw [hc]; exact hi))).1 (hf i hi).1 h1 ?_
    rcases primes504 hq hdvd hq3 with h | h
    · exact Or.inl (by rw [← h]; exact pow_orderOf_eq_one _)
    · exact Or.inr (Or.inr ⟨by norm_num, by rw [← h]; exact pow_orderOf_eq_one _⟩)
  have h := cvB_at hi
  unfold cvBK at h
  simp only [sbeq] at h
  rw [hsel] at h
  dsimp only at h
  obtain ⟨hj, h⟩ := band h
  obtain ⟨hk, he⟩ := band h
  generalize Nat.land (CvB i) 65535 = j at hj he
  generalize Nat.shiftRight (CvB i) 16 = k at hk he
  rw [Nat.blt_eq] at hj hk
  rw [hc] at hk
  obtain ⟨r, hr, er⟩ := rowB hj
  have e := eq22_prep he (hf i hi).1 (hf k hk).1 (hf k hk).1
    (pEL (j := Nat.add 18 j) (by simp only [Nat.add_eq]; omega))
  refine ⟨r, hr, f k, (hf k hk).2, ?_⟩
  rw [← er, ← e, mul_inv_cancel_right]

noncomputable def gS (l : ℕ) : Pm :=
  if l = 0 then eG 2 else if l = 1 then eG 3 else if l = 2 then (eG 2)⁻¹ else (eG 3)⁻¹

theorem both_prep {l : ℕ} (hl : l < 4) : PRep 24 5 (bothK 2 S.GI SI l) (gS l) := by
  obtain ⟨-, -, -, -, ⟨-, -, gi0, gi1, -, -, -⟩, si0, si1⟩ := bind_parts
  interval_cases l
  · change PRep 24 5 (S.GI 0) (eG 2)
    rw [gi0]
    exact pEL (by norm_num)
  · change PRep 24 5 (S.GI 1) (eG 3)
    rw [gi1]
    exact pEL (by norm_num)
  · change PRep 24 5 (SI 0) (eG 2)⁻¹
    rw [si0]
    exact pEI (by norm_num)
  · change PRep 24 5 (SI 1) (eG 3)⁻¹
    rw [si1]
    exact pEI (by norm_num)

theorem recS : ∃ f : ℕ → Pm,
    (∀ i < 27, PRep 24 5 (S.T i) (f i) ∧ f i ∈ closure ({eG 2, eG 3} : Set Pm)) ∧
      ∀ a < 27, ∀ b < 27, f a = f b → a = b := by
  obtain ⟨-, -, -, -, ⟨g0, g1, gi0, gi1, hR, hc, hh⟩, -⟩ := bind_parts
  have hG : ∀ j < 2, S.G j = pidn 24 5 := fun j hj => by
    interval_cases j
    · exact g0
    · exact g1
  have hgen : ∀ j < 2, Cn (S.GI j) ∧ PRep 24 5 (S.GI j) (eG (2 + j)) ∧
      eG (2 + j) ∈ closure ({eG 2, eG 3} : Set Pm) := by
    intro j hj
    interval_cases j
    · rw [gi0]
      exact ⟨cEL (by norm_num), pEL (by norm_num), subset_closure (Set.mem_insert _ _)⟩
    · rw [gi1]
      exact ⟨cEL (by norm_num), pEL (by norm_num),
        subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  rw [hR] at hh
  have := mul_rec hG hgen hh s_pt s_hs
  rw [hc] at this
  exact this

theorem s_step {f : ℕ → Pm} (hf : ∀ i < 27, PRep 24 5 (S.T i) (f i)) {i l : ℕ} (hi : i < 27)
    (hl : l < 4) : ∃ i' < 27, f i' = f i * gS l := by
  obtain ⟨-, -, -, -, ⟨-, -, -, -, -, hc, -⟩, -⟩ := bind_parts
  have h := slK_spec ch12613sCl (i * 4 + l) (Nat.zero_le _)
    (by change i * 4 + l < 0 + S.cnt * 4; rw [hc]; omega)
    (by change i * 4 + l < S.cnt * 4; rw [hc]; omega)
  obtain ⟨hlt, heq⟩ := findPt_spec h
  rw [hc] at hlt
  refine ⟨_, hlt, uniq (hf _ hlt) ?_⟩
  rw [heq]
  have e1 : Nat.div (i * 4 + l) 4 = i := by
    change (i * 4 + l) / 4 = i
    omega
  have e2 : Nat.mod (i * 4 + l) 4 = l := by
    change (i * 4 + l) % 4 = l
    omega
  unfold prodQK
  rw [e1, e2]
  exact prep_pc (hf i hi) (both_prep hl)

theorem s_all {f : ℕ → Pm} (hf : ∀ i < 27, PRep 24 5 (S.T i) (f i)) :
    ∀ y ∈ closure ({eG 2, eG 3} : Set Pm), ∃ i < 27, f i = y := by
  obtain ⟨-, -, -, -, ⟨-, -, -, -, hR, -, hh⟩, -⟩ := bind_parts
  have h0 : f 0 = 1 := by
    unfold penumHdK at hh
    simp only [band_iff] at hh
    have e : S.T 0 = S.R := Nat.eq_of_beq_eq_true hh.2.2.1
    have p := hf 0 (by norm_num)
    rw [e, hR] at p
    exact uniq p prep_id
  intro y hy
  induction hy using Subgroup.closure_induction_right with
  | one => exact ⟨0, by norm_num, h0⟩
  | mul_right x hx g hg ih =>
    obtain ⟨i, hi, rfl⟩ := ih
    rcases hg with rfl | hg
    · exact s_step hf hi (l := 0) (by norm_num)
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact s_step hf hi (l := 1) (by norm_num)
  | mul_inv_cancel x hx g hg ih =>
    obtain ⟨i, hi, rfl⟩ := ih
    rcases hg with rfl | hg
    · exact s_step hf hi (l := 2) (by norm_num)
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact s_step hf hi (l := 3) (by norm_num)

theorem cardS : Nat.card ↥(closure ({eG 2, eG 3} : Set Pm)) = 27 := by
  obtain ⟨f, hf, hinj⟩ := recS
  refine le_antisymm ?_ (card_of_inj (fun i hi => (hf i hi).2) hinj).1
  have hsurj : Function.Surjective fun i : Fin 27 =>
      (⟨f i, (hf i i.2).2⟩ : closure ({eG 2, eG 3} : Set Pm)) := fun y => by
    obtain ⟨i, hi, e⟩ := s_all (fun i hi => (hf i hi).1) y y.2
    exact ⟨⟨i, hi⟩, Subtype.ext e⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_eq_fintype_card (α := Fin 27), Fintype.card_fin] at this

theorem conj3 (t : Pm) (ht : t ∈ NativeSporadic.M24)
    (ht3 : orderOf t = 3) : ∃ g ∈ NativeSporadic.M24, t = g * eG 0 * g⁻¹ ∨ t = g * eG 1 * g⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f, hf, hinj⟩ := recS
  obtain ⟨-, -, -, -, ⟨-, -, -, -, -, hc, -⟩, -⟩ := bind_parts
  have hSR : closure ({eG 2, eG 3} : Set Pm) ≤ NativeSporadic.M24 :=
    (closure_le _).2 (Set.insert_subset_iff.2 ⟨eG_mem 2, Set.singleton_subset_iff.2 (eG_mem 3)⟩)
  have hcard : Nat.card ↥(closure ({eG 2, eG 3} : Set Pm)) =
      3 ^ (Nat.card NativeSporadic.M24).factorization 3 := by
    rw [cardS, m24_card, show (244823040 : ℕ) = 3 ^ 3 * 9067520 by norm_num,
      CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
    norm_num
  obtain ⟨x, hx, hxs⟩ :=
    CFSG.AGLEmbeddingD2.Wilson.ThreeCore.exists_conj_mem_of_card_prime hSR hcard ht ht3
  obtain ⟨i, hi, hfi⟩ := s_all (fun i hi => (hf i hi).1) _ hxs
  have hne : f i ≠ 1 := fun e => by
    rw [hfi] at e
    have e' : t = x * (x⁻¹ * t * x) * x⁻¹ := by group
    rw [e, mul_one, mul_inv_cancel] at e'
    rw [e', orderOf_one] at ht3
    exact absurd ht3 (by norm_num)
  have h := allN_spec ch12613_syl i (by rw [hc]; exact hi)
  unfold sylK at h
  simp only [sbeq] at h
  rw [beq_false_of_ne (hf i hi).1 hne] at h
  dsimp only at h
  obtain ⟨hcl, he⟩ := band h
  generalize Nat.shiftRight (SL i) 16 = c at hcl he
  generalize Nat.land (SL i) 65535 = L at he
  rw [Nat.blt_eq] at hcl
  have pu := wperm_prep_code (W := SW i) (len := L) (by norm_num) (by norm_num) pA pAi pB pBi
  have e := eq22_prep he pu (hf i hi).1 (pEL (j := c) (by omega)) pu
  set u := wC m24gA m24gB (SW i) L
  have hu : u ∈ NativeSporadic.M24 := wC_memM _ _
  have key : t = (x * u⁻¹) * eG c * (x * u⁻¹)⁻¹ := by
    rw [eq_mul_inv_of_mul_eq e.symm, hfi]
    group
  refine ⟨x * u⁻¹, mul_mem hx (inv_mem hu), ?_⟩
  interval_cases c
  · exact Or.inl key
  · exact Or.inr key

end CFSG.KD.M24Three

public section

namespace CFSG.KD.M24Three

open Subgroup CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Mathieu
open CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24

theorem m24_conj3 :
    ∀ t ∈ NativeSporadic.M24, orderOf t = 3 → ∃ g ∈ NativeSporadic.M24,
      t = g * wordG letG xW * g⁻¹ ∨ t = g * wordG letG x2W * g⁻¹ := by
  rw [← wd_parts.1, ← wd_parts.2.1]
  exact conj3

theorem m24_card3A :
    Nat.card ↥(NativeSporadic.M24 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 24)))) =
      1080 := by
  rw [← wd_parts.1]
  exact cardA

theorem m24_card3B :
    Nat.card ↥(NativeSporadic.M24 ⊓ centralizer ({wordG letG x2W} : Set (Equiv.Perm (Fin 24)))) =
      504 := by
  rw [← wd_parts.2.1]
  exact cardB

theorem m24_cent3A_eq :
    closure {wordG letG ca1W, wordG letG ca2W} =
      NativeSporadic.M24 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 24))) := by
  rw [← wd_parts.1, ← wd2_parts.2.2.1, ← wd2_parts.2.2.2.1]
  exact centA_eq

theorem m24_sylow27 : Nat.card ↥(closure {wordG letG s1W, wordG letG s2W}) = 27 := by
  rw [← wd2_parts.1, ← wd2_parts.2.1]
  exact cardS

theorem m24_cover3A :
    ∀ y ∈ NativeSporadic.M24 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 24))),
      (orderOf y).Prime → orderOf y ≠ 3 → ∃ r ∈ [ra0W, ra1W, ra2W],
        ∃ c ∈ NativeSporadic.M24 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 24))),
          y = c * wordG letG r * c⁻¹ := by
  rw [← wd_parts.1]
  exact coverA

theorem m24_cover3B :
    ∀ y ∈ NativeSporadic.M24 ⊓ centralizer ({wordG letG x2W} : Set (Equiv.Perm (Fin 24))),
      (orderOf y).Prime → orderOf y ≠ 3 → ∃ r ∈ [rb0W, rb1W, rb2W],
        ∃ c ∈ NativeSporadic.M24 ⊓ centralizer ({wordG letG x2W} : Set (Equiv.Perm (Fin 24))),
          y = c * wordG letG r * c⁻¹ := by
  rw [← wd_parts.2.1]
  exact coverB

theorem m24_wit3A : ∀ p ∈ [(ra0W, ha0W), (ra1W, ha1W), (ra2W, ha2W)],
    wordG letG p.2 ∈
        NativeSporadic.M24 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 24))) ∧
      3 ∣ orderOf (wordG letG p.1 * (wordG letG p.2 * wordG letG p.1 * (wordG letG p.2)⁻¹)) := by
  obtain ⟨e0, -, e12, e13, e14, e15, e16, e17, -⟩ := wd_parts
  obtain ⟨-, -, c15, c16, c17, -⟩ := comm_parts
  obtain ⟨w1, w2, w3, -⟩ := wit_parts
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · rw [← e0, ← e12, ← e15]
    exact ⟨mem_inf.2 ⟨eG_mem _, comm_mem (by norm_num) (by norm_num) c15⟩, w1⟩
  · rw [← e0, ← e13, ← e16]
    exact ⟨mem_inf.2 ⟨eG_mem _, comm_mem (by norm_num) (by norm_num) c16⟩, w2⟩
  · rw [← e0, ← e14, ← e17]
    exact ⟨mem_inf.2 ⟨eG_mem _, comm_mem (by norm_num) (by norm_num) c17⟩, w3⟩

theorem m24_wit3B : ∀ p ∈ [(rb0W, hb0W), (rb1W, hb1W), (rb2W, hb2W)],
    wordG letG p.2 ∈
        NativeSporadic.M24 ⊓ centralizer ({wordG letG x2W} : Set (Equiv.Perm (Fin 24))) ∧
      3 ∣ orderOf (wordG letG p.1 * (wordG letG p.2 * wordG letG p.1 * (wordG letG p.2)⁻¹)) := by
  obtain ⟨-, e1, -, -, -, -, -, -, e18, e19, e20, e21, e22, e23⟩ := wd_parts
  obtain ⟨-, -, -, -, -, -, -, c21, c22, c23⟩ := comm_parts
  obtain ⟨-, -, -, w4, w5, w6⟩ := wit_parts
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · rw [← e1, ← e18, ← e21]
    exact ⟨mem_inf.2 ⟨eG_mem _, comm_mem (by norm_num) (by norm_num) c21⟩, w4⟩
  · rw [← e1, ← e19, ← e22]
    exact ⟨mem_inf.2 ⟨eG_mem _, comm_mem (by norm_num) (by norm_num) c22⟩, w5⟩
  · rw [← e1, ← e20, ← e23]
    exact ⟨mem_inf.2 ⟨eG_mem _, comm_mem (by norm_num) (by norm_num) c23⟩, w6⟩

end CFSG.KD.M24Three

end
