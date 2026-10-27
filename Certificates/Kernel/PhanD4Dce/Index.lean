module

public import Certificates.Kernel.PhanD4Dce.Ident
public import Certificates.Kernel.PhanD4Dce.OmegaRelsN
public import Certificates.Kernel.PhanD4Dce.CoverLetters
public import Certificates.Kernel.PhanD4Dce.Stab1
public import Certificates.Kernel.PhanD4Dce.Stab2
public import Certificates.Kernel.PhanD4Dce.Stab3
public import Certificates.Kernel.PhanD4Dce.Stab4
public import Certificates.Kernel.PhanD4Dce.Stab5
public import Certificates.Kernel.PhanD4Dce.CoverNBind
public import Certificates.Kernel.PhanD4Dce.CoverN0
public import Certificates.Kernel.PhanD4Dce.CoverN1
public import Certificates.Kernel.PhanD4Dce.CoverN2
public import Certificates.Kernel.PhanD4Dce.CoverN3
public import CFSG.Certificates.Kernel.TwistDce3.RelsNetSound
public import CFSG.Certificates.Kernel.TwistDce2.IndexFinite

public section

namespace CFSG.KD.PhanD4Dce

open CFSG.KC.TwDce2 CFSG.CosetTable CFSG.Certificates.CosetEnumeration CFSG.KC.YModel
  CFSG.Certificates.TwDce CFSG.ClassicalInvolution.Phan.Q3G
open CFSG.Certificates.TwDce2.ChainB (chainLens)

theorem gens_all : ∀ i < 137, ∀ c ∈ CFSG.KC.LaneChain.getL CG i,
    wBelow 12 (gWord INVM RW c) = true := by
  decide +kernel

theorem lens_all : ∀ i < 137, ∀ m ∈ chainLens ((gRegs INVM RW (CFSG.KC.LaneChain.getL CG i)).map
    fun r => CFSG.KC.TwDce.wLen (r / 2)) (getLL CW i), m < 2 ^ 32 := by
  decide +kernel

theorem node1_fix : ∀ c ∈ CFSG.KC.LaneChain.getL CG 1,
    CFSG.KC.TwDce3.evP 15 FO (gWord INVM RW c) 0 = 0 := by
  decide +kernel

theorem gens1_ok : ∀ c ∈ CFSG.KC.LaneChain.getL CG 1, ∀ d ∈ wList (gWord INVM RW c), d < 8 := by
  decide +kernel

theorem ds_get : ∀ j < 137, CFSG.KC.LaneChain.getN DS j = j := by
  decide +kernel

theorem ds_lt : ∀ n ∈ DS, n < 137 := by
  decide +kernel

theorem ds_mem {n : ℕ} (hn : n ∈ DS) : ∃ j : Fin 137, CFSG.KC.LaneChain.getN DS j = n :=
  ⟨⟨n, ds_lt n hn⟩, ds_get n (ds_lt n hn)⟩

theorem cn_pos : ∀ i < 137, 0 < CFSG.KC.LaneChain.getN CN i := by
  decide +kernel

theorem cn_one : CFSG.KC.LaneChain.getN CN 1 = 576 := by
  decide +kernel

@[expose] noncomputable def cnSum (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i s => s + 13063680 / CFSG.KC.LaneChain.getN CN i) n

theorem cnSum_ok : cnSum 137 = 1516320 := by
  decide +kernel

theorem sum_eq_cnSum : ∀ n : ℕ,
    ∑ i ∈ Finset.range n, 13063680 / CFSG.KC.LaneChain.getN CN i = cnSum n
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_eq_cnSum n]
    rfl

theorem cn_sum : ∑ i : Fin 137, 13063680 / CFSG.KC.LaneChain.getN CN i = 1516320 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => 13063680 / CFSG.KC.LaneChain.getN CN i) 137,
    sum_eq_cnSum, cnSum_ok]

theorem ivL_ivL : ∀ c < 12, ivL INVM (ivL INVM c) = c := by
  decide +kernel

theorem netFacts : CFSG.Certificates.TwDce3.NetFacts 15 FO INVM NS 15 12 22680 where
  np := by norm_num
  net := CFSG.Certificates.TwDce3.bindAll_sound (by norm_num) (by norm_num) omega_nets
  tab := CFSG.Certificates.TwDce3.lettersOK_sound omega_letters
  inv := ivL_ivL

theorem omega_rels : CFSG.KC.TwDce3.relsOK 15 FO 22680 a3CodesL = true :=
  CFSG.Certificates.TwDce3.relsOK_of _ codes_len
    (CFSG.Certificates.TwDce3.relsN_sound netFacts le_rfl omega_rels_net codes_len)

section Cert


noncomputable abbrev ptO : QB → ℕ → ℕ := ptT omega_letters omega_rels

theorem ptO_lt (q : QB) {p : ℕ} (hp : p < 22680) : ptO q p < 22680 :=
  ptT_lt omega_letters omega_rels q hp

theorem ptO_one (p : ℕ) : ptO 1 p = p := ptT_one omega_letters omega_rels p

theorem ptO_mul (a b : QB) (p : ℕ) : ptO (a * b) p = ptO b (ptO a p) :=
  ptT_mul omega_letters omega_rels a b p

theorem evP_O {w : ℕ} (hw : ∀ c ∈ wList w, c < 12) {p : ℕ} (hp : p < 22680) :
    CFSG.KC.TwDce3.evP 15 FO w p = ptO (wVal xD w) p := by
  rw [CFSG.Certificates.TwDce3.Words.evP_eq, wVal]
  exact (pt_eval omega_letters omega_rels _ hw p hp).symm

theorem rw_lt {r : ℕ} (hr : r < 16625) : ∀ c ∈ wList (RW r), c < 12 :=
  fun c hc => (CFSG.Certificates.TwDce2.Words.wBelow_spec (rw_below r hr)).2 c hc

theorem gWord_eq (c : ℕ) :
    gWord INVM RW c = if c % 2 = 1 then wInv INVM (RW (c / 2)) else RW (c / 2) := by
  unfold gWord
  have h0 : Nat.shiftRight c 1 = c >>> 1 := rfl
  have h1 : Nat.shiftRight c 1 = c / 2 := by
    rw [h0, Nat.shiftRight_eq_div_pow]
  have h2 : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [h, if_neg (by norm_num)]
    rfl
  · rw [h, if_pos rfl]
    rfl

theorem wInv_lt {w : ℕ} (hw : ∀ c ∈ wList w, c < 12) : ∀ c ∈ wList (wInv INVM w), c < 12 := by
  intro c hc
  have e : wList (wInv INVM w) = (wList w).reverse.map (ivL INVM) :=
    (CFSG.Certificates.TwDce2.Words.wInv_spec INVM w).2.2
  rw [e] at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  exact ivl_lt (hw d (List.mem_reverse.1 hd))

theorem gWord_lt {c : ℕ} (hc : c / 2 < 16625) : ∀ d ∈ wList (gWord INVM RW c), d < 12 := by
  rw [gWord_eq]
  split_ifs
  · exact wInv_lt (rw_lt hc)
  · exact rw_lt hc

theorem evalWord_rev_inv {G : Type*} [Group G] {y : ℕ → G} :
    ∀ {l : List ℕ}, (∀ c ∈ l, y (ivL INVM c) = (y c)⁻¹) →
      evalWord y ((l.reverse).map (ivL INVM)) = (evalWord y l)⁻¹
  | [], _ => by simp [evalWord]
  | c :: l, h => by
    have ih := evalWord_rev_inv (y := y) (l := l) fun d hd => h d (List.mem_cons_of_mem _ hd)
    simp only [evalWord, List.map_map] at ih ⊢
    rw [List.reverse_cons, List.map_append, List.prod_append, ih]
    simp [h c List.mem_cons_self]

theorem wVal_wInv {G : Type*} [Group G] {y : ℕ → G} (hy : ∀ c < 12, y (ivL INVM c) = (y c)⁻¹)
    {w : ℕ} (hw : ∀ c ∈ wList w, c < 12) : wVal y (wInv INVM w) = (wVal y w)⁻¹ := by
  have e : wList (wInv INVM w) = (wList w).reverse.map (ivL INVM) :=
    (CFSG.Certificates.TwDce2.Words.wInv_spec INVM w).2.2
  rw [wVal, e, evalWord_rev_inv fun c hc => hy c (hw c hc)]
  rfl

theorem wVal_gWord {G : Type*} [Group G] {y : ℕ → G} (hy : ∀ c < 12, y (ivL INVM c) = (y c)⁻¹)
    {c : ℕ} (hc : c / 2 < 16625) : wVal y (gWord INVM RW c) =
      if c % 2 = 1 then (wVal y (RW (c / 2)))⁻¹ else wVal y (RW (c / 2)) := by
  rw [gWord_eq]
  split_ifs
  · exact wVal_wInv hy (rw_lt hc)
  · rfl

theorem hinvX : ∀ c < 12, onX (ivL INVM c) = (onX c)⁻¹ := fun c hc => (hinv c hc).2

theorem xQ_ivL {c : ℕ} (hc : c < 12) : xQ (ivL INVM c) = (xQ c)⁻¹ := by
  rw [inv_eq c hc]
  by_cases h : c % 2 = 0
  · rw [if_pos h]
    simp only [xQ, if_pos hc, if_pos (by omega : c + 1 < 12), if_pos h,
      if_neg (by omega : ¬ (c + 1) % 2 = 0), lGen_congr (by omega : (c + 1) / 2 = c / 2)]
  · rw [if_neg h]
    simp only [xQ, if_pos hc, if_pos (by omega : c - 1 < 12), if_neg h,
      if_pos (by omega : (c - 1) % 2 = 0), inv_inv, lGen_congr (by omega : (c - 1) / 2 = c / 2)]

theorem xD_ivL {c : ℕ} (hc : c < 12) : xD (ivL INVM c) = (xD c)⁻¹ := by
  rw [xD, xD, xQ_ivL hc, QuotientGroup.mk_inv]

theorem isStabOf_sound {n k g : ℕ} (h : isStabOf RD n k g = true) :
    g < n ∧ 3 ≤ dKind (RD g) ∧ dKind (RD g) < 5 ∧ dN1 (RD g) = k ∧ dN2 (RD g) = k := by
  unfold isStabOf isEq at h
  simp only [CFSG.Certificates.TwDce2.Words.kandB_iff, CFSG.Certificates.TwDce.Words.andB_iff,
    Nat.blt_eq, Nat.ble_eq, CFSG.Certificates.TwDce.Words.sB_eq] at h
  obtain ⟨h1, ⟨h2, h3⟩, h4, h5⟩ := h
  exact ⟨h1, h2, h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩

theorem allStab_sound {k : ℕ} : ∀ {L : List ℕ}, (List.rec (motive := fun _ => Bool) true
    (fun c _ ih => CFSG.KC.andB (isStabOf RD 16625 k (Nat.shiftRight c 1)) ih) L) = true →
    ∀ c ∈ L, isStabOf RD 16625 k (c / 2) = true
  | [], _, _, hc => absurd hc List.not_mem_nil
  | c :: L, h, d, hd => by
    have h' := CFSG.Certificates.TwDce2.Words.kandB_iff.1 h
    rcases List.mem_cons.1 hd with rfl | hd
    · have e0 : Nat.shiftRight d 1 = d >>> 1 := rfl
      have e : Nat.shiftRight d 1 = d / 2 := by
        rw [e0, Nat.shiftRight_eq_div_pow, pow_one]
      rw [← e]
      exact h'.1
    · exact allStab_sound h'.2 d hd

@[expose] noncomputable def onC : Subgroup PC := Subgroup.closure {onX 0, onX 2, onX 4, onX 6}

theorem onX_memC {d : ℕ} (h : d < 8) : onX d ∈ onC := by
  have hm : ∀ e ∈ ({0, 2, 4, 6} : Finset ℕ), onX e ∈ onC := by
    intro e he
    apply Subgroup.subset_closure
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp
  have hd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hm 0 (by simp)
  · rw [onX_1, ← onX_0]; exact onC.inv_mem (hm 0 (by simp))
  · exact hm 2 (by simp)
  · rw [onX_3, ← onX_2]; exact onC.inv_mem (hm 2 (by simp))
  · exact hm 4 (by simp)
  · rw [onX_5, ← onX_4]; exact onC.inv_mem (hm 4 (by simp))
  · exact hm 6 (by simp)
  · rw [onX_7, ← onX_6]; exact onC.inv_mem (hm 6 (by simp))

theorem onC_le : onC ≤ phanR := by
  rw [onC, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl | rfl)
  · exact hxH 0 (by norm_num)
  · exact hxH 2 (by norm_num)
  · exact hxH 4 (by norm_num)
  · exact hxH 6 (by norm_num)

theorem onC_conj {c : PC} (hc : c ∈ onC) : onT⁻¹ * c * onT = c := by
  have hZ : onC ≤ Subgroup.centralizer {onT} := by
    rw [onC, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hT 0 (by norm_num))
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hT 2 (by norm_num))
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hT 4 (by norm_num))
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hT 6 (by norm_num))
  have h := Subgroup.mem_centralizer_singleton_iff.1 (hZ hc)
  rw [mul_assoc, h, inv_mul_cancel_left]

theorem wVal_mem (w : ℕ) : wVal onX w ∈ phanR := by
  rw [wVal, evalWord]
  exact phanR.list_prod_mem fun y hy => by
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hy
    by_cases hd : d < 12
    · exact hxH d hd
    · rw [onX, if_neg hd]
      exact phanR.one_mem

theorem wVal_piB (w : ℕ) : wVal onX w = piB (wVal xD w) := evalWord_onX _

@[expose] noncomputable def onSt (k : ℕ) : Subgroup QB :=
  Subgroup.closure {q | ∃ c, isStabOf RD 16625 k (c / 2) = true ∧ q = wVal xD (gWord INVM RW c)}

@[expose] noncomputable def onK (i : ℕ) : Subgroup QB :=
  Subgroup.closure {q | ∃ c ∈ CFSG.KC.LaneChain.getL CG i, q = wVal xD (gWord INVM RW c)}

theorem stab_of {a m : ℕ}
    (h : CFSG.KC.TwDce3.stabRangeP 12 F INVM 2160 RD RW 16625 DS CG CW CB CS CT CN a m = true)
    {i : ℕ} (h1 : a ≤ i) (h2 : i < a + m) :
    CFSG.KC.TwDce3.stabOKP 12 F INVM 2160 RD RW 16625 (CFSG.KC.LaneChain.getN DS i)
      (CFSG.KC.LaneChain.getL CG i) (getLL CW i) (getLL CB i) (getLL CS i) (getLL CT i)
      (CFSG.KC.LaneChain.getN CN i) = true := by
  have e := CFSG.Certificates.TwDce3.ChainP.stabRangeP_sound h (i - a) (by omega)
  rwa [Nat.add_sub_cancel' h1] at e

theorem stab_i {i : ℕ} (hi : i < 137) :
    CFSG.KC.TwDce3.stabOKP 12 F INVM 2160 RD RW 16625 (CFSG.KC.LaneChain.getN DS i)
      (CFSG.KC.LaneChain.getL CG i) (getLL CW i) (getLL CB i) (getLL CS i) (getLL CT i)
      (CFSG.KC.LaneChain.getN CN i) = true := by
  by_cases h0 : i < 38
  · exact stab_of stab0 (by omega) (by omega)
  by_cases h1 : i < 79
  · exact stab_of stab1 (by omega) (by omega)
  by_cases h2 : i < 101
  · exact stab_of stab2 (by omega) (by omega)
  by_cases h3 : i < 114
  · exact stab_of stab3 (by omega) (by omega)
  by_cases h4 : i < 127
  · exact stab_of stab4 (by omega) (by omega)
  · exact stab_of stab5 (by omega) (by omega)

theorem onK_le_onSt {i : ℕ} (hi : i < 137) : onK i ≤ onSt (CFSG.KC.LaneChain.getN DS i) := by
  rw [onK, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  exact Subgroup.subset_closure
    ⟨c, allStab_sound (CFSG.Certificates.TwDce2.Words.kandB_iff.1 (stab_i hi)).1 c hc, rfl⟩

theorem card_onK_ge {i : ℕ} (hi : i < 137) :
    CFSG.KC.LaneChain.getN CN i ≤ Nat.card (onK i) := by
  have hs := CFSG.Certificates.TwDce3.ChainP.chainBP_sound (G := QB) xD pt2
    (ptT_one tab_letters tab_rels) (ptT_mul tab_letters tab_rels) (tb_lt tab_letters)
    (hxT tab_letters tab_rels) (onK i)
    (fun c hc => ⟨gens_all i hi c hc, Subgroup.subset_closure ⟨c, hc, rfl⟩⟩)
    (lens_all i hi) (CFSG.Certificates.TwDce2.Words.kandB_iff.1 (stab_i hi)).2
  have : Finite {g : QB // g ∈ onK i ∧ ∀ b ∈ getLL CB i,
      pt2 g (CFSG.KC.LaneChain.colDat 12 b / 2) = CFSG.KC.LaneChain.colDat 12 b / 2} :=
    Subtype.finite
  have : Nonempty {g : QB // g ∈ onK i ∧ ∀ b ∈ getLL CB i,
      pt2 g (CFSG.KC.LaneChain.colDat 12 b / 2) = CFSG.KC.LaneChain.colDat 12 b / 2} :=
    ⟨⟨1, Subgroup.one_mem _, fun b _ => ptT_one tab_letters tab_rels _⟩⟩
  exact le_trans (Nat.le_mul_of_pos_right _ Nat.card_pos) hs

theorem fold_pt {k : ℕ} : ∀ (cs : List ℕ), (∀ c ∈ cs, isStabOf RD 16625 k (c / 2) = true) →
    ∀ a : QB, ∃ g ∈ onSt k,
      cs.foldl (fun q c => CFSG.KC.TwDce3.evP 15 FO (gWord INVM RW c) q) (ptO a 0) =
        ptO (a * g) 0
  | [], _, a => ⟨1, Subgroup.one_mem _, by rw [mul_one]; rfl⟩
  | c :: cs, h, a => by
    have hc := h c List.mem_cons_self
    have hc2 := (isStabOf_sound hc).1
    obtain ⟨g, hg, he⟩ := fold_pt cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      (a * wVal xD (gWord INVM RW c))
    refine ⟨wVal xD (gWord INVM RW c) * g,
      Subgroup.mul_mem _ (Subgroup.subset_closure ⟨c, hc, rfl⟩) hg, ?_⟩
    rw [List.foldl_cons, evP_O (gWord_lt hc2) (ptO_lt _ (by norm_num)), ← ptO_mul, he,
      mul_assoc]

theorem reach_of {a m : ℕ}
    (h : CFSG.KC.TwDce3.coverRangeN 15 FO INVM RD RW NS 15 12 22680 16625 DS CR CA a m = true)
    {i : ℕ} (h1 : a ≤ i) (h2 : i < a + m) : ∀ p < 22680,
    CFSG.Certificates.TwDce3.Reached 15 FO INVM RD RW 16625 DS (CFSG.KC.LaneChain.getN DS i) p := by
  have e := CFSG.Certificates.TwDce3.coverRangeN_sound netFacts h (i - a) (by omega)
  rwa [Nat.add_sub_cancel' h1] at e

theorem reached {i : ℕ} (hi : i < 137) : ∀ p < 22680,
    CFSG.Certificates.TwDce3.Reached 15 FO INVM RD RW 16625 DS (CFSG.KC.LaneChain.getN DS i) p := by
  by_cases h0 : i < 33
  · exact reach_of coverN0 (by omega) (by omega)
  by_cases h1 : i < 62
  · exact reach_of coverN1 (by omega) (by omega)
  by_cases h2 : i < 88
  · exact reach_of coverN2 (by omega) (by omega)
  · exact reach_of coverN3 (by omega) (by omega)

theorem cover_pt {i : ℕ} (hi : i < 137) {p : ℕ} (hp : p < 22680) :
    ∃ f < 16625, dKind (RD f) < 3 ∧ dN1 (RD f) = CFSG.KC.LaneChain.getN DS i ∧ dN2 (RD f) ∈ DS ∧
      ∃ g ∈ onSt (CFSG.KC.LaneChain.getN DS i), p = ptO ((wVal xD (RW f))⁻¹ * g) 0 := by
  obtain ⟨f, hf, hk1, hn1, hn2, cs, hcs, hpe⟩ := reached hi p hp
  have h0 : CFSG.KC.TwDce3.evP 15 FO (wInv INVM (RW f)) 0 = ptO (wVal xD (RW f))⁻¹ 0 := by
    rw [evP_O (wInv_lt (rw_lt hf)) (by norm_num), wVal_wInv (fun c hc => xD_ivL hc) (rw_lt hf)]
  obtain ⟨g, hg, he⟩ := fold_pt cs hcs (wVal xD (RW f))⁻¹
  rw [h0] at hpe
  exact ⟨f, hf, Nat.blt_eq.mp hk1, hn1, hn2, g, hg, hpe.trans he⟩

@[expose] noncomputable def onS0 : Subgroup QB where
  carrier := {q | ptO q 0 = 0}
  mul_mem' {a b} ha hb := by
    have ha' : ptO a 0 = 0 := ha
    have hb' : ptO b 0 = 0 := hb
    change ptO (a * b) 0 = 0
    rw [ptO_mul, ha', hb']
  one_mem' := ptO_one 0
  inv_mem' {a} ha := by
    have ha' : ptO a 0 = 0 := ha
    change ptO a⁻¹ 0 = 0
    have h := ptO_mul a a⁻¹ 0
    rw [mul_inv_cancel, ptO_one, ha'] at h
    exact h.symm

theorem mem_onS0 {q : QB} : q ∈ onS0 ↔ ptO q 0 = 0 := Iff.rfl

theorem card_onS0_le : Nat.card onS0 ≤ 576 := by
  let φ : QB ⧸ onS0 → Fin 22680 := fun z => Quotient.liftOn' z
    (fun a => (⟨ptO a⁻¹ 0, ptO_lt _ (by norm_num)⟩ : Fin 22680)) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab
      apply Fin.ext
      change ptO a⁻¹ 0 = ptO b⁻¹ 0
      have e : b⁻¹ = (a⁻¹ * b)⁻¹ * a⁻¹ := by group
      rw [e, ptO_mul, mem_onS0.1 (onS0.inv_mem hab)])
  have hsurj : Function.Surjective φ := by
    intro p
    obtain ⟨f, -, -, -, -, g, -, he⟩ := cover_pt (i := 0) (by norm_num) p.2
    refine ⟨((((wVal xD (RW f))⁻¹ * g)⁻¹ : QB) : QB ⧸ onS0), Fin.ext ?_⟩
    change ptO ((wVal xD (RW f))⁻¹ * g)⁻¹⁻¹ 0 = p
    rw [inv_inv, ← he]
  have h1 : 22680 ≤ onS0.index := by
    rw [Subgroup.index_eq_card]
    have := Nat.card_le_card_of_surjective φ hsurj
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have h2 := onS0.card_mul_index
  have hQ : Nat.card QB = 13063680 := card_QB
  by_contra h
  have h3 := Nat.mul_le_mul (Nat.succ_le_of_lt (not_le.1 h)) h1
  omega

theorem onK1_le : onK 1 ≤ onS0 := by
  rw [onK, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  change ptO _ 0 = 0
  have hb := CFSG.Certificates.TwDce2.Words.wBelow_spec (gens_all 1 (by norm_num) c hc)
  rw [← evP_O (fun d hd => hb.2 d hd) (by norm_num)]
  exact node1_fix c hc

theorem onS0_eq : onK 1 = onS0 := by
  have h := card_onK_ge (i := 1) (by norm_num)
  rw [cn_one] at h
  exact Subgroup.eq_of_le_of_card_ge onK1_le (card_onS0_le.trans h)

theorem pi_S0_le {q : QB} (hq : q ∈ onS0) : piB q ∈ onC := by
  rw [← onS0_eq] at hq
  have : (onK 1).map piB ≤ onC := by
    rw [onK, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, ← wVal_piB, wVal, evalWord]
    refine onC.list_prod_mem fun y hy => ?_
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hy
    exact onX_memC (gens1_ok c hc d hd)
  exact this ⟨q, hq, rfl⟩

theorem relIndex_map_piB_le (S : Subgroup QB) : (S.map piB).relIndex piB.range ≤ S.index := by
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le le_sup_left)

theorem idx_le (i : Fin 137) : ((onSt (CFSG.KC.LaneChain.getN DS i)).map piB).relIndex phanR ≤
    13063680 / CFSG.KC.LaneChain.getN CN i := by
  rw [← range_piB]
  refine (relIndex_map_piB_le _).trans ?_
  rw [Nat.le_div_iff_mul_le (cn_pos i i.2)]
  have h1 := (card_onK_ge i.2).trans (Subgroup.card_le_of_le (onK_le_onSt i.2))
  calc (onSt (CFSG.KC.LaneChain.getN DS i)).index * CFSG.KC.LaneChain.getN CN i ≤
        (onSt (CFSG.KC.LaneChain.getN DS i)).index *
          Nat.card (onSt (CFSG.KC.LaneChain.getN DS i)) := Nat.mul_le_mul_left _ h1
    _ = Nat.card QB := (onSt _).index_mul_card
    _ = 13063680 := card_QB

theorem index_phanR_le : phanR.FiniteIndex ∧ phanR.index ≤ 1516320 := by
  classical
  obtain ⟨X, hX0, hX⟩ := factsP
  let repS : Fin 137 → Set PC := fun i => {k | ∃ f < 16625, dKind (RD f) < 3 ∧
    dN1 (RD f) = CFSG.KC.LaneChain.getN DS i ∧ dN2 (RD f) ∈ DS ∧ k = wVal onX (RW f)}
  let tP : Fin 137 → PC → Prop := fun i k =>
    ∃ j : Fin 137, ∃ v, v ∈ phanR ∧ X (CFSG.KC.LaneChain.getN DS i) * k * onT *
      (X (CFSG.KC.LaneChain.getN DS j) * v)⁻¹ ∈ phanR
  have htP : ∀ i : Fin 137, ∀ k ∈ repS i, tP i k := by
    rintro i _ ⟨f, hf, hk, hn1, hn2, rfl⟩
    obtain ⟨j, hj⟩ := ds_mem hn2
    have hfa := (hX f hf).2.2.2.1 hk
    refine ⟨j, wVal onX (RA f), wVal_mem _, ?_⟩
    rw [hj, ← hn1]
    exact hfa
  let D : TwistData phanR onC onT 137 :=
    { x := fun i => X (CFSG.KC.LaneChain.getN DS i)
      S := fun i => (onSt (CFSG.KC.LaneChain.getN DS i)).map piB
      rep := repS
      tgt := fun i k => if h : tP i k then h.choose else 0
      tgtElt := fun i k => if h : tP i k then h.choose_spec.choose else 1
      base := 0
      base_mem := by
        change X (CFSG.KC.LaneChain.getN DS 0) ∈ phanR
        rw [ds_get 0 (by norm_num), hX0]
        exact phanR.one_mem
      S_le := fun i => by
        rw [← range_piB]
        exact Subgroup.map_le_range _ _
      S_conj := by
        rintro i _ ⟨q, hq, rfl⟩
        induction hq using Subgroup.closure_induction with
        | mem q hq =>
          obtain ⟨c, hc, rfl⟩ := hq
          obtain ⟨hg, hk3, -, hn1, hn2⟩ := isStabOf_sound hc
          have hf := (hX (c / 2) hg).2.2.2.2 hk3
          rw [hn1, hn2] at hf
          rw [← wVal_piB, wVal_gWord hinvX hg]
          split_ifs
          · convert hf using 1
            group
          · convert phanR.inv_mem hf using 1
            group
        | one => rw [map_one, mul_one, mul_inv_cancel]; exact phanR.one_mem
        | mul a b _ _ ha hb =>
          have e : X (CFSG.KC.LaneChain.getN DS i) * piB (a * b) *
              (X (CFSG.KC.LaneChain.getN DS i))⁻¹ =
              (X (CFSG.KC.LaneChain.getN DS i) * piB a * (X (CFSG.KC.LaneChain.getN DS i))⁻¹) *
                (X (CFSG.KC.LaneChain.getN DS i) * piB b *
                  (X (CFSG.KC.LaneChain.getN DS i))⁻¹) := by
            rw [map_mul]; group
          rw [e]
          exact phanR.mul_mem ha hb
        | inv a _ ha =>
          have e : X (CFSG.KC.LaneChain.getN DS i) * piB a⁻¹ *
              (X (CFSG.KC.LaneChain.getN DS i))⁻¹ =
              (X (CFSG.KC.LaneChain.getN DS i) * piB a *
                (X (CFSG.KC.LaneChain.getN DS i))⁻¹)⁻¹ := by
            rw [map_inv]; group
          rw [e]
          exact phanR.inv_mem ha
      rep_le := by
        rintro i _ ⟨f, -, -, -, -, rfl⟩
        exact wVal_mem _
      rep_cover := by
        intro i h hh
        rw [← range_piB] at hh
        obtain ⟨q, rfl⟩ := hh
        obtain ⟨f, hf, hk, hn1, hn2, g, hg, hp⟩ :=
          cover_pt i.2 (ptO_lt q⁻¹ (p := 0) (by norm_num))
        have hc : (wVal xD (RW f))⁻¹ * g * q ∈ onS0 := by
          rw [mem_onS0, ptO_mul, ← hp, ← ptO_mul, inv_mul_cancel, ptO_one]
        refine ⟨wVal onX (RW f), ⟨f, hf, hk, hn1, hn2, rfl⟩, piB g⁻¹,
          ⟨g⁻¹, (onSt _).inv_mem hg, rfl⟩, piB ((wVal xD (RW f))⁻¹ * g * q), pi_S0_le hc, ?_⟩
        rw [wVal_piB, ← map_mul, ← map_mul]
        congr 1
        group
      tgtElt_mem := by
        intro i k hk
        have h := htP i k hk
        simp only [dif_pos h]
        exact h.choose_spec.choose_spec.1
      tgt_spec := by
        intro i k hk
        have h := htP i k hk
        simp only [dif_pos h]
        exact h.choose_spec.choose_spec.2 }
  have : Finite phanR := by
    rw [← range_piB]
    exact Finite.of_surjective _ piB.rangeRestrict_surjective
  obtain ⟨hfi, hle⟩ := D.index_le_sum_of_finite
    (fun c hc => by rw [onC_conj hc]; exact onC_le hc) hgen
  refine ⟨hfi, hle.trans ?_⟩
  calc ∑ i, (D.S i).relIndex phanR ≤ ∑ i : Fin 137, 13063680 / CFSG.KC.LaneChain.getN CN i :=
        Finset.sum_le_sum fun i _ => idx_le i
    _ = 1516320 := cn_sum

end Cert

end CFSG.KD.PhanD4Dce

end
