module

public import Certificates.Kernel.Fi23T.Idx
public import CFSG.Certificates.Kernel.Fi23Tr.Searches

public section

set_option maxRecDepth 400000

open Pointwise

namespace CertificateChecks.KernelFi23T

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23T CFSG.KC.Fi23C CFSG.KD.Fi23K CFSG.KD.Fi23T
  CFSG.KS.Fi23Tr CertificateChecks.KernelFi23M
open CFSG.Sporadic.Fi23.Native (trData cData tauAct dTable genTables PBits pBit pOf pZero pImg TrOrb
  trBFS trAct trD trBi dWord mkRowInv trIsFar trRowOK trFarOK trMuOK trEdOK trPhi xiGens mkMu
  mkMuTree mkEd nbrWit inTreeB)
open CFSG.Sporadic.Th.Native (ap Table none32 allIn)
open CFSG.Sporadic.Th (Rep idx_of_lt allIn_eq_true ap_ofFn)
open CFSG.Perm.Native (treeBFS treeOK)

noncomputable abbrev V0 : ℕ := ((List.range 137632).find? fun m => trIsFar RI m).getD 0

noncomputable abbrev PHI : Array Table := trPhi orbLit orb (trD orb) (trBi orb)

noncomputable abbrev FT : CFSG.Perm.Native.Tree := treeBFS 137632 V0 PHI (Array.range xiGens.size)

noncomputable abbrev MU : Array ℕ × Array ℕ := mkMu orbLit orb (trD orb) (trBi orb) RI V0

noncomputable abbrev MT : Array ℕ × Array ℕ × Array ℕ × Array ℕ × Array (ℕ × Table) :=
  mkMuTree orbLit orb (trD orb) (trBi orb) MU.1 MU.2

noncomputable abbrev ED : Array ℕ × Array ℕ :=
  mkEd orbLit orb (trD orb) (trBi orb) RI V0 MT.1 MT.2.2.2.2

theorem xiGens_size : xiGens.size = 10 := rfl

theorem xiGens_mem : ∀ l < 10, xiGens[l]! ∈ xiL := by decide

theorem xiGens_of : ∀ x ∈ xiL, ∃ l < 10, xiGens[l]! = x := by decide

theorem map_get {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (xs : Array α) {l : ℕ}
    (hl : l < xs.size) : (xs.map f)[l]! = f xs[l]! := by
  rw [getElem!_pos (xs.map f) l (by rw [Array.size_map]; exact hl), Array.getElem_map,
    getElem!_pos xs l hl]

section


theorem tA_ne0 {f : ℕ} (hf : f < 31671) (hT : fp f ∉ T0) : tA f 0 ≠ 0 := by
  intro e
  have h := vS_tA hf (by norm_num : 0 < 137632)
  rw [e, vS_zero] at h
  exact cfg_ok.nr_ne ⟨fp f, hT, rfl⟩ h.symm

theorem RI_tA {f : ℕ} (hf : f < 31671) (hT : fp f ∉ T0) : ap RI (tA f 0) = f := by
  have hm := tA_lt hf (by norm_num : 0 < 137632)
  rcases RI_spec.2 _ hm with ⟨-, h2⟩ | ⟨h1, h2, h3⟩
  · exact absurd rfl (h2 f hf ((tB_false hf).2 hT))
  · have e1 := vS_tA h1 (by norm_num : 0 < 137632)
    have e2 := vS_tA hf (by norm_num : 0 < 137632)
    rw [h3, e2, vS_zero] at e1
    have e := cfg_ok.inj (e := fp f) (f := fp (ap RI (tA f 0))) hT ((tB_false h1).1 h2) e1
    rw [← fp_val h1, ← e, fp_val hf]

theorem row_ok : trRowOK orbLit orb (trD orb) (trBi orb) (pOf (pZero ()) (trData ())) RI = true := by
  unfold trRowOK
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨RI_spec.1, allIn_eq_true.2 fun f _ hf => ?_⟩, allIn_eq_true.2 fun m _ hm => ?_⟩
  · rw [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
    by_cases hb : pBit (pOf (pZero ()) (trData ())) f = true
    · exact Or.inl hb
    · have hT := (tB_false hf).1 (Bool.eq_false_iff.2 hb)
      exact Or.inr ⟨tA_ne0 hf hT, RI_tA hf hT⟩
  · rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq,
      Bool.not_eq_true', decide_eq_true_eq]
    rcases RI_spec.2 m hm with ⟨h1, -⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl h1
    · exact Or.inr ⟨⟨h1, h2⟩, h3⟩

theorem exists_far : ∃ m < 137632, trIsFar RI m = true := by
  have hne : cfg.N2.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [card_N2]; norm_num)
  obtain ⟨W, hW⟩ := hne
  have hV : W ∈ cfg.Vtx := by
    rw [cfg_ok.vtx_eq]
    exact Or.inr (Or.inr hW)
  obtain ⟨m, hm, rfl⟩ := vS_surj hV
  exact ⟨m, hm, (far_iff hm).2 ⟨hW.1, hW.2.1⟩⟩

theorem v0_spec : V0 < 137632 ∧ trIsFar RI V0 = true := find_range_spec exists_far

theorem v0_lt : V0 < 137632 := v0_spec.1

theorem N2_of_far {m : ℕ} (hm : m < 137632) (h : trIsFar RI m = true) : vS m ∈ cfg.N2 :=
  cfg_ok.far_N2 (vS_vtx hm) ((far_iff hm).1 h).1 ((far_iff hm).1 h).2

theorem v0_N2' : vS V0 ∈ cfg.N2 := N2_of_far v0_lt v0_spec.2

theorem ap_phi {l x : ℕ} (hl : l < 10) (hx : x < 137632) : ap PHI[l]! x = tA xiGens[l]! x := by
  have hlt : xiGens[l]! < 31671 := xi_lt _ (xiGens_mem l hl)
  unfold PHI trPhi
  rw [map_get _ _ (by rw [xiGens_size]; exact hl), ap_ofFn _ hx]
  dsimp only
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt ((tA_lt hlt hx).trans (by norm_num))]

theorem lv_lt : ∀ l ∈ Array.range xiGens.size, l < 10 := fun l hl => by
  rw [Array.mem_range, xiGens_size] at hl
  exact hl

theorem phi_lt : ∀ l ∈ Array.range xiGens.size, ∀ x < 137632, ap PHI[l]! x < 137632 := by
  intro l hl x hx
  rw [ap_phi (lv_lt l hl) hx]
  exact tA_lt (xi_lt _ (xiGens_mem l (lv_lt l hl))) hx

theorem lv32 : ∀ l ∈ Array.range xiGens.size, l < 2 ^ 32 := fun l hl =>
  (lv_lt l hl).trans (by norm_num)

theorem reach_far {m : ℕ} (hm : m < 137632) (h : trIsFar RI m = true) :
    CFSG.KC.VecK.Reach (· ∈ Array.range xiGens.size) (fun l x => ap PHI[l]! x) V0 m := by
  let Y : Set (Finset (Fin 31671)) := {V | ∃ p, CFSG.KC.VecK.Reach (· ∈ Array.range xiGens.size)
    (fun l x => ap PHI[l]! x) V0 p ∧ p < 137632 ∧ vS p = V}
  have hT : vS V0 ∈ Y := ⟨V0, CFSG.KC.VecK.Reach.root, v0_lt, rfl⟩
  have hX : ∀ γ ∈ tau '' ptSet xiL, ∀ V ∈ Y, γ • V ∈ Y := by
    rintro _ ⟨x, hx, rfl⟩ V ⟨p, hp, hpl, rfl⟩
    obtain ⟨l, hl, e⟩ := xiGens_of x.val hx
    have hlv : l ∈ Array.range xiGens.size := by rw [Array.mem_range, xiGens_size]; exact hl
    have hr := CFSG.KC.VecK.Reach.step (f := fun l x => ap PHI[l]! x) hp hlv
    have hlt : xiGens[l]! < 31671 := by rw [e]; exact x.isLt
    refine ⟨_, hr, phi_lt l hlv p hpl, ?_⟩
    beta_reduce
    rw [ap_phi hl hpl, vS_tA hlt hpl, e, fp_of]
  obtain ⟨g, hg, e⟩ := cfg_ok.N2_trans v0_N2' (N2_of_far hm h)
  obtain ⟨p, hp, hpl, ep⟩ := orbit_sub hT hX g hg
  rw [← e] at ep
  rw [← vS_inj hpl hm ep]
  exact hp

theorem far_ok : trFarOK orbLit orb (trD orb) (trBi orb) (pOf (pZero ()) (trData ())) RI PHI V0 FT =
    true := by
  unfold trFarOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hB := CFSG.KC.VecK.treeBFS_spec (n := 137632) (by norm_num) v0_lt lv32 phi_lt
  refine ⟨⟨⟨⟨allIn_eq_true.2 fun l _ hl => ?_, v0_lt⟩, v0_spec.2⟩, hB.ok⟩,
    allIn_eq_true.2 fun m _ hm => ?_⟩
  · rw [xiGens_size] at hl
    have hx := xiGens_mem l hl
    have hlt := xi_lt _ hx
    have hT : fp xiGens[l]! ∈ T0 := hST0 (fp_ptSet xi_lt hx)
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, tB_iff hlt]
    refine ⟨⟨hlt, hT⟩, vS_inj (tA_lt hlt (by norm_num)) (by norm_num) ?_⟩
    rw [vS_tA hlt (by norm_num), vS_zero]
    exact hS0 _ (fp_ptSet xi_lt hx)
  · rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases h : trIsFar RI m = true
    · exact Or.inr (inTreeB_of_reach (by norm_num) v0_lt lv32 phi_lt (reach_far hm h))
    · exact Or.inl (Bool.eq_false_iff.2 h)

theorem hFv : ∀ h < 31671, pBit orb.sets[V0]! h = false → tA h V0 < 137632 :=
  fun h hh _ => tA_lt hh v0_lt

theorem mu_facts : MU.2.size = MU.1.size ∧
    (∀ i < MU.1.size, MU.2[i]! < 31671 ∧ pBit orb.sets[V0]! MU.2[i]! = false ∧
      tA MU.2[i]! V0 = MU.1[i]! ∧ RI[MU.1[i]!]! ≠ none32 ()) ∧
    (∀ i < MU.1.size, ∀ j < MU.1.size, MU.1[i]! = MU.1[j]! → i = j) ∧
    ∀ h < 31671, pBit orb.sets[V0]! h = false → RI[tA h V0]! ≠ none32 () →
      ∃ i < MU.1.size, MU.1[i]! = tA h V0 :=
  mkMu_spec _ _ _ _ _ _ hFv

theorem ms_lt : ∀ i < MU.1.size, MU.1[i]! < 137632 := fun i hi => by
  rw [← (mu_facts.2.1 i hi).2.2.1]
  exact hFv _ (mu_facts.2.1 i hi).1 (mu_facts.2.1 i hi).2.1

theorem ms_mu : ∀ i < MU.1.size, vS MU.1[i]! ∈ cfg.Mu (vS V0) := fun i hi => by
  obtain ⟨h1, h2, h3, h4⟩ := mu_facts.2.1 i hi
  refine ⟨nr_of (ms_lt i hi) h4, ?_⟩
  have h := adj_tA h1 v0_lt h2
  rw [h3] at h
  exact tsys.adj_symm h

theorem mu_ms {W : Finset (Fin 31671)} (hW : W ∈ cfg.Mu (vS V0)) :
    ∃ i < MU.1.size, vS MU.1[i]! = W := by
  obtain ⟨hN, hadj⟩ := hW
  obtain ⟨h, hh, rfl⟩ := tsys.adj_symm hadj
  have hb := (not_mem_vS h.isLt).2 (by rwa [fp_of])
  have e := vS_tA h.isLt v0_lt
  rw [fp_of] at e
  have hm := tA_lt h.isLt v0_lt
  have hne : RI[tA h.val V0]! ≠ none32 () := (nr_iff hm).2 (by rw [e]; exact hN)
  obtain ⟨i, hi, ei⟩ := mu_facts.2.2.2 h.val h.isLt hb hne
  exact ⟨i, hi, by rw [ei, e]⟩

theorem ms_size : 1 < MU.1.size := by
  have hsub : cfg.Mu (vS V0) ⊆ (((Finset.range MU.1.size).image fun i => vS MU.1[i]! :
      Finset (Finset (Fin 31671))) : Set (Finset (Fin 31671))) := by
    intro W hW
    obtain ⟨i, hi, rfl⟩ := mu_ms hW
    rw [Finset.coe_image]
    exact ⟨i, Finset.mem_coe.2 (Finset.mem_range.2 hi), rfl⟩
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, cfg_ok.mu_card v0_N2', cfg_M, M0_card] at h
  have h2 := (Finset.card_image_le (s := Finset.range MU.1.size) (f := fun i => vS MU.1[i]!)).trans
    (Finset.card_range MU.1.size).le
  omega

theorem hFms : ∀ i < MU.1.size, ∀ h < 31671, pBit orb.sets[MU.1[i]!]! h = false →
    tA h MU.1[i]! < 137632 := fun i hi h hh _ => tA_lt hh (ms_lt i hi)

theorem mt_facts : MT.2.1.size = MT.1.size ∧ MT.2.2.1.size = MT.1.size ∧
    MT.2.2.2.1.size = MT.1.size ∧ 0 < MT.1.size ∧ MT.1[0]! = MU.1[0]! ∧
    (∀ k < MT.1.size, ∃ i < MU.1.size, MU.1[i]! = MT.1[k]! ∧ MU.2[i]! = MT.2.2.2.1[k]!) ∧
    (∀ i < MT.1.size, ∀ j < MT.1.size, MT.1[i]! = MT.1[j]! → i = j) ∧
    (∀ k, 0 < k → k < MT.1.size → MT.2.1[k]! < k ∧ MT.2.2.1[k]! < 31671 ∧
      pBit orb.sets[MT.1[MT.2.1[k]!]!]! MT.2.2.1[k]! = false ∧
      tA MT.2.2.1[k]! MT.1[MT.2.1[k]!]! = MT.1[k]!) ∧
    MT.2.2.2.2.size ≤ MT.1.size ∧
    (∀ i < MT.2.2.2.2.size, MT.2.2.2.2[i]! =
      (MT.1[i]!, nbrWit orbLit orb (trD orb) (trBi orb) MT.1[i]!)) ∧
    (1 < MU.1.size → 0 < MT.2.2.2.2.size) ∧
    ((∀ i < MU.1.size, ∃ k < MT.1.size, MT.1[k]! = MU.1[i]!) ∨
      ∀ k < MT.1.size, ∀ i < MU.1.size, ∀ h < 31671, pBit orb.sets[MT.1[k]!]! h = false →
        tA h MT.1[k]! = MU.1[i]! → ∃ j < MT.1.size, MT.1[j]! = MU.1[i]!) :=
  mkMuTree_spec _ _ _ _ (lt_trans Nat.zero_lt_one ms_size) mu_facts.1 ms_lt mu_facts.2.2.1 hFms

theorem ord_lt : ∀ k < MT.1.size, MT.1[k]! < 137632 := fun k hk => by
  obtain ⟨i, hi, e, -⟩ := mt_facts.2.2.2.2.2.1 k hk
  rw [← e]
  exact ms_lt i hi

theorem mu_sub {W : Finset (Fin 31671)} (hW : W ∈ cfg.Mu (vS V0)) :
    ∃ k < MT.1.size, vS MT.1[k]! = W := by
  let X : Set (Finset (Fin 31671)) := {V | ∃ k < MT.1.size, vS MT.1[k]! = V}
  rcases mt_facts.2.2.2.2.2.2.2.2.2.2.2 with hall | hcl
  · obtain ⟨i, hi, rfl⟩ := mu_ms hW
    obtain ⟨k, hk, e⟩ := hall i hi
    exact ⟨k, hk, by rw [e]⟩
  · have hXM : X ⊆ cfg.Mu (vS V0) := by
      rintro _ ⟨k, hk, rfl⟩
      obtain ⟨i, hi, e, -⟩ := mt_facts.2.2.2.2.2.1 k hk
      rw [← e]
      exact ms_mu i hi
    have h0 : vS MT.1[0]! ∈ X := ⟨0, mt_facts.2.2.2.1, rfl⟩
    refine cfg_ok.mu_closed v0_N2' h0 hXM (fun a ha b hb hab => ?_) hW
    obtain ⟨k, hk, rfl⟩ := ha
    obtain ⟨i, hi, rfl⟩ := mu_ms hb
    obtain ⟨h, hh, e⟩ := hab
    have hb' := (not_mem_vS h.isLt).2 (by rwa [fp_of])
    have e2 : vS (tA h.val MT.1[k]!) = vS MU.1[i]! := by
      rw [vS_tA h.isLt (ord_lt k hk), fp_of]
      exact e.symm
    obtain ⟨j, hj, ej⟩ := hcl k hk i hi h.val h.isLt hb'
      (vS_inj (tA_lt h.isLt (ord_lt k hk)) (ms_lt i hi) e2)
    exact ⟨j, hj, by rw [ej]⟩

theorem ms_in_ord : ∀ i < MU.1.size, ∃ k < MT.1.size, MT.1[k]! = MU.1[i]! := by
  intro i hi
  obtain ⟨k, hk, e⟩ := mu_sub (ms_mu i hi)
  exact ⟨k, hk, vS_inj (ord_lt k hk) (ms_lt i hi) e⟩

theorem ord_size : MT.1.size < 2 ^ 32 := by
  have h : ((Finset.range MT.1.size).image fun k => MT.1[k]!).card = MT.1.size := by
    rw [Finset.card_image_of_injOn (fun i hi j hj e => mt_facts.2.2.2.2.2.2.1 i
      (Finset.mem_range.1 (Finset.mem_coe.1 hi)) j (Finset.mem_range.1 (Finset.mem_coe.1 hj)) e),
      Finset.card_range]
  have hsub : ((Finset.range MT.1.size).image fun k => MT.1[k]!) ⊆ Finset.range 137632 := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_range.2 (ord_lt k (Finset.mem_range.1 hk))
  have h2 := Finset.card_le_card hsub
  rw [h, Finset.card_range] at h2
  omega

theorem mu_ok : trMuOK orbLit orb (trD orb) (trBi orb) RI V0 MT.1 MT.2.1 MT.2.2.1 MT.2.2.2.1
    (muPosOf MT.1) = true := by
  have hp := muPosOf_spec ord_lt mt_facts.2.2.2.2.2.2.1 ord_size
  unfold trMuOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨mt_facts.2.2.2.1, mt_facts.1⟩, mt_facts.2.1⟩, mt_facts.2.2.1⟩, hp.1⟩,
    allIn_eq_true.2 fun k _ hk => ?_⟩, allIn_eq_true.2 fun k hk1 hk => ?_⟩,
    allIn_eq_true.2 fun h _ hh => ?_⟩
  · obtain ⟨i, hi, e1, e2⟩ := mt_facts.2.2.2.2.2.1 k hk
    obtain ⟨h1, h2, h3, h4⟩ := mu_facts.2.1 i hi
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, decide_eq_true_eq, bne_iff_ne, beq_iff_eq, beq_iff_eq, Bool.not_eq_true',
      ← e1, ← e2]
    exact ⟨⟨⟨⟨⟨ms_lt i hi, h4⟩, h1⟩, h2⟩, h3⟩, by rw [e1]; exact hp.2.1 k hk⟩
  · obtain ⟨p1, p2, p3, p4⟩ := mt_facts.2.2.2.2.2.2.2.1 k (by omega) hk
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
      beq_iff_eq, Bool.not_eq_true']
    exact ⟨⟨⟨p1, p2⟩, p3⟩, p4⟩
  · rw [Bool.or_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq]
    by_cases hb : pBit orb.sets[V0]! h = true
    · exact Or.inl (Or.inl hb)
    by_cases hn : RI[tA h V0]! = none32 ()
    · exact Or.inl (Or.inr hn)
    obtain ⟨i, hi, ei⟩ := mu_facts.2.2.2 h hh (Bool.eq_false_iff.2 hb) hn
    obtain ⟨k, hk, ek⟩ := ms_in_ord i hi
    have e : ap (muPosOf MT.1) (tA h V0) = k := by
      rw [← ei, ← ek]
      exact hp.2.1 k hk
    have e' : MT.1[k]! = tA h V0 := ek.trans ei
    refine Or.inr ⟨?_, ?_⟩
    · change ap (muPosOf MT.1) (tA h V0) < MT.1.size
      rw [e]
      exact hk
    · change MT.1[ap (muPosOf MT.1) (tA h V0)]! = tA h V0
      rw [e]
      exact e'

theorem ed_wit : ∀ h < 31671, pBit orb.sets[V0]! h = false → trIsFar RI (tA h V0) = true →
    ∃ i < MT.1.size, ∃ g < 31671, pBit orb.sets[MT.1[i]!]! g = false ∧
      tA g MT.1[i]! = tA h V0 := by
  intro h hh hb hf
  have hm := tA_lt hh v0_lt
  obtain ⟨hT, hN⟩ := (far_iff hm).1 hf
  have hadj := adj_tA hh v0_lt hb
  rcases cfg_ok.ed v0_N2' hadj with hn | ⟨W, hW, hUW⟩
  · exact absurd hn hN
  obtain ⟨k, hk, rfl⟩ := mu_sub hW
  obtain ⟨g, hg, e⟩ := tsys.adj_symm hUW
  have e2 : vS (tA g.val MT.1[k]!) = vS (tA h V0) := by
    rw [vS_tA g.isLt (ord_lt k hk), fp_of]
    exact e.symm
  exact ⟨k, hk, g.val, g.isLt, (not_mem_vS g.isLt).2 (by rwa [fp_of]),
    vS_inj (tA_lt g.isLt (ord_lt k hk)) hm e2⟩

theorem ed_facts : ∀ h < 31671, pBit orb.sets[V0]! h = false → trIsFar RI (tA h V0) = true →
    ED.1[h]! < MT.1.size ∧ ED.2[h]! < 31671 ∧ pBit orb.sets[MT.1[ED.1[h]!]!]! ED.2[h]! = false ∧
      tA ED.2[h]! MT.1[ED.1[h]!]! = tA h V0 :=
  mkEd_spec _ _ _ _ _ _ ord_lt mt_facts.2.2.2.2.2.2.1 mt_facts.2.2.2.2.2.2.2.2.1
    (mt_facts.2.2.2.2.2.2.2.2.2.2.1 ms_size) mt_facts.2.2.2.2.2.2.2.2.2.1
    (fun i hi h hh _ => tA_lt hh (ord_lt i hi)) hFv ed_wit

theorem ed_ok : trEdOK orbLit orb (trD orb) (trBi orb) RI V0 MT.1 ED.1 ED.2 = true := by
  unfold trEdOK
  refine allIn_eq_true.2 fun h _ hh => ?_
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true', Bool.not_eq_true']
  by_cases hb : pBit orb.sets[V0]! h = true
  · exact Or.inl (Or.inl hb)
  by_cases hf : trIsFar RI (tA h V0) = true
  · obtain ⟨e1, e2, e3, e4⟩ := ed_facts h hh (Bool.eq_false_iff.2 hb) hf
    exact Or.inr ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩
  · exact Or.inl (Or.inr (Bool.eq_false_iff.2 hf))

end

end CertificateChecks.KernelFi23T

end
