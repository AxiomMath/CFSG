
module

public import Certificates.Kernel.LocalComp.HeFix2329.Glue
public import CFSG.Certificates.Kernel.Spor.BfsMap
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowBase
public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.InnerCheckInputs
public meta import CFSG.Sporadic.HeldB.InnerData
public meta import CFSG.Sporadic.HeldB.Common
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.HeldB.OuterArithCheckInputs
public meta import CFSG.Sporadic.HeldB.AutData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.OuterCentCheckInputs
public meta import CFSG.Sporadic.HeldB.OuterCentAux
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.Certificates.Kernel.HeAutKSound

public noncomputable section

namespace CertificateChecks.KernelLC.HeFix2329

open CFSG Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore CFSG.Sporadic.HeldB CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.GrSLit.HeldFix
open CertificateChecks.KernelLC.HeFix (c1Tab_eq heT1_eq hfX_eq tau_lt yw_lt delta_len delta_lt)

set_option maxRecDepth 100000 in
theorem lettersX : lettersOK 3 hfXWord = true := by decide

theorem c1_size {j : ℕ} (hj : j < 9) : (hfC1Tabs[j]!).size = 8330 := by
  rw [c1Tab_eq hj, CFSG.KS.Raw.unpack, Array.size_ofFn]

theorem t1_size : heT1Arr.size = 8330 := by rw [heT1_eq, CFSG.KS.Raw.unpack, Array.size_ofFn]

theorem x_size : hfXTab.size = 8330 := by rw [hfX_eq, CFSG.KS.Raw.unpack, Array.size_ofFn]

theorem rep_X : Rep 8330 hfXTab hfX := by
  rw [hfXTab, hfAUArrs_eq, hfX]
  exact rep_wordA_evalSignedWord (fun h hh => (rep_heLetter h hh).1)
    (fun h hh => (rep_heLetter h hh).2) (by rw [heOuterLetters_length]; exact lettersX)

theorem tabRep_C1 : ∀ j < hfC1Tabs.size, TabRep hfC1Tabs[j]! (heInnerCP1 j) := by
  intro j hj
  have hj9 : j < 9 := by simpa [hfC1Tabs] using hj
  have hs := c1_size hj9
  have e : hfC1Tabs[j]! = heInnerC1 j := by
    rw [hfC1Tabs, getElem!_pos _ j (by simpa using hj9), Array.getElem_ofFn]
  rw [e] at hs ⊢
  exact tabRep_of_rep (rep_heInnerC1 hj9) hs

theorem tabRep_TT : ∀ j < hfTTabs.size, TabRep hfTTabs[j]! (hfTL j) := by
  intro j hj
  have hj5 : j < 5 := hfTTabs_size ▸ hj
  rw [hfTTabs, getElem!_pos _ j (by simpa using hj5), Array.getElem_ofFn]
  simp only [hfTL]
  by_cases h0 : j = 0
  · simp only [h0, ↓reduceIte]
    exact tabRep_of_rep rep_heT1 t1_size
  · simp only [h0, ↓reduceIte]
    exact tabRep_wordTabS tabRep_C1 _ fun i hi => by
      have := tau_lt (j - 1) (by omega) i hi
      simpa [hfC1Tabs] using this

theorem tabRep_YL : ∀ j < hfYLetterTabs.size, TabRep hfYLetterTabs[j]! (hfYL j) := by
  intro j hj
  have hj10 : j < 10 := by simpa [hfYLetterTabs] using hj
  rw [hfYLetterTabs, getElem!_pos _ j (by simpa using hj10), Array.getElem_ofFn]
  simp only [hfYL]
  by_cases h9 : j < 9
  · simp only [h9, ↓reduceIte]
    have := tabRep_C1 j (by simpa [hfC1Tabs] using h9)
    rwa [hfC1Tabs, getElem!_pos _ j (by simpa using h9), Array.getElem_ofFn] at this
  · simp only [h9, ↓reduceIte]
    exact tabRep_of_rep rep_X x_size

theorem tabRep_Y : TabRep hfYTab hfY :=
  tabRep_wordTabS tabRep_YL _ fun j hj => by
    have := yw_lt j hj
    simpa [hfYLetterTabs] using this

theorem tabRep_T0 : ∀ j < hfT0Tabs.size, TabRep hfT0Tabs[j]! (hfT0L j) := by
  intro j hj
  have hj6 : j < 6 := hfT0Tabs_size ▸ hj
  rw [hfT0Tabs, getElem!_pos _ j (by simpa using hj6), Array.getElem_ofFn]
  simp only [hfT0L]
  by_cases h5 : j < 5
  · simp only [h5, ↓reduceIte]
    exact tabRep_TT j (hfTTabs_size ▸ h5)
  · simp only [h5, ↓reduceIte]
    exact tabRep_Y

theorem tau_mem {i : ℕ} (hi : i < 4) : hfTau i ∈ heInnerGrp1 := by
  refine heInnerGrp1.list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact heInnerCP1_mem_grp1 (tau_lt i hi j hj)

theorem tl_mem {j : ℕ} (hj : j < 5) : hfTL j ∈ heInnerGrp1 := by
  simp only [hfTL]
  split_ifs with h0
  · exact heT1P_mem_grp1
  · exact tau_mem (by omega)

theorem T_le_heP : hfT ≤ heP := by
  rw [hfT, genGroup, closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact heInnerGrp1_le.trans inf_le_left (tl_mem (hfTTabs_size ▸ hj))

theorem T0_le_R : hfT0 ≤ heAutGroup := by
  rw [hfT0, genGroup, closure_le]
  rintro _ ⟨j, hj, rfl⟩
  simp only [hfT0L]
  split_ifs with h5
  · exact heP_le_heAutGroup (T_le_heP (subset_closure ⟨j, hfTTabs_size ▸ h5, rfl⟩))
  · exact hfY_mem

theorem heP_mul_mem_iff' {a b : Equiv.Perm (Fin 8330)} (ha : a ∈ heAutGroup) (hb : b ∈ heAutGroup) :
    a * b ∈ heP ↔ (a ∈ heP ↔ b ∈ heP) := by
  have h := Subgroup.mul_mem_iff_of_index_two (H := heP.subgroupOf heAutGroup)
    heP_relIndex_heAutGroup (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h
  exact h

theorem outerLetter_mem (s : Fin heOuterLetters.length) : heOuterLetters.get s ∈ heAutGroup := by
  have h3 : s.val < 3 := s.2
  match s with
  | ⟨0, _⟩ => exact heP_le_heAutGroup (heGenPerm_mem (by norm_num))
  | ⟨1, _⟩ => exact heP_le_heAutGroup (heGenPerm_mem (by norm_num))
  | ⟨2, _⟩ => exact heAutU_mem_heAutGroup

theorem outerLetter_mem_heP_iff (s : Fin heOuterLetters.length) :
    heOuterLetters.get s ∈ heP ↔ (s.val == 2) = false := by
  have h3 : s.val < 3 := s.2
  match s with
  | ⟨0, _⟩ => exact ⟨fun _ => rfl, fun _ => heGenPerm_mem (by norm_num)⟩
  | ⟨1, _⟩ => exact ⟨fun _ => rfl, fun _ => heGenPerm_mem (by norm_num)⟩
  | ⟨2, _⟩ => exact ⟨fun h => absurd h heAutU_not_mem, fun h => absurd h (by simp)⟩

theorem evalWord_mem_heP_iff' (w : List (Fin heOuterLetters.length × Bool)) :
    Quiver.SchreierGraph.evalWord (fun h : Fin heOuterLetters.length => heOuterLetters.get h) w ∈
      heP ↔ w.countP (fun l => l.1.val == 2) % 2 = 0 := by
  have hR : ∀ v : List (Fin heOuterLetters.length × Bool),
      Quiver.SchreierGraph.evalWord (fun h : Fin heOuterLetters.length => heOuterLetters.get h) v ∈
        heAutGroup := fun v =>
    (Subgroup.closure_le heAutGroup).2 (by
      rintro _ ⟨h, rfl⟩
      exact outerLetter_mem h) (Quiver.SchreierGraph.evalWord_mem_closure _ v)
  induction w with
  | nil => simp
  | cons l w ih =>
    obtain ⟨s, b⟩ := l
    have hs := outerLetter_mem_heP_iff s
    have e : ∀ x : Equiv.Perm (Fin 8330), x ∈ heAutGroup → (x ∈ heP ↔ (s.val == 2) = false) →
        (x * Quiver.SchreierGraph.evalWord (fun h => heOuterLetters.get h) w ∈ heP ↔
          ((s, b) :: w).countP (fun l => l.1.val == 2) % 2 = 0) := by
      intro x hx hxs
      rw [heP_mul_mem_iff' hx (hR w), hxs]
      refine (iff_congr Iff.rfl ih).trans ?_
      rw [List.countP_cons]
      cases (s.val == 2)
      · simp
      · simp
        omega
    cases b
    · rw [Quiver.SchreierGraph.evalWord_cons_false]
      exact e _ (heAutGroup.inv_mem (outerLetter_mem s)) (by rw [inv_mem_iff]; exact hs)
    · rw [Quiver.SchreierGraph.evalWord_cons_true]
      exact e _ (outerLetter_mem s) hs

set_option maxRecDepth 100000 in
theorem hfX_notMem : hfX ∉ heP := by
  have hl : lettersOK heOuterLetters.length hfXWord = true := lettersX
  rw [hfX, evalSignedWord]
  simp only [hl, ↓reduceIte]
  rw [evalWord_mem_heP_iff']
  decide

theorem hfY_notMem : hfY ∉ heP := by
  intro h
  have hyl : ∀ j < 9, hfYL j = heInnerCP1 j := fun j hj => by simp [hfYL, hj]
  have e : hfY = hfYL 1 * (hfYL 8 * (hfX * (hfYL 3 * (hfYL 2 * (hfYL 8 * hfYL 8))))) := by
    have h9 : hfYL 9 = hfX := by simp [hfYL]
    simp only [hfY, hfYWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      h9]
  have hc : ∀ j < 9, hfYL j ∈ heP := fun j hj => by
    rw [hyl j hj]
    exact heInnerCP1_mem j
  rw [e, heP.mul_mem_cancel_left (hc 1 (by norm_num)), heP.mul_mem_cancel_left (hc 8 (by norm_num)),
    heP.mul_mem_cancel_right (heP.mul_mem (hc 3 (by norm_num)) (heP.mul_mem (hc 2 (by norm_num))
      (heP.mul_mem (hc 8 (by norm_num)) (hc 8 (by norm_num)))))] at h
  exact hfX_notMem h

theorem siftY_false :
    siftA 8330 (rawLevels 8330 heStrongArrs heBase.toArray) heBase.toArray 0 hfYTab = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact hfY_notMem ((mem_heP_iff_siftA tabRep_Y.2).1 h)

theorem pts : PointsList 8330 32 hfDelta32 := ⟨delta_len, delta_lt, by decide⟩

theorem T0_pres : ∀ g ∈ hfT0, ∀ x : Fin 8330, (x : ℕ) ∈ hfDelta32 → (g x : ℕ) ∈ hfDelta32 :=
  genGroup_preserves (fun j hj => (tabRep_T0 j hj).2) fun j hj =>
    hfDelta_pres j (hfT0Tabs_size ▸ hj)

@[expose] def phi : hfT0 →* Equiv.Perm (Fin 32) := pts.restrHom hfT0 T0_pres

theorem card_range_phi : Nat.card phi.range = 2048 := by
  have h : Enumerates phi.range hfT0Enum32.tabs.toList :=
    enumerates_range_restrHom pts T0_pres (fun j hj => (tabRep_T0 j hj).2) hfSylow32_true.2.2.1
  rw [h.card, Array.length_toList, hfSylow32_true.2.2.2.1]

theorem eq_one_of_ker_fix' {k : hfT0} (hk : phi k = 1)
    (hb : ∀ b : Fin 8330, (b : ℕ) < 5 → (k : Equiv.Perm (Fin 8330)) b = b) : k = 1 := by
  have hcard := Subgroup.card_ker_mul_card_range phi
  rw [card_range_phi] at hcard
  have hdvd : Nat.card phi.ker * 2048 ∣ 2048 * 3935925 := by
    rw [hcard, show 2048 * 3935925 = 8060774400 by norm_num, ← card_heAutGroup]
    exact Subgroup.card_dvd_of_le T0_le_R
  have hdvd' : 2048 * Nat.card phi.ker ∣ 2048 * 3935925 :=
    Nat.mul_comm (Nat.card phi.ker) 2048 ▸ hdvd
  have hodd : Odd (Nat.card phi.ker) :=
    Odd.of_dvd_nat (Nat.odd_iff.2 (by norm_num)) (Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd')
  have hko : Odd (orderOf (k : Equiv.Perm (Fin 8330))) := by
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ (MonoidHom.mem_ker.2 hk))
  have hkR : (k : Equiv.Perm (Fin 8330)) ∈ heAutGroup := T0_le_R k.2
  have hsq : (k : Equiv.Perm (Fin 8330)) ^ 2 ∈ heP := by
    have h := Subgroup.sq_mem_of_index_two (H := heP.subgroupOf heAutGroup)
      heP_relIndex_heAutGroup ⟨k, hkR⟩
    rwa [Subgroup.mem_subgroupOf] at h
  obtain ⟨m, hm⟩ := hko
  have hkP : (k : Equiv.Perm (Fin 8330)) ∈ heP := by
    have e : (k : Equiv.Perm (Fin 8330)) = ((k : Equiv.Perm (Fin 8330)) ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = orderOf (k : Equiv.Perm (Fin 8330)) + 1 by omega,
        pow_succ, pow_orderOf_eq_one, one_mul]
    rw [e]
    exact heP.pow_mem hsq _
  exact Subtype.ext (eq_one_of_fix_base hkP hb)

@[expose] def psi (g : hfT0) : List ℕ × List ℕ :=
  ((List.range 32).map fun i => if h : i < 32 then (phi g ⟨i, h⟩ : ℕ) else 0,
    heBase.map fun b => if h : b < 8330 then ((g : Equiv.Perm (Fin 8330)) ⟨b, h⟩ : ℕ) else 0)

theorem psi_one : psi 1 = (List.range 32, heBase) := by
  simp only [psi, map_one, Equiv.Perm.coe_one, id_eq, OneMemClass.coe_one]
  refine Prod.ext ?_ ?_
  · conv_rhs => rw [← List.map_id (List.range 32)]
    exact List.map_congr_left fun i hi => by simp [List.mem_range.1 hi]
  · conv_rhs => rw [← List.map_id heBase]
    exact List.map_congr_left fun b hb => by
      have : b < 5 := by simp [heBase] at hb; omega
      simp [show b < 8330 by omega]

theorem psi_mul {j : ℕ} (hj : j < 6) (x y : hfT0) (hx : (x : Equiv.Perm (Fin 8330)) = hfT0L j) :
    psi (x * y) = ((psi y).1.map (fun x => (hfT0Tabs32[j]!)[x]!),
      (psi y).2.map (fun x => (hfT0Tabs[j]!)[x]!)) := by
  have hj' : j < hfT0Tabs.size := by rw [hfT0Tabs_size]; exact hj
  have hrep : Rep 8330 hfT0Tabs[j]! x := hx ▸ (tabRep_T0 j hj').2
  have hres : Rep 32 hfT0Tabs32[j]! (phi x) := by
    have h := pts.tabRep_restrHom hfT0 T0_pres x hrep
    rw [hfT0Tabs32, getElem!_map_eq _ _ hj']
    exact h.2
  simp only [psi, List.map_map]
  refine Prod.ext (List.map_congr_left fun i hi => ?_) (List.map_congr_left fun b hb => ?_)
  · have hi32 : i < 32 := List.mem_range.1 hi
    simp only [Function.comp_apply, hi32, dite_true, map_mul, Equiv.Perm.mul_apply]
    exact (hres _).symm
  · have hb5 : b < 8330 := by simp [heBase] at hb; omega
    simp only [Function.comp_apply, hb5, dite_true, Subgroup.coe_mul, Equiv.Perm.mul_apply]
    exact (hrep _).symm

theorem psi_mem {S : Finset (List ℕ × List ℕ)} (h1 : (List.range 32, heBase) ∈ S)
    (hS : ∀ j < 6, ∀ p ∈ S,
      (p.1.map (fun x => (hfT0Tabs32[j]!)[x]!), p.2.map (fun x => (hfT0Tabs[j]!)[x]!)) ∈ S)
    (g : hfT0) : psi g ∈ S := by
  have step : ∀ j < 6, ∀ z : Equiv.Perm (Fin 8330), (∀ hz : z ∈ hfT0, psi ⟨z, hz⟩ ∈ S) →
      ∀ hz : hfT0L j * z ∈ hfT0, psi ⟨hfT0L j * z, hz⟩ ∈ S := by
    intro j hj z ih hz
    have hxm : hfT0L j ∈ hfT0 := subset_closure ⟨j, by rw [hfT0Tabs_size]; exact hj, rfl⟩
    have hzm : z ∈ hfT0 := by simpa using hfT0.mul_mem (hfT0.inv_mem hxm) hz
    have e : (⟨hfT0L j * z, hz⟩ : hfT0) = ⟨hfT0L j, hxm⟩ * ⟨z, hzm⟩ := rfl
    rw [e, psi_mul hj _ _ rfl]
    exact hS j hj _ (ih hzm)
  obtain ⟨g, hg⟩ := g
  refine Subgroup.closure_induction_left (p := fun z _ => ∀ hz : z ∈ hfT0, psi ⟨z, hz⟩ ∈ S)
    (fun _ => by rw [show (⟨1, _⟩ : hfT0) = 1 from rfl, psi_one]; exact h1) ?_ ?_ hg hg
  · rintro _ ⟨j, hj, rfl⟩ y _ ih
    exact step j (hfT0Tabs_size ▸ hj) y ih
  · rintro _ ⟨j, hj, rfl⟩ y _ ih
    have hj6 : j < 6 := hfT0Tabs_size ▸ hj
    have hpow : ∀ k : ℕ, ∀ hz : hfT0L j ^ k * y ∈ hfT0, psi ⟨hfT0L j ^ k * y, hz⟩ ∈ S := by
      intro k
      induction k with
      | zero => simpa using ih
      | succ k ihk =>
        intro hz
        have e : hfT0L j ^ (k + 1) * y = hfT0L j * (hfT0L j ^ k * y) := by rw [pow_succ', mul_assoc]
        have hz' : hfT0L j * (hfT0L j ^ k * y) ∈ hfT0 := by
          rw [← e]
          exact hz
        have e' : (⟨hfT0L j ^ (k + 1) * y, hz⟩ : hfT0) = ⟨hfT0L j * (hfT0L j ^ k * y), hz'⟩ :=
          Subtype.ext e
        rw [e']
        exact step j hj6 _ ihk hz'
    have hinv : (hfT0L j)⁻¹ = hfT0L j ^ (orderOf (hfT0L j) - 1) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos _), pow_orderOf_eq_one]
    intro hz
    have hz' : hfT0L j ^ (orderOf (hfT0L j) - 1) * y ∈ hfT0 := by
      rw [← hinv]
      exact hz
    have e : (⟨(hfT0L j)⁻¹ * y, hz⟩ : hfT0) = ⟨hfT0L j ^ (orderOf (hfT0L j) - 1) * y, hz'⟩ :=
      Subtype.ext (congrArg (· * y) hinv)
    rw [e]
    exact hpow _ hz'

theorem card_T0 : Nat.card hfT0 = 2048 := by
  obtain ⟨S, hS, h1, hcl⟩ := hfS_closed
  have hinj : Function.Injective fun g : hfT0 => (⟨psi g, psi_mem h1 hcl g⟩ : S) := by
    intro g g' h
    have e := congrArg Subtype.val h
    simp only [psi, Prod.mk.injEq, List.map_inj_left] at e
    have hphi : phi g = phi g' := by
      ext i
      have := e.1 i (List.mem_range.2 i.2)
      simpa [i.2] using this
    have hbase : ∀ b : Fin 8330, (b : ℕ) < 5 →
        (g : Equiv.Perm (Fin 8330)) b = (g' : Equiv.Perm (Fin 8330)) b := by
      intro b hb5
      have := e.2 b (by simp [heBase]; omega)
      exact Fin.ext (by simpa [b.2] using this)
    have hk := eq_one_of_ker_fix' (k := g'⁻¹ * g) (by rw [map_mul, map_inv, hphi, inv_mul_cancel])
      fun b hb => by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hbase b hb]
        exact Equiv.symm_apply_apply _ _
    rw [inv_mul_eq_one] at hk
    exact hk.symm
  have hle : Nat.card hfT0 ≤ 2048 := by
    refine (Nat.card_le_card_of_injective _ hinj).trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hS
  have hge : 2048 ≤ Nat.card hfT0 := by
    rw [← Subgroup.card_ker_mul_card_range phi, card_range_phi]
    exact Nat.le_mul_of_pos_left _ Nat.card_pos
  omega

theorem phi_injective : Function.Injective phi :=
  injective_of_card_range phi (by rw [card_range_phi, card_T0])

@[expose] def XT (t : Tab) : Prop := ∃ g ∈ hfT0, TabRep t g

theorem tabRep_res {t : Tab} {g : Equiv.Perm (Fin 8330)} (hg : g ∈ hfT0) (ht : TabRep t g) :
    TabRep (hfRes t) (phi ⟨g, hg⟩) :=
  pts.tabRep_restrHom hfT0 T0_pres ⟨g, hg⟩ ht.2

theorem gen_mem {j : ℕ} (hj : j < hfT0Tabs.size) : hfT0L j ∈ hfT0 := subset_closure ⟨j, hj, rfl⟩

theorem mapHyp : CFSG.KS.BfsMap.MapHyp (leftStep 8330 hfT0Tabs) (leftStep 32 hfT0Tabs32)
    hfT0Tabs.size (idTab 8330) (idTab 32) hfRes XT := by
  refine ⟨?_, ⟨1, one_mem _, TabRep.idTab⟩, fun j hj t ⟨g, hg, ht⟩ =>
    ⟨_, hfT0.mul_mem (gen_mem hj) hg, (tabRep_T0 j hj).comp ht⟩, fun j hj t ⟨g, hg, ht⟩ => ?_,
    fun a b ⟨g, hg, ha⟩ ⟨g', hg', hb⟩ e => ?_⟩
  · have h := tabRep_res (one_mem hfT0) TabRep.idTab
    rw [show (⟨1, one_mem hfT0⟩ : hfT0) = 1 from rfl, map_one] at h
    exact h.tab_eq TabRep.idTab
  · have h1 := tabRep_res (hfT0.mul_mem (gen_mem hj) hg) ((tabRep_T0 j hj).comp ht)
    have e : (⟨hfT0L j * g, hfT0.mul_mem (gen_mem hj) hg⟩ : hfT0) = ⟨hfT0L j, gen_mem hj⟩ * ⟨g, hg⟩ :=
      rfl
    rw [e, map_mul] at h1
    have h2 := (tabRep_res (gen_mem hj) (tabRep_T0 j hj)).comp (tabRep_res hg ht)
    have hg32 : hfT0Tabs32[j]! = hfRes hfT0Tabs[j]! := by
      rw [hfT0Tabs32]
      exact getElem!_map_eq _ _ hj
    unfold leftStep
    rw [hg32]
    exact h1.tab_eq h2
  · have hp : phi ⟨g, hg⟩ = phi ⟨g', hg'⟩ := (tabRep_res hg ha).perm_eq (e ▸ tabRep_res hg' hb)
    have hgg := congrArg Subtype.val (phi_injective hp)
    simp only at hgg
    subst hgg
    exact ha.tab_eq hb

theorem enumT0_ok : enumOK 8330 hfT0Tabs hfT0Enum = true ∧ hfT0Enum.tabs.size = 2048 := by
  have h := CFSG.KS.BfsMap.enumBFS_map (by rw [hfT0Tabs32, Array.size_map]) mapHyp 2048
    hfSylow32_true.2.2.1
  exact ⟨h.1, h.2.trans hfSylow32_true.2.2.2.1⟩

end CertificateChecks.KernelLC.HeFix2329

end
