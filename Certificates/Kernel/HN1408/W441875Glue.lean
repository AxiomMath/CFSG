module

public import Certificates.Kernel.HN1408.W441875Base
public import Certificates.Kernel.HN1408.InvClassK
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Basic

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.W441875

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.CompatModel
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

noncomputable abbrev Kc : Subgroup (Equiv.Perm (Fin 1408)) :=
  P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408)))

theorem bIf_tt {t e : Bool} (h : bIf(true, t, e) = true) : t = true := h

theorem in2AK_iff {t : Nat} : in2AK t = true ↔ t = 0 ∨ t = 2 ∨ t = 3 := by
  unfold in2AK
  rcases Nat.lt_or_ge t 4 with h | h
  · interval_cases t <;> decide
  · have e0 : Nat.beq t 0 = false := Bool.eq_false_iff.2 fun h' => by
      have := Nat.eq_of_beq_eq_true h'
      omega
    have e2 : Nat.beq t 2 = false := Bool.eq_false_iff.2 fun h' => by
      have := Nat.eq_of_beq_eq_true h'
      omega
    have e3 : Nat.beq t 3 = false := Bool.eq_false_iff.2 fun h' => by
      have := Nat.eq_of_beq_eq_true h'
      omega
    rw [e0, e2, e3]
    exact ⟨fun h' => absurd h' (by decide), fun h' => by omega⟩

theorem in2A_of_conj (hnc : ∀ i j : Fin 5, i ≠ j → ¬ IsConj (vH i) (vH j)) {t : Fin 5}
    {y : ↥P1408} (hc : IsConj (vH t) y) : In2A y ↔ in2AK t.val = true := by
  rw [in2AK_iff]
  have key : ∀ s : Fin 5, IsConj (vH s) y → (s.val = t.val) := by
    intro s hs
    by_contra hne
    exact hnc s t (fun e => hne (congrArg Fin.val e)) (hs.trans hc.symm)
  constructor
  · rintro (h | h | h)
    · have := key 0 h
      omega
    · have := key 2 h
      omega
    · have := key 3 h
      omega
  · intro h
    have e : t = 0 ∨ t = 2 ∨ t = 3 := by
      rcases h with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases e with rfl | rfl | rfl
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)

section Card

variable (hK : Nat.card cK = 3840)
include hK

theorem conj_tgt {k : Nat} (hk : k < 3840) (h0 : R k ≠ 0) :
    (R k - 1) % 16 < 15 ∧ ∃ ht : RT ((R k - 1) % 16) < 5,
      IsConj (vH ⟨RT ((R k - 1) % 16), ht⟩) (elH hk) ∧
      ∃ g ∈ cK, el k = g * el (RK ((R k - 1) % 16)) * g⁻¹ := by
  obtain ⟨hc15, c', hc', he⟩ := row_conj hK hk h0
  obtain ⟨hr, ht, hconj⟩ := rep_conj hc15
  have e : el k = el c' * el (RK ((R k - 1) % 16)) * (el c')⁻¹ := by
    rw [he, mul_inv_cancel_right]
  refine ⟨hc15, ht, hconj.trans (isConj_iff.2 ⟨elH hc', Subtype.ext ?_⟩), el c', el_mem hc', e⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, elH_val, elH_val, elH_val]
  exact e.symm

theorem in2A_of_row (hnc : ∀ i j : Fin 5, i ≠ j → ¬ IsConj (vH i) (vH j)) {y : Nat}
    (hy : y < 3840) (h : rowIn2A R RT y = true) : In2A (elH hy) := by
  unfold rowIn2A at h
  simp only [strictB_app] at h
  obtain ⟨h0, h1⟩ := mkA h
  obtain ⟨-, ht, hconj, -⟩ := conj_tgt hK hy (bIf_ne_zero h0)
  exact (in2A_of_conj hnc hconj).2 h1

theorem cover (hnc : ∀ i j : Fin 5, i ≠ j → ¬ IsConj (vH i) (vH j)) {a : ↥P1408} (ha : In2A a)
    (haK : (a : Equiv.Perm (Fin 1408)) ∈ cK) :
    ∃ c < 15, in2AK (RT c) = true ∧
      ∃ g ∈ cK, (a : Equiv.Perm (Fin 1408)) = g * el (RK c) * g⁻¹ := by
  obtain ⟨k, hk, hak⟩ := exists_el hK haK
  have hinv : ∀ s : Fin 5, IsConj (vH s) a → el k * el k = 1 ∧ el k ≠ 1 := by
    intro s hs
    obtain ⟨g, hg⟩ := isConj_iff.1 hs
    obtain ⟨h1, h2⟩ := vH_inv s
    have e : el k =
        (g : Equiv.Perm (Fin 1408)) * (vH s : ↥P1408) * (g : Equiv.Perm (Fin 1408))⁻¹ := by
      rw [← hak, ← hg]
      rfl
    rw [e]
    refine ⟨?_, fun e1 => h2 ?_⟩
    · rw [show (g : Equiv.Perm (Fin 1408)) * (vH s : ↥P1408) * (g : Equiv.Perm (Fin 1408))⁻¹ *
          ((g : Equiv.Perm (Fin 1408)) * (vH s : ↥P1408) * (g : Equiv.Perm (Fin 1408))⁻¹) =
          (g : Equiv.Perm (Fin 1408)) * (((vH s : ↥P1408) : Equiv.Perm (Fin 1408)) *
            (vH s : ↥P1408)) * (g : Equiv.Perm (Fin 1408))⁻¹ by group, h1, mul_one, mul_inv_cancel]
    · have := congrArg (fun u => (g : Equiv.Perm (Fin 1408))⁻¹ * u * g) e1
      simp only [mul_one, inv_mul_cancel] at this
      rw [← this]
      group
  have hi : el k * el k = 1 ∧ el k ≠ 1 := by
    rcases ha with h | h | h
    · exact hinv 0 h
    · exact hinv 2 h
    · exact hinv 3 h
  have h0 : R k ≠ 0 := fun h0 => row_zero hK hk h0 hi
  obtain ⟨hc15, ht, hconj, g, hg, he⟩ := conj_tgt hK hk h0
  have hconj' : IsConj (vH ⟨RT ((R k - 1) % 16), ht⟩) a := by
    have e : elH hk = a := Subtype.ext hak.symm
    rwa [e] at hconj
  exact ⟨_, hc15, (in2A_of_conj hnc hconj').1 ha, g, hg, hak.trans he⟩

noncomputable def prodW (Yc : Nat) (w : List Nat) : Equiv.Perm (Fin 1408) :=
  (w.map fun i => el (Tr2.fd Yc i)).prod

omit hK in
theorem prodW_spec {Yc : Nat} (hY : ∀ i < 4, Tr2.fd Yc i < 3840) {w : List Nat}
    (hw : ∀ i ∈ w, i < 4) :
    prodW Yc w ∈ closure (Set.image (fun i => el (Tr2.fd Yc i)) {i | i < 4}) ∧ prodW Yc w ∈ cK ∧
      ∀ p (hp : p < 1408), (prodW Yc w ⟨p, hp⟩).val = evW Yc w p := by
  induction w with
  | nil =>
    refine ⟨one_mem _, one_mem _, fun p hp => rfl⟩
  | cons i w ih =>
    obtain ⟨h1, h2, h3⟩ := ih fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have hi : i < 4 := hw i List.mem_cons_self
    have hyi := hY i hi
    have e : prodW Yc (i :: w) = el (Tr2.fd Yc i) * prodW Yc w := by
      simp only [prodW, List.map_cons, List.prod_cons]
    rw [e]
    refine ⟨mul_mem (subset_closure ⟨i, hi, rfl⟩) h1, mul_mem (el_mem hyi) h2, fun p hp => ?_⟩
    have e2 : evW Yc (i :: w) p = ev (Tr2.fd Yc i) (evW Yc w p) := rfl
    have hlt : evW Yc w p < 1408 := by
      rw [← h3 p hp]
      exact Fin.isLt _
    have h4 : prodW Yc w ⟨p, hp⟩ = ⟨evW Yc w p, hlt⟩ := Fin.ext (h3 p hp)
    rw [e2, Equiv.Perm.mul_apply, h4, el_pt hyi hlt]

omit hK in
theorem pow_pt {r y : Nat} (hr : r < 3840) (hy : y < 3840) (n : Nat) {p : Nat} (hp : p < 1408) :
    (((el r * el y) ^ n) ⟨p, hp⟩).val = evPow2 r y n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : evPow2 r y (n + 1) p = ev r (ev y (evPow2 r y n p)) := rfl
    have hlt : evPow2 r y n p < 1408 := by
      rw [← ih]
      exact Fin.isLt _
    have h1 : ((el r * el y) ^ n) ⟨p, hp⟩ = ⟨evPow2 r y n p, hlt⟩ := Fin.ext ih
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, e, h1, el_apply hy hlt,
      el_pt hr (ev_lt hy hlt)]

theorem row_spec (hnc : ∀ i j : Fin 5, i ≠ j → ¬ IsConj (vH i) (vH j)) {c : Nat} (hc : c < 15)
    (h2A : in2AK (RT c) = true) :
    (∀ i < 4, ∃ hy : Tr2.fd (Y c) i < 3840,
      In2A (elH hy) ∧ orderOf (el (RK c) * el (Tr2.fd (Y c) i)) ≠ 5) ∧
      closure (Set.image (fun i => el (Tr2.fd (Y c) i)) {i | i < 4}) = cK := by
  have h := allN_spec ch441875_rowY c hc
  unfold rowYK at h
  rw [h2A] at h
  have h' := bIf_tt (e := true) h
  simp only [strictB_app] at h'
  obtain ⟨hv, hg⟩ := mkA h'
  have hr : RK c < 3840 := (repK_parts (allN_spec ch441875_rep c hc)).1
  have hvert : ∀ i < 4, Tr2.fd (Y c) i < 3840 ∧ rowIn2A R RT (Tr2.fd (Y c) i) = true ∧
      Tr2.fd (YP c) i < 1408 ∧
        evPow2 (RK c) (Tr2.fd (Y c) i) 5 (Tr2.fd (YP c) i) ≠ Tr2.fd (YP c) i := by
    intro i hi
    have h1 := allN_spec hv i hi
    unfold vertK at h1
    simp only [strictB_app] at h1
    obtain ⟨a, h1⟩ := mkA h1
    obtain ⟨b, h1⟩ := mkA h1
    obtain ⟨d, f⟩ := mkA h1
    refine ⟨Nat.blt_eq.mp a, b, Nat.blt_eq.mp d, fun e => ?_⟩
    rw [e, Nat.beq_refl] at f
    exact absurd f (by decide)
  have hY : ∀ i < 4, Tr2.fd (Y c) i < 3840 := fun i hi => (hvert i hi).1
  refine ⟨fun i hi => ⟨hY i hi, in2A_of_row hK hnc (hY i hi) (hvert i hi).2.1, fun e5 => ?_⟩, ?_⟩
  · obtain ⟨hy, -, hp, hne⟩ := hvert i hi
    have h5 := pow_pt hr hy 5 hp
    have h1 : (el (RK c) * el (Tr2.fd (Y c) i)) ^ 5 = 1 := by
      rw [← e5]
      exact pow_orderOf_eq_one _
    rw [h1] at h5
    exact hne h5.symm
  · refine le_antisymm ((closure_le _).2 ?_) ((closure_le _).2 ?_)
    · rintro _ ⟨i, hi, rfl⟩
      exact el_mem (hY i hi)
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨l, hl, rfl⟩ : ∃ l < classz₁.centGens.length, classz₁.centGens.getD l [] = w := by
        have hw' : w ∈ classz₁.centGens := hw
        obtain ⟨l, hl, e⟩ := List.getElem_of_mem hw'
        exact ⟨l, hl, by rw [List.getD_eq_getElem _ _ hl, e]⟩
      have hl2 : l < 2 := hl
      have hgw := allN_spec hg l hl2
      unfold genWK at hgw
      obtain ⟨hlet, hb⟩ := mkA hgw
      obtain ⟨b0, b1⟩ := base2_parts hb
      have hlet' : ∀ i ∈ CW.getD (2 * c + l) [], i < 4 := fun i hi =>
        Nat.blt_eq.mp (List.all_eq_true.1 hlet i hi)
      obtain ⟨m1, m2, m3⟩ := prodW_spec hY hlet'
      have hG := Tr2.repC_G Cz1T.cz1T_ok hl
      have e : prodW (Y c) (CW.getD (2 * c + l) []) = elemW (classz₁.centGens.getD l []) := by
        refine eq_of_base hK m2 (Tr2.gen_mem hl) (Fin.ext ?_) (Fin.ext ?_)
        · rw [m3 0 (by norm_num), ← repC_pt hG (by norm_num)]
          exact Nat.eq_of_beq_eq_true b0
        · rw [m3 1 (by norm_num), ← repC_pt hG (by norm_num)]
          exact Nat.eq_of_beq_eq_true b1
      rw [← e]
      exact m1

end Card

theorem wit5e_modelK (hP : Nat.card ↥P1408 = 177408000) (a x : ↥P1408) (ha : In2A a)
    (hac : a * pZ₁ = pZ₁ * a) (hxc : x * pZ₁ = pZ₁ * x) :
    x ∈ closure {y : ↥P1408 | y * pZ₁ = pZ₁ * y ∧ In2A y ∧ orderOf (a * y) ≠ 5} := by
  obtain ⟨-, hKcard, hKeq⟩ := Cz1T.z1_facts hP
  have hK : Nat.card cK = 3840 := by
    change Nat.card (Tr2.genC classz₁.centGens) = 3840
    rw [hKeq]
    exact hKcard
  have hnc := CzInv.not_isConj_K hP
  have hmemK : ∀ u : ↥P1408, u * pZ₁ = pZ₁ * u → (u : Equiv.Perm (Fin 1408)) ∈ cK := by
    intro u hu
    change (u : Equiv.Perm (Fin 1408)) ∈ Tr2.genC classz₁.centGens
    rw [hKeq]
    exact Subgroup.mem_inf.2 ⟨u.2, mem_centralizer_singleton_iff.2 (congrArg Subtype.val hu)⟩
  have hcomm : ∀ g ∈ cK, g * elemZ₁ = elemZ₁ * g := by
    intro g hg
    have hg' : g ∈ Kc := by
      change g ∈ Tr2.genC classz₁.centGens at hg
      rwa [hKeq] at hg
    exact mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg').2
  obtain ⟨c, hc, h2A, g, hg, hae⟩ := cover hK hnc ha (hmemK a hac)
  obtain ⟨hy, hcl⟩ := row_spec hK hnc hc h2A
  have hr : RK c < 3840 := (repK_parts (allN_spec ch441875_rep c hc)).1
  set S : Set ↥P1408 := {y | y * pZ₁ = pZ₁ * y ∧ In2A y ∧ orderOf (a * y) ≠ 5} with hS
  let N : Subgroup (Equiv.Perm (Fin 1408)) := (closure S).map P1408.subtype
  let g' : ↥P1408 := ⟨g, cK_le hg⟩
  let ar : ↥P1408 := elH hr
  have hae' : a = g' * ar * g'⁻¹ := Subtype.ext hae
  have hgc : Commute g' pZ₁ := Subtype.ext (hcomm g hg)
  have hconj : ∀ i < 4, g * el (Tr2.fd (Y c) i) * g⁻¹ ∈ N := by
    intro i hi
    obtain ⟨hyi, h2, h5⟩ := hy i hi
    let y' : ↥P1408 := elH hyi
    have hyc : Commute y' pZ₁ := Subtype.ext (hcomm _ (el_mem hyi))
    refine Subgroup.mem_map.2 ⟨g' * y' * g'⁻¹, Subgroup.subset_closure ⟨?_, ?_, ?_⟩, rfl⟩
    · exact ((hgc.mul_left hyc).mul_left hgc.inv_left)
    · exact h2.map_conj g'
    · have e1 : a * (g' * y' * g'⁻¹) = MulAut.conj g' (ar * y') := by
        rw [hae']
        simp only [MulAut.conj_apply]
        group
      rw [e1, MulEquiv.orderOf_eq]
      exact (Subgroup.orderOf_coe (ar * y')).symm.trans_ne h5
  have hx'' : (g⁻¹ * (x : Equiv.Perm (Fin 1408)) * g) ∈
      closure (Set.image (fun i => el (Tr2.fd (Y c) i)) {i | i < 4}) := by
    rw [hcl]
    exact cK.mul_mem (cK.mul_mem (cK.inv_mem hg) (hmemK x hxc)) hg
  have hle : closure (Set.image (fun i => el (Tr2.fd (Y c) i)) {i | i < 4}) ≤
      N.comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact hconj i hi
  have h2 := hle hx''
  rw [Subgroup.mem_comap] at h2
  have e2 : (MulAut.conj g).toMonoidHom (g⁻¹ * (x : Equiv.Perm (Fin 1408)) * g) = x := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e2] at h2
  obtain ⟨y, hy2, hyx⟩ := Subgroup.mem_map.1 h2
  rwa [show y = x from Subtype.ext hyx] at hy2

end CFSG.KD.HN1408.W441875

end
