module

public import CFSG.LargeExtraspecial.AS35WQP45Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import Certificates.Data.Kernel.QP45W.Defs
public import Certificates.Kernel.ONanSmall.P43P
public import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import Certificates.Kernel.QP45W.Checks
import Certificates.Kernel.Sporadic.PSp45.Facts
import CFSG.Certificates.Kernel.LocalQTCovPerm
import CFSG.Certificates.NativeSchreierCard

public section

namespace Certificates.Kernel.QP45W

open Subgroup CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.Sporadic.Schreier CFSG.GH74.KGroups.NativeChecks CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.KC.QP45W CFSG.Certificates.Kernel.PkCV CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.LargeExtraspecial.AS35W
  Certificates.Kernel.ONanSmall

theorem pin (j i : Fin 45) : (tauFun j i).val = T j.val i.val := by
  have h := ch21296_pin
  unfold pinB at h
  exact Nat.eq_of_beq_eq_true
    (List.all_eq_true.1 (List.all_eq_true.1 h j (List.mem_finRange j)) i (List.mem_finRange i))

theorem pinY (i : Fin 45) : (y45 i).val = fd6 yRow i.val := by
  have h := ch21296_pinY
  unfold pinYB at h
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 h i (List.mem_finRange i))

theorem tauPerm_apply (j i : Fin 45) : tauPerm j i = tauFun j i := rfl

theorem x45_apply (k : Fin 45) : x45 k = tauFun 0 k := rfl

theorem x45_val (k : Fin 45) : (x45 k).val = T 0 k.val := by
  rw [x45_apply]
  exact pin 0 k

theorem app_inv (g : Equiv.Perm (Fin 45)) (i : Fin 45) : g (g⁻¹ i) = i := by
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

theorem conj_of_conjT {g : Equiv.Perm (Fin 45)} {gf : ℕ → ℕ} (hg : ∀ k, (g k).val = gf k.val)
    (h : conjT gf = true) (j : Fin 45) : g * tauPerm j * g⁻¹ = tauPerm (g j) := by
  refine Equiv.ext fun i => Fin.ext ?_
  unfold conjT allB at h
  have hc := Nat.eq_of_beq_eq_true (List.all_eq_true.1 (List.all_eq_true.1 h j.val
    (List.mem_range.2 j.2)) (g⁻¹ i).val (List.mem_range.2 (g⁻¹ i).2))
  simp only [Equiv.Perm.mul_apply, tauPerm_apply]
  calc (g (tauFun j (g⁻¹ i))).val = gf (T j.val (g⁻¹ i).val) := by rw [hg, pin]
    _ = T (gf j.val) (gf (g⁻¹ i).val) := hc
    _ = (tauFun (g j) i).val := by
      rw [pin, hg j, ← hg (g⁻¹ i), app_inv]

theorem orig_eq : QP45.originalSubgroup = closure {g | g ∈ [tab x45, tab y45]} := by
  rw [CertificateChecks.KernelSpor.PSp45.qp_eq, certificate_originalSubgroup]

theorem conj_mem {h : Equiv.Perm (Fin 45)} (hh : h ∈ QP45.originalSubgroup) :
    ∀ j, h * tauPerm j * h⁻¹ = tauPerm (h j) := by
  rw [orig_eq] at hh
  induction hh using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, tab_eq] at hg
    rcases hg with rfl | rfl
    · exact conj_of_conjT x45_val ch21296_conjX
    · exact conj_of_conjT pinY ch21296_conjY
  | one => intro j; simp
  | mul a b _ _ ha hb =>
    intro j
    have e : a * b * tauPerm j * (a * b)⁻¹ = a * (b * tauPerm j * b⁻¹) * a⁻¹ := by group
    rw [e, hb, ha]
    rfl
  | inv a _ ha =>
    intro j
    have h1 := ha (a⁻¹ j)
    rw [app_inv] at h1
    rw [inv_inv, ← h1]
    group

theorem eq_one_of_idT {σ : Equiv.Perm (Fin 45)} {F : ℕ → ℕ} (hσ : ∀ k, (σ k).val = F k.val)
    (h : idT F = true) : σ = 1 :=
  Equiv.ext fun i => Fin.ext ((hσ i).trans
    (Nat.eq_of_beq_eq_true (List.all_eq_true.1 h i.val (List.mem_range.2 i.2))))

theorem ord_x (j : Fin 45) : x45 * tauPerm j = 1 ∨ x45 * tauPerm j * (x45 * tauPerm j) = 1 ∨
    x45 * tauPerm j * (x45 * tauPerm j * (x45 * tauPerm j)) = 1 := by
  have hc : ∀ k, ((x45 * tauPerm j) k).val = T 0 (T j.val k.val) := fun k => by
    rw [Equiv.Perm.mul_apply, tauPerm_apply, ← pin j k]
    exact x45_val _
  have hc2 : ∀ k, ((x45 * tauPerm j * (x45 * tauPerm j)) k).val =
      T 0 (T j.val (T 0 (T j.val k.val))) := fun k => by
    rw [Equiv.Perm.mul_apply, hc, hc]
  have hc3 : ∀ k, ((x45 * tauPerm j * (x45 * tauPerm j * (x45 * tauPerm j))) k).val =
      T 0 (T j.val (T 0 (T j.val (T 0 (T j.val k.val))))) := fun k => by
    rw [Equiv.Perm.mul_apply, hc, hc2]
  have h0 := ch21296_ord3
  unfold ord3T allB at h0
  have h := List.all_eq_true.1 h0 j.val (List.mem_range.2 j.2)
  rw [Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact Or.inl (eq_one_of_idT (F := fun i => T 0 (T j.val i)) hc h)
  · exact Or.inr (Or.inl (eq_one_of_idT (F := fun i => T 0 (T j.val (T 0 (T j.val i)))) hc2 h))
  · exact Or.inr (Or.inr (eq_one_of_idT
      (F := fun i => T 0 (T j.val (T 0 (T j.val (T 0 (T j.val i)))))) hc3 h))

theorem x45_mul_self : x45 * x45 = 1 := Equiv.ext fun j => by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, x45_apply, x45_apply]
  exact tauFun_tauFun 0 j

theorem x45_ne_one : x45 ≠ 1 := by
  intro h
  have hm := ch21296_moves
  unfold movesT at hm
  obtain ⟨i, hi, hne⟩ := List.any_eq_true.1 hm
  have hi' := List.mem_range.1 hi
  have e : (x45 ⟨i, hi'⟩).val = T 0 i := x45_val ⟨i, hi'⟩
  rw [h, Equiv.Perm.one_apply] at e
  rw [← e] at hne
  simp at hne


@[expose] def cnt (s : Equiv.Perm (Fin 45)) : ℕ :=
  ((elemsT QP45).filter fun g => decide (g * s = s * g)).length

theorem cnt_eq_card (s : Equiv.Perm (Fin 45)) :
    cnt s = Nat.card {g : QP45.originalSubgroup // (g : Equiv.Perm (Fin 45)) * s = s * g} :=
  (card_filter QP45 QP45_ok (fun g => g * s = s * g)).symm

theorem conj_comm_iff {G : Type*} [Group G] (g h s : G) :
    g * h * g⁻¹ * (g * s * g⁻¹) = g * s * g⁻¹ * (g * h * g⁻¹) ↔ h * s = s * h := by
  have e1 : g * h * g⁻¹ * (g * s * g⁻¹) = g * (h * s) * g⁻¹ := by group
  have e2 : g * s * g⁻¹ * (g * h * g⁻¹) = g * (s * h) * g⁻¹ := by group
  rw [e1, e2, mul_left_inj, mul_right_inj]

theorem cnt_conj {g : Equiv.Perm (Fin 45)} (hg : g ∈ QP45.originalSubgroup)
    (s : Equiv.Perm (Fin 45)) : cnt (g * s * g⁻¹) = cnt s := by
  rw [cnt_eq_card, cnt_eq_card]
  refine (Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj (⟨g, hg⟩ : QP45.originalSubgroup)).toEquiv
    fun h => ?_)).symm
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, Subgroup.coe_mul,
    Subgroup.coe_inv]
  exact (conj_comm_iff g h s).symm

theorem cnt_ev (r : CV 45) : cnt (ev r) = (centC (elemsC QP45) r).length := by
  unfold cnt centC
  rewrite [elemsT_eq_elemsC, List.filter_map, List.length_map]
  refine congrArg List.length (List.filter_congr fun c _ => ?_)
  rewrite [Function.comp_apply, eq22C_eq, ← ev_mul, ← ev_mul]
  exact decide_eq_decide.2 ev_injective.eq_iff

theorem cover {s : Equiv.Perm (Fin 45)} (hs : s ∈ QP45.originalSubgroup) (h2 : s * s = 1)
    (h1 : s ≠ 1) : ∃ g ∈ QP45.originalSubgroup, ∃ r ∈ P43P.reps, g * s * g⁻¹ = ev r := by
  have hs' := (mem_elemsT QP45 QP45_ok s).2 hs
  rw [elemsT_eq_elemsC] at hs'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hs'
  have hc2 : c * c = 1 := ev_injective (by rw [ev_mul, h2, ev_one])
  have hc1 : c ≠ 1 := fun e => h1 (by rw [e, ev_one])
  have hcov := (pickRun_cover (elemsC QP45) invC conjC (genC QP45) invC_eq conjC_eq
    (genC_mem QP45) P43P.one_mem (elemsC QP45) [] _ P43P.reps P43P.pick).2 c hc ⟨hc2, hc1⟩
  unfold isCovered at hcov
  obtain ⟨g, hg, hr⟩ := List.any_eq_true.1 hcov
  obtain ⟨r, hr, he⟩ := List.any_eq_true.1 hr
  refine ⟨ev g, ?_, r, hr, ?_⟩
  · refine (mem_elemsT QP45 QP45_ok _).1 ?_
    rw [elemsT_eq_elemsC]
    exact List.mem_map_of_mem hg
  · rw [← ev_mul, ← ev_inv, ← ev_mul, of_decide_eq_true he]

theorem reps_eq : ∃ a b, P43P.reps = [a, b] ∧ (centC (elemsC QP45) a).length = 576 ∧
    (centC (elemsC QP45) b).length = 96 := by
  have h := congrArg (List.map List.length) P43P.cent_ok
  rw [List.map_map, P43P.cents, List.map_map] at h
  have hC : CFSG.KD.ONS.P43P.C.map (List.length ∘ List.map P43P.el) =
      CFSG.KD.ONS.P43P.C.map List.length := by
    refine List.map_congr_left fun l _ => ?_
    simp
  rw [hC, ch21296_cents] at h
  rcases e : P43P.reps with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rw [e] at h; simp at h
  · rw [e] at h; simp at h
  · rw [e] at h
    simp only [List.map_cons, List.map_nil, List.cons.injEq, Function.comp_apply] at h
    exact ⟨a, b, rfl, h.1, h.2.1⟩
  · rw [e] at h; simp at h

theorem x45_mem : x45 ∈ QP45.originalSubgroup :=
  CertificateChecks.KernelSpor.PSp45.gens_mem x45 (by simp)

theorem cnt_x : 576 ≤ cnt x45 := by
  rw [cnt_eq_card]
  have hP : Nat.card QP45.originalSubgroup = 25920 := by
    rw [card_group QP45 QP45_ok, QP45_valid.2]
  have horb : Nat.card (MulAction.orbit QP45.originalSubgroup (0 : Fin 45)) ≤ 45 := by
    have := Nat.card_mono (Set.finite_univ) (Set.subset_univ
      (MulAction.orbit QP45.originalSubgroup (0 : Fin 45)))
    simpa using this
  have hmul := (MulAction.stabilizer QP45.originalSubgroup (0 : Fin 45)).card_mul_index
  rw [MulAction.index_stabilizer, hP] at hmul
  have hst : 576 ≤ Nat.card (MulAction.stabilizer QP45.originalSubgroup (0 : Fin 45)) := by
    have h1 := Nat.mul_le_mul_left
      (Nat.card (MulAction.stabilizer QP45.originalSubgroup (0 : Fin 45))) horb
    rw [← Nat.card_coe_set_eq] at hmul
    rw [hmul] at h1
    omega
  refine hst.trans (Nat.card_le_card_of_injective
    (fun h => ⟨(h : QP45.originalSubgroup), ?_⟩) ?_)
  · have h0 : ((h : QP45.originalSubgroup) : Equiv.Perm (Fin 45)) 0 = 0 := h.2
    have hc := conj_mem (h : QP45.originalSubgroup).2 0
    rw [h0] at hc
    have hx : x45 = tauPerm 0 := rfl
    rw [← hx] at hc
    calc _ = ((h : QP45.originalSubgroup) : Equiv.Perm (Fin 45)) * x45 *
          ((h : QP45.originalSubgroup) : Equiv.Perm (Fin 45))⁻¹ *
          ((h : QP45.originalSubgroup) : Equiv.Perm (Fin 45)) := by group
      _ = _ := by rw [hc]
  · intro a b hab
    have e := congrArg Subtype.val hab
    exact Subtype.ext e

theorem qp45InvCheck_true : qp45InvCheck = true := by
  unfold qp45InvCheck qp45InvCheckL
  rewrite [enumA_eq]
  refine List.all_eq_true.2 fun sA hsA => ?_
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hsA
  have hsP := (mem_elemsT QP45 QP45_ok s).1 hs
  have hrs := rep_toA s
  have hfilt : ((List.map toA (elemsT QP45)).filter fun g =>
      eqA 45 (compA 45 g (toA s)) (compA 45 (toA s) g)).length = cnt s := by
    unfold cnt
    rewrite [List.filter_map, List.length_map]
    refine congrArg List.length (List.filter_congr fun g _ => ?_)
    rewrite [Function.comp_apply]
    exact eqA_eq_decide (rep_compA (rep_toA g) hrs) (rep_compA hrs (rep_toA g))
  rewrite [hfilt, Bool.or_eq_true, Bool.or_eq_true]
  by_cases hinv : s * s = 1 ∧ s ≠ 1
  · obtain ⟨a, b, hab, ha, hb⟩ := reps_eq
    obtain ⟨g, hg, r, hr, hgr⟩ := cover hsP hinv.1 hinv.2
    have hcs : cnt s = (centC (elemsC QP45) r).length := by
      rw [← cnt_conj hg s, hgr, cnt_ev]
    rw [hab] at hr
    rcases List.mem_pair.1 hr with rfl | rfl
    · refine Or.inl (Or.inr ?_)
      obtain ⟨g', hg', r', hr', hgr'⟩ := cover x45_mem x45_mul_self x45_ne_one
      have hcx : cnt x45 = (centC (elemsC QP45) r').length := by
        rw [← cnt_conj hg' x45, hgr', cnt_ev]
      rw [hab] at hr'
      have hra : r' = r := by
        rcases List.mem_pair.1 hr' with rfl | rfl
        · rfl
        · have := cnt_x
          omega
      rw [hra] at hgr'
      set h := g⁻¹ * g'
      have hhP : h ∈ QP45.originalSubgroup :=
        QP45.originalSubgroup.mul_mem (QP45.originalSubgroup.inv_mem hg) hg'
      have heq : h * x45 = s * h := by
        have e1 : s = g⁻¹ * (g * s * g⁻¹) * g := by group
        rw [e1, hgr, ← hgr']
        simp only [h]
        group
      rw [List.any_map]
      refine List.any_eq_true.2 ⟨h, (mem_elemsT QP45 QP45_ok h).2 hhP, ?_⟩
      rw [Function.comp_apply]
      exact (eqA_iff (rep_compA (rep_toA h) (rep_toA x45)) (rep_compA hrs (rep_toA h))).2 heq
    · refine Or.inr ?_
      rw [hcs, hb]
      decide
  · refine Or.inl (Or.inl ?_)
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro h
    apply hinv
    unfold invA45 at h
    rw [Bool.and_eq_true, eqA_iff (rep_compA hrs hrs) rep_idA, Bool.not_eq_true',
      Bool.eq_false_iff, Ne, eqA_iff hrs rep_idA] at h
    exact h

theorem qp45ProdCheck_true : qp45ProdCheck = true := by
  unfold qp45ProdCheck qp45ProdCheckL
  rewrite [enumA_eq]
  refine List.all_eq_true.2 fun gA hgA => ?_
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hgA
  have hgP := (mem_elemsT QP45 QP45_ok g).1 hg
  have hri := CFSG.KC.LQT.Cov.Perm.rep_invCand (rep_toA g)
  rw [Bool.and_eq_true]
  refine ⟨CFSG.KC.LQT.Cov.Perm.isInvA_of_rep (rep_toA g) hri, ?_⟩
  have hc := rep_compA (rep_toA x45) (rep_compA (rep_compA (rep_toA g) (rep_toA x45)) hri)
  have hcm : g * x45 * g⁻¹ = tauPerm (g 0) := conj_mem hgP 0
  rw [hcm] at hc
  unfold ord123A45
  rw [Bool.or_eq_true, Bool.or_eq_true]
  rcases ord_x (g 0) with h | h | h
  · exact Or.inl (Or.inl ((eqA_iff hc rep_idA).2 h))
  · exact Or.inl (Or.inr ((eqA_iff (rep_compA hc hc) rep_idA).2 h))
  · exact Or.inr ((eqA_iff (rep_compA hc (rep_compA hc hc)) rep_idA).2 h)

end Certificates.Kernel.QP45W
