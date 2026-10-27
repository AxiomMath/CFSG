module

public import Certificates.Kernel.Sporadic.Fi24F3d.Adj
public import CFSG.Certificates.Kernel.Spor.Fi24KnSound
public import CFSG.Certificates.Kernel.Spor.Fi24G2dSound
import Certificates.Kernel.Sporadic.Fi24F3d.SE
import Certificates.Kernel.Sporadic.Fi24F3d.SEF
import Certificates.Kernel.Sporadic.Fi24F3d.SY
import Certificates.Kernel.Sporadic.Fi24F3d.M0
import Certificates.Kernel.Sporadic.Fi24F3d.M1
import Certificates.Kernel.Sporadic.Fi24F3d.M2
import Certificates.Kernel.Sporadic.Fi24F3d.P

public section

namespace CertificateChecks.KernelFi24F3d

open CertificateChecks.KernelFi24 CertificateChecks.KernelCo2 CertificateChecks.KernelFi24Fix
  CertificateChecks.KernelFi24Orb CertificateChecks.KernelFi24G2e CertificateChecks.KernelFi24Ext
  TauCeti TauCeti.Sporadic CFSG.Sporadic.Bridge CFSG.KC.Fi24FixC CFSG.KC.Fi24FixS CFSG.KC.Fi24FixK
  CFSG.KC.Fi24Orb CFSG.KC.Fi24OrbS CFSG.KC.Fi24OrbT CFSG.KC.Fi24G2d CFSG.KC.Fi24G2dS CFSG.KC.Fi24Kn
  CFSG.KC.Fi24KnS CFSG.Sporadic.Fi24 CFSG.KD.Fi24F3d CFSG.KD.Fi24G2e

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local irreducible] CFSG.KD.Fi24G2e.BX CFSG.KD.Fi24Ext.MX CFSG.KD.BrFi24.MT
  CFSG.KD.Fi24Fix.MX

theorem xw_val {w : List ℕ} (hw : ∀ g ∈ w, g < 12) :
    ((xw w : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
      Mt (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG w CFSG.KD.BrFi24.ONE) := by
  rw [(wordMul_τ cn_one w hw).2, mt_one, Matrix.mul_one]

theorem xw_eq_of_beq {u v : List ℕ} (hu : ∀ g ∈ u, g < 12) (hv : ∀ g ∈ v, g < 12)
    (h : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG u CFSG.KD.BrFi24.ONE)
      (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG v CFSG.KD.BrFi24.ONE) = true) : xw u = xw v :=
  Units.ext (by rw [xw_val hu, xw_val hv, Nat.eq_of_beq_eq_true h])

theorem xw_eq_one_of_beq {u : List ℕ} (hu : ∀ g ∈ u, g < 12)
    (h : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG u CFSG.KD.BrFi24.ONE)
      CFSG.KD.BrFi24.ONE = true) : xw u = 1 :=
  Units.ext (by rw [xw_val hu, Nat.eq_of_beq_eq_true h, mt_one]; rfl)

noncomputable abbrev eE : GL (Fin 781) (ZMod 3) := xw WE

noncomputable abbrev eF : GL (Fin 781) (ZMod 3) := xw WF

noncomputable abbrev eY : GL (Fin 781) (ZMod 3) := xw WY

theorem eE_mem : eE ∈ seedGrp := xw_mem (by decide) (by decide)

theorem eF_mem : eF ∈ seedGrp := xw_mem (by decide) (by decide)

theorem eY_mem : eY ∈ seedGrp := xw_mem (by decide) (by decide)

theorem eE_pow5 : eE ^ 5 = 1 := by
  have h := xw_eq_one_of_beq (u := WE ++ WE ++ WE ++ WE ++ WE) (by decide) M0.e5
  simp only [xw_append] at h
  rw [← h]
  simp only [pow_succ, pow_zero, one_mul]

theorem eY_pow7 : eY ^ 7 = 1 := by
  have h := xw_eq_one_of_beq (u := WY ++ WY ++ WY ++ WY ++ WY ++ WY ++ WY) (by decide) M1.y7
  simp only [xw_append] at h
  rw [← h]
  simp only [pow_succ, pow_zero, one_mul]

theorem eEF_comm : eE * eF = eF * eE := by
  have h := xw_eq_of_beq (u := WE ++ WF) (v := WF ++ WE) (by decide) (by decide) M0.ef
  rwa [xw_append, xw_append] at h

theorem eEY_comm : eE * eY = eY * eE := by
  have h := xw_eq_of_beq (u := WE ++ WY) (v := WY ++ WE) (by decide) (by decide) M0.ey
  rwa [xw_append, xw_append] at h

theorem eF_conj : (xw NS)⁻¹ * eE * xw NS = eF := by
  have h := xw_eq_of_beq (u := NS.reverse ++ WE ++ NS) (v := WF) (by decide) (by decide) M1.sw
  rwa [xw_append, xw_append, xw_reverse] at h

theorem xw_WEF : xw WEF = eE * eF := by
  rw [show WEF = WE ++ WF from rfl, xw_append]

theorem eF_pow5 : eF ^ 5 = 1 := by
  have e : ((xw NS)⁻¹ * eE * xw NS) ^ 5 = (xw NS)⁻¹ * eE ^ 5 * xw NS := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  rw [← eF_conj, e, eE_pow5, mul_one, inv_mul_cancel]

theorem eEFk_conj2 : (xw N2)⁻¹ * (eE * eF) * xw N2 = eE * eF ^ 2 := by
  have h := xw_eq_of_beq (u := N2.reverse ++ WEF ++ N2) (v := WE ++ WF ++ WF) (by decide)
    (by decide) M2.n2
  rw [xw_append, xw_append, xw_reverse, xw_WEF, xw_append, xw_append] at h
  rw [h, mul_assoc, ← pow_two]

theorem eEFk_conj3 : (xw N3)⁻¹ * (eE * eF) * xw N3 = eE * eF ^ 3 := by
  have h := xw_eq_of_beq (u := N3.reverse ++ WEF ++ N3) (v := WE ++ WF ++ WF ++ WF) (by decide)
    (by decide) M2.n3
  rw [xw_append, xw_append, xw_reverse, xw_WEF, xw_append, xw_append, xw_append] at h
  rw [h]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem eEFk_conj4 : (xw N4)⁻¹ * (eE * eF) * xw N4 = eE * eF ^ 4 := by
  have h := xw_eq_of_beq (u := N4.reverse ++ WEF ++ N4) (v := WE ++ WF ++ WF ++ WF ++ WF)
    (by decide) (by decide) M2.n4
  rw [xw_append, xw_append, xw_reverse, xw_WEF, xw_append, xw_append, xw_append, xw_append] at h
  rw [h]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem act_xw_iff {w : List ℕ} (hw : ∀ g ∈ w, g < 12) {r : ℕ} (hr : r < N) :
    act (xw w) (ψ r) = ψ r ↔ walk CFSG.KD.Fi24Fix.TG w r = r := by
  rw [← act_inv_eq_iff, act_xw_inv hw hr]
  exact ⟨ψ_inj (walk_lt hw hr) hr, fun h => by rw [h]⟩

theorem eE_ne : eE ≠ 1 := by
  intro h
  have h1 : act eE (ψ 6) = ψ 6 := by rw [h, act_one]
  rw [act_xw_iff (by decide) (by norm_num)] at h1
  have := P.mvE
  rw [h1] at this
  exact absurd this (by simp [negB])

theorem eY_ne : eY ≠ 1 := by
  intro h
  have h1 : act eY (ψ 1) = ψ 1 := by rw [h, act_one]
  rw [act_xw_iff (by decide) (by norm_num)] at h1
  have := P.mvY
  rw [h1] at this
  exact absurd this (by simp [negB])

theorem eF_ne_pow (k : ℕ) : eF ≠ eE ^ k := by
  intro h
  have hE : act eE (ψ 1) = ψ 1 :=
    (act_xw_iff (by decide) (by norm_num)).2 (Nat.eq_of_beq_eq_true P.fE)
  have hF : act eF (ψ 1) = ψ 1 := by rw [h]; exact act_pow_of_act hE k
  rw [act_xw_iff (by decide) (by norm_num)] at hF
  have := P.mF
  rw [hF] at this
  exact absurd this (by simp [negB])

theorem card_E : ((Finset.range 306936).filter fun r => walk CFSG.KD.Fi24Fix.TG WE r = r).card = 36 := by
  rw [card_fix_of_chunks _ _ J.KE (fun c hc => by
      have := SE.all c hc
      unfold okE at this
      rwa [nthN_eq] at this)
    (by have := SE.last; rwa [nthN_eq] at this)]
  decide

theorem card_EF :
    ((Finset.range 306936).filter fun r => walk CFSG.KD.Fi24Fix.TG WEF r = r).card = 36 := by
  rw [card_fix_of_chunks _ _ J.KEF (fun c hc => by
      have := SEF.all c hc
      unfold okEF at this
      rwa [nthN_eq] at this)
    (by have := SEF.last; rwa [nthN_eq] at this)]
  decide

theorem card_Y : ((Finset.range 306936).filter fun r => walk CFSG.KD.Fi24Fix.TG WY r = r).card = 21 := by
  rw [card_fix_of_chunks _ _ J.KY (fun c hc => by
      have := SY.all c hc
      unfold okY at this
      rwa [nthN_eq] at this)
    (by have := SY.last; rwa [nthN_eq] at this)]
  decide

theorem wordsC {l : List (List ℕ)} {m : ℕ} (hl : l.length = m)
    (h : ∀ w ∈ l, (∀ g ∈ w, g < 12) ∧ w.length % 2 = 0) :
    ∀ i < m, (∀ g ∈ nthW l i, g < 12) ∧ (nthW l i).length % 2 = 0 := by
  intro i hi
  rw [nthW_eq, List.getD_eq_getElem _ _ (by omega)]
  exact h _ (List.getElem_mem _)

theorem lst {w : List ℕ} {L : ℕ → ℕ} {m : ℕ}
    (h : ∀ j < m, L j < 306936 ∧ walk CFSG.KD.Fi24Fix.TG w (L j) = L j ∧ (j + 1 < m → L j < L (j + 1))) :
    ∀ j < m, L j < N ∧ (j + 1 < m → L j < L (j + 1)) := fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

theorem knE : KnModel eE 9 :=
  knModel_of_data (w := WE) (C := nthW J.CE) (by decide) card_KP9
    (fix_iff_of_list (fixLOK_spec P.lE (by omega)) card_E) (lst (fixLOK_spec P.lE (by omega)))
    (wordsC (by decide) P.wE) (knOK_spec P.kE (by omega))

theorem knEF : KnModel (eE * eF) 9 := by
  rw [← xw_WEF]
  exact knModel_of_data (w := WEF) (C := nthW J.CEF) (by decide) card_KP9
    (fix_iff_of_list (fixLOK_spec P.lEF (by omega)) card_EF) (lst (fixLOK_spec P.lEF (by omega)))
    (wordsC (by decide) P.wEF) (knOK_spec P.kEF (by omega))

theorem knY : KnModel eY 7 :=
  knModel_of_data (w := WY) (C := nthW J.CY) (by decide) card_KP7
    (fix_iff_of_list (fixLOK_spec P.lY (by omega)) card_Y) (lst (fixLOK_spec P.lY (by omega)))
    (wordsC (by decide) P.wY) (knOK_spec P.kY (by omega))

theorem knF : KnModel eF 9 := by
  rw [← eF_conj]
  exact knE.conj (xw_mem (by decide) (by decide))

theorem knEFk : ∀ k < 5, KnModel (eE * eF ^ k) 9 := by
  intro k hk
  interval_cases k
  · rw [pow_zero, mul_one]
    exact knE
  · rw [pow_one]
    exact knEF
  · rw [← eEFk_conj2]
    exact knEF.conj (xw_mem (by decide) (by decide))
  · rw [← eEFk_conj3]
    exact knEF.conj (xw_mem (by decide) (by decide))
  · rw [← eEFk_conj4]
    exact knEF.conj (xw_mem (by decide) (by decide))

theorem comm_EF_pow : ∀ k : ℕ, eE * eF ^ k = eF ^ k * eE
  | 0 => by rw [pow_zero, mul_one, one_mul]
  | k + 1 => by rw [pow_succ, ← mul_assoc, comm_EF_pow k, mul_assoc, eEF_comm, ← mul_assoc]

theorem mul_pow_EF (k : ℕ) : ∀ a : ℕ, (eE * eF ^ k) ^ a = eE ^ a * (eF ^ k) ^ a
  | 0 => by rw [pow_zero, pow_zero, pow_zero, mul_one]
  | a + 1 => by
    have hc : (eF ^ k) ^ a * eE = eE * (eF ^ k) ^ a := by
      rw [← pow_mul, comm_EF_pow (k * a)]
    calc (eE * eF ^ k) ^ (a + 1) = eE ^ a * (eF ^ k) ^ a * (eE * eF ^ k) := by
          rw [pow_succ, mul_pow_EF k a]
      _ = eE ^ a * ((eF ^ k) ^ a * eE) * eF ^ k := by simp only [mul_assoc]
      _ = eE ^ a * (eE * (eF ^ k) ^ a) * eF ^ k := by rw [hc]
      _ = eE ^ (a + 1) * (eF ^ k) ^ (a + 1) := by
          rw [pow_succ eE, pow_succ (eF ^ k)]
          simp only [mul_assoc]

theorem pow_mod5 {g : GL (Fin 781) (ZMod 3)} (h5 : g ^ 5 = 1) (n : ℕ) : g ^ n = g ^ (n % 5) := by
  conv_lhs => rw [← Nat.mod_add_div n 5, pow_add, pow_mul, h5, one_pow, mul_one]

theorem five_kn : ∀ a < 5, ∀ b < 5, a + b ≠ 0 → KnModel (eE ^ a * eF ^ b) 9 := by
  intro a ha b hb hab
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · rw [pow_zero, one_mul]
    exact knF.ofEq (ptFix_pow5 eF_pow5 (by omega) hb).symm
  · obtain ⟨k, hk, hka⟩ : ∃ k < 5, (k * a) % 5 = b := by
      interval_cases a <;> interval_cases b <;> first
        | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩
        | exact ⟨2, by decide, by decide⟩ | exact ⟨3, by decide, by decide⟩
        | exact ⟨4, by decide, by decide⟩
    have e : eE ^ a * eF ^ b = (eE * eF ^ k) ^ a := by
      rw [mul_pow_EF, ← pow_mul, pow_mod5 eF_pow5 (k * a), hka]
    have h5 : (eE * eF ^ k) ^ 5 = 1 := by
      rw [mul_pow_EF, eE_pow5, ← pow_mul, mul_comm, pow_mul, eF_pow5, one_pow, one_mul]
    rw [e]
    exact (knEFk k hk).ofEq (ptFix_pow5 h5 ha0 ha).symm

theorem graph_of_kn {g : GL (Fin 781) (ZMod 3)} (M : KnModel g 9) :
    (ptFix g).Nonempty ∧
      (∀ V ∈ ptFix g, ∃ W ∈ ptFix g, W ≠ V ∧ PtAdj V W) ∧
      (∀ V ∈ ptFix g, ∀ W ∈ ptFix g, V ≠ W → ¬ PtAdj V W →
        ∃ Z ∈ ptFix g, PtAdj Z V ∧ PtAdj Z W) := by
  obtain ⟨φ, hφ⟩ := M
  refine ⟨⟨_, (φ.symm ⟨(0, 1), by decide⟩).2⟩, fun V hV => ?_, fun V hV W hW hVW hn => ?_⟩
  · obtain ⟨q, hq⟩ := KP9_nbr (φ ⟨V, hV⟩)
    have hadj : PtAdj V (φ.symm q) := by
      have := (hφ ⟨V, hV⟩ (φ.symm q)).2
      rw [Equiv.apply_symm_apply] at this
      exact this hq
    exact ⟨_, (φ.symm q).2, fun h => ptAdj_irrefl V (by rwa [h] at hadj), hadj⟩
  · have hne : φ ⟨V, hV⟩ ≠ φ ⟨W, hW⟩ := fun h => hVW (congrArg Subtype.val (φ.injective h))
    have hnd : ¬ KP.Disj (φ ⟨V, hV⟩) (φ ⟨W, hW⟩) := fun h => hn ((hφ ⟨V, hV⟩ ⟨W, hW⟩).2 h)
    obtain ⟨r, hr1, hr2⟩ := KP9_common _ _ hne hnd
    refine ⟨_, (φ.symm r).2, ?_, ?_⟩
    · have := (hφ (φ.symm r) ⟨V, hV⟩).2
      rw [Equiv.apply_symm_apply] at this
      exact this hr1
    · have := (hφ (φ.symm r) ⟨W, hW⟩).2
      rw [Equiv.apply_symm_apply] at this
      exact this hr2

theorem chain_of_kn {g : GL (Fin 781) (ZMod 3)} {n : ℕ} (M : KnModel g n) (k : ℕ) (hk : k + 1 ≤ n) :
    ∃ P : Fin k → Submodule (ZMod 3) (Fin 781 → ZMod 3), (∀ i, P i ∈ ptFix g) ∧
      (∀ i j : Fin k, i.val + 1 = j.val → P i ≠ P j ∧ ¬ PtAdj (P i) (P j)) ∧
      (∀ i j : Fin k, i.val + 2 ≤ j.val → PtAdj (P i) (P j)) := by
  obtain ⟨φ, hφ⟩ := M
  have hlt : ∀ i : Fin k, i.val + 1 < n := fun i => by omega
  refine ⟨fun i => φ.symm (KP.chain i.val (hlt i)), fun i => (φ.symm _).2, fun i j hij => ?_,
    fun i j hij => ?_⟩
  · obtain ⟨h1, h2⟩ := chain_succ (hlt i) (hlt j) hij
    refine ⟨fun h => h1 (φ.symm.injective (Subtype.ext h)), fun h => h2 ?_⟩
    have := (hφ (φ.symm _) (φ.symm _)).1 h
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  · have := (hφ (φ.symm (KP.chain i.val (hlt i))) (φ.symm (KP.chain j.val (hlt j)))).2
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this (chain_far (hlt i) (hlt j) hij)

theorem sylow_five : eE ^ 5 = 1 ∧ eE ≠ 1 ∧ eF ^ 5 = 1 ∧ eE * eF = eF * eE ∧
    ∀ k < 5, eF ≠ eE ^ k :=
  ⟨eE_pow5, eE_ne, eF_pow5, eEF_comm, fun k _ => eF_ne_pow k⟩

theorem fi24_five_graph : ∃ e ∈ seedGrp, ∃ f ∈ seedGrp, e ^ 5 = 1 ∧ e ≠ 1 ∧ f ^ 5 = 1 ∧
    e * f = f * e ∧ (∀ k < 5, f ≠ e ^ k) ∧ ∀ a < 5, ∀ b < 5, a + b ≠ 0 →
      (ptFix (e ^ a * f ^ b)).Nonempty ∧
      (∀ V ∈ ptFix (e ^ a * f ^ b), ∃ W ∈ ptFix (e ^ a * f ^ b), W ≠ V ∧ PtAdj V W) ∧
      (∀ V ∈ ptFix (e ^ a * f ^ b), ∀ W ∈ ptFix (e ^ a * f ^ b), V ≠ W → ¬ PtAdj V W →
        ∃ Z ∈ ptFix (e ^ a * f ^ b), PtAdj Z V ∧ PtAdj Z W) :=
  ⟨eE, eE_mem, eF, eF_mem, eE_pow5, eE_ne, eF_pow5, eEF_comm, fun k _ => eF_ne_pow k,
    fun a ha b hb hab => graph_of_kn (five_kn a ha b hb hab)⟩

theorem fi24_five_card : ∃ e ∈ seedGrp, ∃ f ∈ seedGrp, e ^ 5 = 1 ∧ e ≠ 1 ∧ f ^ 5 = 1 ∧
    e * f = f * e ∧ (∀ k < 5, f ≠ e ^ k) ∧ ∀ a < 5, ∀ b < 5, a + b ≠ 0 →
      Nat.card (ptFix (e ^ a * f ^ b)) = 36 :=
  ⟨eE, eE_mem, eF, eF_mem, eE_pow5, eE_ne, eF_pow5, eEF_comm, fun k _ => eF_ne_pow k,
    fun a ha b hb hab => by rw [(five_kn a ha b hb hab).card, card_KP9]⟩

theorem fi24_five_chain : ∃ e ∈ seedGrp, ∃ f ∈ seedGrp, e ^ 5 = 1 ∧ e ≠ 1 ∧ f ^ 5 = 1 ∧
    e * f = f * e ∧ (∀ k < 5, f ≠ e ^ k) ∧ ∀ a < 5, ∀ b < 5, a + b ≠ 0 →
      Nat.card (ptFix (e ^ a * f ^ b)) = 36 ∧
      ∃ P : Fin 8 → Submodule (ZMod 3) (Fin 781 → ZMod 3), (∀ i, P i ∈ ptFix (e ^ a * f ^ b)) ∧
        (∀ i j : Fin 8, i.val + 1 = j.val → P i ≠ P j ∧ ¬ PtAdj (P i) (P j)) ∧
        (∀ i j : Fin 8, i.val + 2 ≤ j.val → PtAdj (P i) (P j)) :=
  ⟨eE, eE_mem, eF, eF_mem, eE_pow5, eE_ne, eF_pow5, eEF_comm, fun k _ => eF_ne_pow k,
    fun a ha b hb hab => ⟨by rw [(five_kn a ha b hb hab).card, card_KP9],
      chain_of_kn (five_kn a ha b hb hab) 8 (by norm_num)⟩⟩

theorem fi24_seven_chain : ∃ y ∈ seedGrp, ∃ e ∈ seedGrp, y ^ 7 = 1 ∧ y ≠ 1 ∧ e ^ 5 = 1 ∧
    e ≠ 1 ∧ e * y = y * e ∧
    ∃ P : Fin 6 → Submodule (ZMod 3) (Fin 781 → ZMod 3), (∀ i, P i ∈ ptFix y) ∧
      (∀ i j : Fin 6, i.val + 1 = j.val → P i ≠ P j ∧ ¬ PtAdj (P i) (P j)) ∧
      (∀ i j : Fin 6, i.val + 2 ≤ j.val → PtAdj (P i) (P j)) :=
  ⟨eY, eY_mem, eE, eE_mem, eY_pow7, eY_ne, eE_pow5, eE_ne, eEY_comm, chain_of_kn knY 6 (by norm_num)⟩

end CertificateChecks.KernelFi24F3d

end
