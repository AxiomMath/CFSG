module

public import Certificates.Kernel.Misc.Perm.GH23TagK
public import Certificates.Kernel.Misc.Perm.GH23Facts
public import CFSG.Certificates.Kernel.Misc.PermGH23TagSound
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Tags
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Top
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23GL32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Solv

public section

namespace CertificateChecks.KernelMisc.GH23Tag

open Equiv CFSG.KC.Misc.Clos CFSG.KC.Misc.GH23 CFSG.OddStandard.SmallF3.HarrisU33.GH23Data
  CFSG.OddStandard.SmallF3.HarrisU33.Outside CertificateChecks.KernelMisc.GH23

theorem xn_pos : ∀ x < 49, 0 < XN x := by decide +kernel

theorem nn41 : NN 41 = 168 := by decide +kernel

theorem members_length : members.length = 41 := by decide +kernel

theorem ref_lo {r : ℕ} (h : r < 42) :
    gE r = eM r ∧ gN r = NN r ∧ refGens r = (List.range (NG r)).map (gM r) := by
  have hb : Nat.blt r 42 = true := Nat.blt_eq.mpr h
  refine ⟨funext fun k => ?_, ?_, ?_⟩
  · unfold gE
    rw [hb]
  · unfold gN
    rw [hb]
  · unfold refGens gNG gG
    rw [hb]

theorem ref_hi (x : ℕ) :
    gE (42 + x) = eX x ∧ gN (42 + x) = XN x ∧
      refGens (42 + x) = (List.range (XNG x)).map (gX x) := by
  have hb : Nat.blt (42 + x) 42 = false :=
    Bool.eq_false_iff.mpr fun h => by
      rw [Nat.blt_eq] at h
      omega
  have hs : Nat.sub (42 + x) 42 = x := Nat.add_sub_cancel_left 42 x
  refine ⟨funext fun k => ?_, ?_, ?_⟩
  · unfold gE
    rw [hb, hs]
  · unfold gN
    rw [hb, hs]
  · unfold refGens gNG gG
    rw [hb, hs]

theorem ref_valid {r : ℕ} (hr : r < 91) : (refGens r).all validC = true := by
  rcases Nat.lt_or_ge r 42 with h | h
  · rw [(ref_lo h).2.2]
    rcases Nat.lt_or_ge r 41 with h' | h'
    · rw [← gens_ok r h']
      exact members_valid r h'
    · obtain rfl : r = 41 := by omega
      rw [q2_gens_ok]
      exact q2_valid
  · obtain ⟨x, rfl⟩ : ∃ x, r = 42 + x := ⟨r - 42, by omega⟩
    exact xvalid x (by omega)

theorem ref_exact {r : ℕ} (hr : r < 91) :
    Nat.card (gh23Sub (refGens r)) = gN r ∧
      ExactList gh23Code (gh23Sub (refGens r)) (gN r) (gE r) := by
  rcases Nat.lt_or_ge r 42 with h | h
  · obtain ⟨h1, h2, h3⟩ := ref_lo h
    rw [h1, h2]
    exact group_exact r h h3 (ref_valid hr)
  · obtain ⟨x, rfl⟩ : ∃ x, r = 42 + x := ⟨r - 42, by omega⟩
    have hx : x < 49 := by omega
    obtain ⟨h1, h2, h3⟩ := ref_hi x
    rw [h1, h2]
    have hb := XK.all x hx
    unfold xB at hb
    obtain ⟨ht, hb⟩ := CFSG.KC.Misc.Clos.andB_eq_true hb
    obtain ⟨hs, hc⟩ := CFSG.KC.Misc.Clos.andB_eq_true hb
    exact gh23_clos h3 (ref_valid hr) (xn_pos x hx) (all_of_allR ht) (all_of_allR hs)
      (all_of_allR hc)

theorem memR_sound {r c t : ℕ} (hr : r < 91) (h : memR r c t = true) :
    ∃ σ ∈ gh23Sub (refGens r), gh23Code σ = c :=
  memAt_sound (ref_exact hr).2 h

theorem refGens_member {m : ℕ} (hm : m < 41) :
    refGens m = (members.getD m ⟨[], .top⟩).gens :=
  (ref_lo (by omega)).2.2.trans (gens_ok m hm).symm

theorem mem_member_gens {m c : ℕ} (hm : m < 41) (hc : c ∈ (members.getD m ⟨[], .top⟩).gens) :
    ∃ j < NG m, gM m j = c := by
  rw [gens_ok m hm, List.mem_map] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  exact ⟨j, List.mem_range.mp hj, rfl⟩

theorem forall_mem_of_getD {l : List ℕ} {p : ℕ → Prop} (h : ∀ i < l.length, p (l.getD i 0)) :
    ∀ c ∈ l, p c := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hp := h i hi
  rwa [List.getD_eq_getElem _ _ hi] at hp

theorem job_le {j : ℕ} (hj : j < 27) (hA : jA j < 91) (hB : jB j < 91) :
    ⁅gh23Sub (refGens (jA j)), gh23Sub (refGens (jA j))⁆ ≤ gh23Sub (refGens (jB j)) :=
  comm_le_of_commAt (ref_exact hA).2 (ref_exact hB).2 (all_of_allR (JK.all j hj))

theorem iso_facts {m sz : ℕ} {imgs : List ℕ} (hm : m < 41) (h : isoW (wM m) m imgs sz = true) :
    (∀ c ∈ imgs, ∃ σ ∈ gh23Sub (members.getD m ⟨[], .top⟩).gens, gh23Code σ = c) ∧
      (∀ c ∈ (members.getD m ⟨[], .top⟩).gens, ∃ σ ∈ gh23Sub imgs, gh23Code σ = c) ∧
      Nat.card (gh23Sub imgs) = sz := by
  unfold isoW at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range,
    and_assoc] at h
  obtain ⟨hx, hg, hsz, hmem, hgen⟩ := h
  rw [cnt_ok.1] at hx
  have hx' : XB m < 91 := by omega
  refine ⟨forall_mem_of_getD fun i hi => ?_, fun c hc => ?_, ?_⟩
  · rw [← refGens_member hm]
    exact memR_sound (by omega) (hmem i hi)
  · obtain ⟨j, hj, rfl⟩ := mem_member_gens hm hc
    rw [← hg]
    exact memR_sound hx' (hgen j hj)
  · rw [← hg, (ref_exact hx').1, hsz]

theorem z3a5_of {m : ℕ} (hm : m < 41) {imgs : List ℕ} {z : ℕ}
    (ht : (members.getD m ⟨[], .top⟩).tag = .z3a5 imgs z) :
    Nonempty (↥(gh23Sub (members.getD m ⟨[], .top⟩).gens) ≃*
      Multiplicative (ZMod 3) × alternatingGroup (Fin 5)) := by
  have h := TW.all m hm
  unfold tagW at h
  rw [ht] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, and_assoc] at h
  obtain ⟨hlen, hcarm, hz3, hcomm, hiso⟩ := h
  obtain ⟨himgs, hPg, hcard⟩ := iso_facts hm hiso
  exact gh23_z3a5_exact himgs hPg hcard hlen hcarm hz3 hcomm

theorem member_spec (m : ℕ) (hm : m < 41) :
    GH23Spec (gh23Sub (members.getD m ⟨[], .top⟩).gens) := by
  have h := TW.all m hm
  unfold tagW at h
  unfold GH23Spec
  cases ht : (members.getD m ⟨[], .top⟩).tag with
  | solv chain =>
    rw [ht] at h
    refine Or.inl ?_
    simp only [solvW, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
      List.mem_range, and_assoc] at h
    obtain ⟨hlast, hk⟩ := h
    rw [cnt_ok.1, cnt_ok.2] at hk
    have hn0 : chain.length ≠ 0 := by
      intro h0
      rw [List.length_eq_zero_iff] at h0
      rw [h0] at hlast
      simp at hlast
    let rA : ℕ → ℕ := fun k => if k = 0 then m else XB m + k - 1
    have hrA : ∀ k < chain.length, rA k < 91 := by
      intro k hk'
      by_cases h0 : k = 0
      · simp only [rA, if_pos h0]
        omega
      · simp only [rA, if_neg h0]
        have hb := (hk (k - 1) (by omega)).1
        omega
    have hstep : ∀ k < chain.length,
        ⁅gh23Sub (refGens (rA k)), gh23Sub (refGens (rA k))⁆ ≤ gh23Sub (refGens (rA (k + 1))) := by
      intro k hk'
      obtain ⟨hb, -, hj, hja, hjb⟩ := hk k hk'
      have hA : jA (JM m + k) = rA k := hja
      have hB : jB (JM m + k) = rA (k + 1) := by
        rw [hjb]
        change XB m + k = if k + 1 = 0 then m else XB m + (k + 1) - 1
        rw [if_neg (Nat.add_one_ne_zero k)]
        omega
      have hle := job_le hj (by rw [hA]; exact hrA k hk') (by rw [hjb]; omega)
      rwa [hA, hB] at hle
    have hlastD : refGens (rA chain.length) = [] := by
      have h1 := (hk (chain.length - 1) (by omega)).2.1
      have h2 : rA chain.length = XB m + (chain.length - 1) := by
        simp only [rA, if_neg hn0]
        omega
      rw [h2, h1, List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, hlast]
      rfl
    have hbot : gh23Sub (refGens (rA chain.length)) = ⊥ := by
      rw [hlastD]
      exact gh23Sub_nil
    have hs : IsSolvable ↥(gh23Sub (refGens (rA 0))) :=
      gh23_isSolvable_of_chain (fun k => gh23Sub (refGens (rA k))) chain.length hstep hbot
    have h0 : gh23Sub (refGens (rA 0)) = gh23Sub (members.getD m ⟨[], .top⟩).gens := by
      change gh23Sub (refGens m) = _
      rw [refGens_member hm]
    rw [h0] at hs
    exact hs
  | two ngens =>
    rw [ht] at h
    refine Or.inr (Or.inl ?_)
    simp only [twoW, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
      List.mem_range, List.any_eq_true, bne_iff_ne, ne_eq, and_assoc] at h
    obtain ⟨hx, hg, hne, hmem, hsq, hconj⟩ := h
    rw [cnt_ok.1] at hx
    have hx' : XB m < 91 := by omega
    have hN := (ref_exact hx').2
    rw [hg] at hN
    refine gh23_two_exact hN ?_ ?_ ?_ ?_
    · refine forall_mem_of_getD fun i hi => ?_
      rw [← refGens_member hm]
      exact memR_sound (by omega) (hmem i hi)
    · obtain ⟨c, hc, hc1⟩ := hne
      exact ⟨c, hc, fun h1 => hc1 (h1.trans one8_eq.symm)⟩
    · intro k hk
      have hk' := hsq k hk
      rwa [mul8_eq, one8_eq] at hk'
    · intro σ hσ ν hν
      obtain ⟨j, hj, hσj⟩ := mem_member_gens hm hσ
      obtain ⟨i, hi, hνi⟩ := List.getElem_of_mem hν
      have hνi' : ngens.getD i 0 = gh23Code ν := by rw [List.getD_eq_getElem _ _ hi, hνi]
      obtain ⟨ha, hea, hb, heb⟩ := hconj j hj i hi
      obtain ⟨τ, hτ, hτc⟩ := hN.1 _ ha
      obtain ⟨τ', hτ', hτc'⟩ := hN.1 _ hb
      rw [hσj, hνi', ← hτc, mul8_eq, mul8_eq, gh23_mulC_code, gh23_mulC_code] at hea
      rw [hσj, hνi', ← hτc', mul8_eq, mul8_eq, gh23_mulC_code, gh23_mulC_code] at heb
      have e1 := gh23_code_injective hea
      have e2 := gh23_code_injective heb
      constructor
      · rw [e1, mul_inv_cancel_right]
        exact hτ
      · rw [mul_assoc, e2, inv_mul_cancel_left]
        exact hτ'
  | alt n imgs =>
    rw [ht] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
    obtain ⟨hn, hlen, hcarm, hiso⟩ := h
    obtain ⟨himgs, hPg, hcard⟩ := iso_facts hm hiso
    obtain ⟨e⟩ := gh23_alt_exact himgs hPg hcard (by omega) hlen hcarm
    refine Or.inr (Or.inr ?_)
    rcases hn with (rfl | rfl) | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))
    · exact Or.inr (Or.inl ⟨e⟩)
  | sym n imgs =>
    rw [ht] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
    obtain ⟨hn, hlen, hcox, hiso⟩ := h
    obtain ⟨himgs, hPg, hcard⟩ := iso_facts hm hiso
    obtain ⟨e⟩ := gh23_sym_exact himgs hPg hcard hlen hcox
    refine Or.inr (Or.inr ?_)
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))))
    · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  | z3a5 imgs z =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (z3a5_of hm ht))))))))))
  | idx2 j =>
    rw [ht] at h
    simp only [idx2W, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
      List.mem_range, and_assoc] at h
    obtain ⟨hj, hNN, hz, hmem⟩ := h
    cases htj : (members.getD j ⟨[], .top⟩).tag with
    | z3a5 imgs z =>
      have hle : ∀ c ∈ (members.getD j ⟨[], .top⟩).gens,
          ∃ σ ∈ gh23Sub (members.getD m ⟨[], .top⟩).gens, gh23Code σ = c := by
        intro c hc
        obtain ⟨i, hi, rfl⟩ := mem_member_gens hj hc
        rw [← refGens_member hm]
        exact memR_sound (by omega) (hmem i hi)
      have hcard : Nat.card (gh23Sub (members.getD m ⟨[], .top⟩).gens) =
          2 * Nat.card (gh23Sub (members.getD j ⟨[], .top⟩).gens) := by
        rw [(member_exact m hm).1, (member_exact j hj).1, hNN]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (gh23_idx2_exact hle hcard (z3a5_of hj htj)))))))))))
    | _ =>
      rw [htj] at hz
      exact (Bool.false_ne_true hz).elim
  | gl imgs =>
    rw [ht] at h
    simp only [glW, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
      List.mem_range, and_assoc] at h
    obtain ⟨hNN, h1P, h1Q, hk⟩ := h
    have hcl := closed_ok m (by omega)
    have hCT : ∀ k < NN m, ∀ j < NG m,
        cM m (k * NG m + j) < NN m ∧ eM m (cM m (k * NG m + j)) = mulC (eM m k) (gM m j) := by
      intro k hk' j hj
      have hc := hcl k hk'
      unfold closedAt at hc
      rw [CFSG.KC.Misc.Clos.allN_iff] at hc
      have hc' := hc j hj
      rw [CFSG.KC.Misc.Clos.letB_eq] at hc'
      obtain ⟨h1, h2⟩ := CFSG.KC.Misc.Clos.andB_eq_true hc'
      exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩
    obtain ⟨e1⟩ := gh23_gl_exact (φ := wM m) (ψ := fun t => wM m (NN m + t)) (gens_ok m hm)
      (member_exact m hm).2 q2_exact.2 (member_exact m hm).1 q2_exact.1 hNN hCT
      (h1P.trans one8_eq) (h1Q.trans one8_eq) (fun k hk' => (hk k hk').1)
      (fun k hk' => (hk k hk').2.1) (fun k hk' j hj => (hk k hk').2.2 j hj)
    obtain ⟨e2⟩ := gh23_q2_equiv_GL32 (q2_exact.1.trans nn41)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e1.trans e2⟩))))))
  | top =>
    rw [ht] at h
    simp only [beq_iff_eq] at h
    rw [h, gh23_sub_topGens]
    exact Or.inr (Or.inr (Or.inl ⟨MulEquiv.refl _⟩))

theorem members_spec : ∀ m ∈ members, GH23Spec (gh23Sub m.gens) := by
  intro m hm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  have hs := member_spec i (by rw [members_length] at hi; exact hi)
  rwa [List.getD_eq_getElem _ _ hi] at hs

end CertificateChecks.KernelMisc.GH23Tag

end
