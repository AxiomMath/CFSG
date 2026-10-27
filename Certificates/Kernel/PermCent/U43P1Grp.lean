module

public import Certificates.Kernel.PermCent.U43P1Elt
public import Certificates.Kernel.PermCent.U43P1Bind
public import CFSG.Certificates.Kernel.P1Model.Conj
public import Certificates.Kernel.PermCent.U43P1Tab

public section

namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43
  CFSG.ComponentClassification.HarrisLit.P1 CFSG.LieType.Multipliers.U43 CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.ConjOrb CFSG.KC.LeftOrb CFSG.KC.BfsPin Subgroup

theorem baseL_lt : ∀ p ∈ baseL, p < 820 := by decide

theorem baseL4_lt : ∀ p ∈ baseL4, p < 820 := by decide

theorem baseT_lt : ∀ p ∈ baseT, p < 820 := by decide

theorem card_range_psi' : Nat.card psi.range = 3265920 := by
  rw [range_psi, card_closure_psi]

theorem class_facts {ng N r : ℕ} {G GI T E D S : ℕ → ℕ}
    {t : Equiv.Perm (Fin 820)} (hng : ng = 2) (hh : headK 820 10 ng G GI = true)
    (h0 : tabOK tabA (G 0) = true) (h1 : tabOK tabB (G 1) = true)
    (hcl : ∀ i < N, closPt 820 10 ng N G GI T E i = true)
    (htr : ∀ i < N, treePt ng N r E D i = true) (hr : r < N) (ht : PRep 820 10 (T r) t)
    (hK : distinctK N (fun i => pkeyK 820 10 baseL (T i)) S = true) :
    N * Nat.card ↥(psi.range ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 820)))) = 3265920 ∧
      (∀ i < N, ∃ h ∈ psi.range, PRep 820 10 (T i) (h * t * h⁻¹)) ∧
      ∀ h ∈ psi.range, ∃ i < N, PRep 820 10 (T i) (h * t * h⁻¹) := by
  subst hng
  obtain ⟨c, hc, hreach, hcl', hinj⟩ := conjOrb_reps (g := fun k => psi (genX k)) (t := t)
    (by norm_num) hh (prep_psi_gen h0 h1) hcl htr hr ht baseL_lt hK
  have hroot : ∃ i < N, c i = t := ⟨r, hr, prep_eq (hc r hr) ht⟩
  have hcard := card_inf_centralizer_of_reps (fun k => psi (genX k)) t c hreach hcl' hroot hinj
  have hall := exists_eq_conj_of_reps (fun k => psi (genX k)) t c hcl' hroot
  rw [closure_gen, card_range_psi'] at hcard
  rw [closure_gen] at hall
  refine ⟨hcard, fun i hi => ?_, fun h hm => ?_⟩
  · obtain ⟨h, hm, e⟩ := hreach i hi
    rw [closure_gen] at hm
    exact ⟨h, hm, e ▸ hc i hi⟩
  · obtain ⟨i, hi, e⟩ := hall h hm
    exact ⟨i, hi, e ▸ hc i hi⟩

theorem group_facts {n w : ℕ} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {ng N : ℕ}
    {G T E D S : ℕ → ℕ} {ps : List ℕ} {g : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ k < ng, PRep n w (G k) (g k)) (hcl : ∀ i < N, closPtL n w ng N G T E i = true)
    (htr : ∀ i < N, treePt ng N 0 E D i = true) (hN : 0 < N) (h0 : T 0 = pidn n w)
    (hps : ∀ p ∈ ps, p < n) (hK : distinctK N (fun i => pkeyK n w ps (T i)) S = true) :
    Nat.card (closure (g '' {k | k < ng})) = N ∧
      (∀ y ∈ closure (g '' {k | k < ng}), ∃ i < N, PRep n w (T i) y) ∧
      ∀ i < N, ∃ y ∈ closure (g '' {k | k < ng}), PRep n w (T i) y := by
  have h0' : PRep n w (T 0) 1 := by
    rw [h0]
    exact prep_pidn hn hw
  obtain ⟨c, hc0, hc, hmem, hcl', hinj⟩ := leftOrb_reps (by omega) hg hcl htr hN h0' hps hK
  obtain ⟨hcard, hall⟩ := group_of_reps (MonoidHom.id _) Function.injective_id g c
    ⟨0, hN, hc0⟩ hmem hcl' hinj
  refine ⟨hcard, fun y hy => ?_, fun i hi => ⟨c i, hmem i hi, hc i hi⟩⟩
  obtain ⟨i, hi, e⟩ := hall y hy
  have e' : c i = y := e
  exact ⟨i, hi, e' ▸ hc i hi⟩

@[expose] def repOf (c : ℕ) : ℕ × Bool :=
  cond (Nat.beq c 0) repIn (cond (Nat.beq c 1) repM1a (cond (Nat.beq c 2) repM1b
    (cond (Nat.beq c 3) repFa (cond (Nat.beq c 4) repFb repIa))))

@[expose] noncomputable def tRep (c : ℕ) : Equiv.Perm (Fin 820) := eK (repOf c).1 (repOf c).2

theorem detOf_rep : ∀ c < 6, detOf (repOf c).1 ≠ 0 := by decide

theorem prep_root (c : ℕ) (hc : c < 6) (h : matOK (repOf c).1 (repOf c).2 (clsT c (clsR c)) = true) :
    PRep 820 10 (clsT c (clsR c)) (tRep c) :=
  prep_matOK (detOf_spec (detOf_rep c hc)).1 h

theorem cls_facts :
    ∀ c < 6, clsN c * Nat.card ↥(psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820)))) =
        3265920 ∧
      (∀ j < clsN c, ∃ h ∈ psi.range, PRep 820 10 (clsT c j) (h * tRep c * h⁻¹)) ∧
      ∀ h ∈ psi.range, ∃ j < clsN c, PRep 820 10 (clsT c j) (h * tRep c * h⁻¹) := by
  obtain ⟨hb, nIn, nM1a, nM1b, nFa, nFb, nIa, gIn, gM1a, gM1b, gFa, gFb, gIa, rIn, rM1a, rM1b,
    rFa, rFb, rIa⟩ := bindsC
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨aIn, bIn⟩, tIn⟩, aM1a⟩, bM1a⟩, tM1a⟩, aM1b⟩, bM1b⟩, tM1b⟩, aFa⟩, bFa⟩,
    tFa⟩, aFb⟩, bFb⟩, tFb⟩, aIa⟩, bIa⟩, tIa⟩ := hb
  intro c hc
  interval_cases c
  · exact class_facts (N := CIn.N) (r := CIn.r0) gIn CIn.h aIn bIn (fun i hi => CIn.cl i (lt_of_lt_of_le hi (by decide)))
      (fun i hi => CIn.tr0 i (lt_of_lt_of_le hi (by decide))) (by omega)
      (prep_root 0 (by norm_num) tIn) CIn.k
  · exact class_facts (N := CM1a.N) (r := CM1a.r0) gM1a CM1a.h aM1a bM1a (fun i hi => CM1a.cl i (lt_of_lt_of_le hi (by decide)))
      (fun i hi => CM1a.tr0 i (lt_of_lt_of_le hi (by decide))) (by omega)
      (prep_root 1 (by norm_num) tM1a) CM1a.k
  · exact class_facts (N := CM1b.N) (r := CM1b.r0) gM1b CM1b.h aM1b bM1b (fun i hi => CM1b.cl i (lt_of_lt_of_le hi (by decide)))
      (fun i hi => CM1b.tr0 i (lt_of_lt_of_le hi (by decide))) (by omega)
      (prep_root 2 (by norm_num) tM1b) CM1b.k
  · exact class_facts (N := CFa.N) (r := CFa.r0) gFa CFa.h aFa bFa (fun i hi => CFa.cl i (lt_of_lt_of_le hi (by decide)))
      (fun i hi => CFa.tr0 i (lt_of_lt_of_le hi (by decide))) (by omega)
      (prep_root 3 (by norm_num) tFa) CFa.k
  · exact class_facts (N := CFb.N) (r := CFb.r0) gFb CFb.h aFb bFb (fun i hi => CFb.cl i (lt_of_lt_of_le hi (by decide)))
      (fun i hi => CFb.tr0 i (lt_of_lt_of_le hi (by decide))) (by omega)
      (prep_root 4 (by norm_num) tFb) CFb.k
  · exact class_facts (N := CIa.N) (r := CIa.r0) gIa CIa.h aIa bIa (fun i hi => CIa.cl i (lt_of_lt_of_le hi (by decide)))
      (fun i hi => CIa.tr0 i (lt_of_lt_of_le hi (by decide))) (by omega)
      (prep_root 5 (by norm_num) tIa) CIa.k

theorem isId_of_prep {p : ℕ} (hp : PRep 820 10 p 1) : isId p = true := by
  rw [isId, List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  have e : pg 10 (mask 10) p i = ((1 : Equiv.Perm (Fin 820)) ⟨i, hi'⟩ : ℕ) := hp ⟨i, hi'⟩
  rw [at10, e]
  exact Nat.beq_refl i

theorem eq_one_of_isId {p : ℕ} {σ : Equiv.Perm (Fin 820)} (hp : PRep 820 10 p σ)
    (h : isId p = true) : σ = 1 := by
  refine Equiv.ext fun x => Fin.ext ?_
  rw [isId, List.all_eq_true] at h
  rw [← hp x]
  exact Nat.eq_of_beq_eq_true (h x (List.mem_range.2 x.2))

theorem prep_pc {p q : ℕ} {σ τ : Equiv.Perm (Fin 820)} (hp : PRep 820 10 p σ)
    (hq : PRep 820 10 q τ) : PRep 820 10 (pc p q) (σ * τ) :=
  prep_pcomp (by norm_num) hp hq

theorem invol_iff {p : ℕ} {σ : Equiv.Perm (Fin 820)} (hp : PRep 820 10 p σ) :
    invol p = true ↔ σ * σ = 1 ∧ σ ≠ 1 := by
  rw [invol, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨eq_one_of_isId (prep_pc hp hp) h1, fun e => ?_⟩
    rw [e] at hp
    rw [isId_of_prep hp] at h2
    exact Bool.noConfusion h2
  · rintro ⟨h1, h2⟩
    refine ⟨isId_of_prep (h1 ▸ prep_pc hp hp), ?_⟩
    cases e : isId p
    · rfl
    · exact absurd (eq_one_of_isId hp e) h2

theorem inCls_spec {cls : ℕ → ℕ → ℕ} {sz : ℕ → ℕ} {cs : List ℕ} {c j x : ℕ}
    (h : inCls cls sz cs c j x = true) : c ∈ cs ∧ j < sz c ∧ cls c j = x := by
  rw [inCls, Bool.and_eq_true, Bool.and_eq_true, List.contains_iff_mem, Nat.blt_eq] at h
  exact ⟨h.1.1, h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem coverOK_spec {S : ℕ → ℕ} {cls : ℕ → ℕ → ℕ} {sz : ℕ → ℕ} {cs : List ℕ} {W : List ℕ}
    (h : coverOK S cls sz cs W = true) :
    ∀ i < W.length, invol (S i) = true → ∃ c ∈ cs, ∃ j < sz c, cls c j = S i := by
  intro i hi hv
  rw [coverOK, List.all_eq_true] at h
  have hm : (W[i], i) ∈ W.zipIdx := List.mk_mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hi)
  have h1 := h _ hm
  dsimp only at h1
  cases e : Nat.beq W[i] 0
  · rw [e, cond_false] at h1
    obtain ⟨hc, hj, hx⟩ := inCls_spec h1
    exact ⟨_, hc, _, hj, hx⟩
  · rw [e, cond_true, hv] at h1
    exact Bool.noConfusion h1

end CertificateChecks.KernelPermCent.U43P1

end
