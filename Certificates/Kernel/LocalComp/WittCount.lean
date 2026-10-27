module

public import Certificates.Kernel.LocalComp.WittLev
public import Certificates.Kernel.Sporadic.M22Syl.Facts
public import CFSG.Certificates.Kernel.WittCntSound
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count

public section

namespace CertificateChecks.KernelLC.Witt

open Equiv CFSG.KC.WCnt CFSG.KS CFSG.KS.PCnt CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Th CFSG.Certificates CFSG.ComponentClassification.WittDesign
  CertificateChecks.KernelSpor.M22Syl

theorem lv_eq : ∃ T0 T1 T2 T3 T4, lv = [T0, T1, T2, T3, T4] ∧ T0.map (pkw 5) = L0 ∧
    T1.map (pkw 5) = L1 ∧ T2.map (pkw 5) = L2 ∧ T3.map (pkw 5) = L3 ∧ T4.map (pkw 5) = L4 := by
  have h := lv_pk
  rcases hl : lv with _ | ⟨T0, _ | ⟨T1, _ | ⟨T2, _ | ⟨T3, _ | ⟨T4, _ | ⟨T5, rest⟩⟩⟩⟩⟩⟩ <;>
    rw [hl] at h <;> simp at h
  exact ⟨T0, T1, T2, T3, T4, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem fix_levels : ((L1 ++ L2 ++ L3 ++ L4).all fun t => Nat.beq (pt t 0) 0) = true ∧
    ((L2 ++ L3 ++ L4).all fun t => Nat.beq (pt t 1) 1) = true ∧
    ((L3 ++ L4).all fun t => Nat.beq (pt t 2) 2) = true := by
  decide +kernel

private theorem fix_of_packed {T : List (Perm (Fin 22))} {L : List Nat} (hT : T.map (pkw 5) = L)
    {i : Fin 22} (h : (L.all fun t => Nat.beq (pt t i.val) i.val) = true) :
    ∀ t ∈ T, t i = i := by
  intro t ht
  have hm : pkw 5 t ∈ L := hT ▸ List.mem_map_of_mem ht
  have h1 := Nat.eq_of_beq_eq_true (List.all_eq_true.1 h _ hm)
  rw [pt_pkw] at h1
  exact Fin.ext h1

private theorem mul_fix {Ts : List (List (Perm (Fin 22)))} {b : Fin 22}
    (h : ∀ T ∈ Ts, ∀ t ∈ T, t b = b) (u : Perm (Fin 22)) {g : Perm (Fin 22)}
    (hg : g ∈ products Ts) : (u * g) b = u b := by
  rw [Perm.mul_apply, products_fix h g hg]

theorem m22Count_eq_ccnt (Q : (Fin 22 → Fin 22) → Prop)
    [DecidablePred Q] (d : Perm (Fin 22)) (hd : d ∈ M22) (F : Nat → Nat)
    (hFd : ∀ σ : Perm (Fin 22), F (pkw 5 σ) = if Q ⇑(σ * d) then 1 else 0)
    (C0 : Nat → Bool) (C1 : Nat → Nat → Bool) (C2 : Nat → Nat → Nat → Bool)
    (hcov : ∀ σ : Perm (Fin 22), Q ⇑(σ * d) →
      C0 (σ 0).val = true ∧ C1 (σ 0).val (σ 1).val = true ∧
        C2 (σ 0).val (σ 1).val (σ 2).val = true) :
    m22Count Q = ccnt 22 5 31 F (lev C0 C1 C2) I 0 := by
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  have e1 : m22Count Q = Nat.card {x : M22 // Q ⇑((x : Perm (Fin 22)) * d)} := by
    rw [← card_m22_subtype]
    exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulRight (⟨d, hd⟩ : M22)⁻¹)
      (fun x => by simp))
  have e2 := card_subtype_eq_countP m22Certificate.originalSubgroup (enumeration m22Certificate)
    (enumeration_nodup _ hQ) (mem_enumeration_iff _ hQ) (fun g => Q ⇑(g * d))
  rw [m22Certificate_originalSubgroup] at e2
  refine e1.trans (e2.trans ?_)
  rw [← sum_ite_eq_countP]
  obtain ⟨T0, T1, T2, T3, T4, hlv, h0, h1, h2, h3, h4⟩ := lv_eq
  have hE : enumeration m22Certificate = products [T0, T1, T2, T3, T4] := by
    rw [← hlv]
    rfl
  obtain ⟨f0, f1, f2⟩ := fix_levels
  have hf0 : ∀ T ∈ [T1, T2, T3, T4], ∀ t ∈ T, t 0 = 0 := by
    intro T hT
    rw [List.all_append, List.all_append, List.all_append] at f0
    simp only [Bool.and_eq_true] at f0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl | rfl
    exacts [fix_of_packed h1 f0.1.1.1, fix_of_packed h2 f0.1.1.2, fix_of_packed h3 f0.1.2,
      fix_of_packed h4 f0.2]
  have hf1 : ∀ T ∈ [T2, T3, T4], ∀ t ∈ T, t 1 = 1 := by
    intro T hT
    rw [List.all_append, List.all_append] at f1
    simp only [Bool.and_eq_true] at f1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl
    exacts [fix_of_packed h2 f1.1.1, fix_of_packed h3 f1.1.2, fix_of_packed h4 f1.2]
  have hf2 : ∀ T ∈ [T3, T4], ∀ t ∈ T, t 2 = 2 := by
    intro T hT
    rw [List.all_append] at f2
    simp only [Bool.and_eq_true] at f2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    exacts [fix_of_packed h3 f2.1, fix_of_packed h4 f2.2]
  have hF : ∀ σ : Perm (Fin 22), F (pkw 5 σ) ≠ 0 →
      C0 (σ 0).val = true ∧ C1 (σ 0).val (σ 1).val = true ∧
        C2 (σ 0).val (σ 1).val (σ 2).val = true := by
    intro σ hσ
    rw [hFd] at hσ
    by_cases hq : Q ⇑(σ * d)
    · exact hcov σ hq
    · rw [if_neg hq] at hσ
      exact absurd rfl hσ
  have hPr : Pruned 5 F [(fun x => C0 (pt x 0), T0), (fun x => C1 (pt x 0) (pt x 1), T1),
      (fun x => C2 (pt x 0) (pt x 1) (pt x 2), T2), (fun _ => true, T3), (fun _ => true, T4)] 1 := by
    intro t0 _
    refine ⟨fun hc h hh => ?_, fun t1 _ => ⟨fun hc h hh => ?_, fun t2 _ => ⟨fun hc h hh => ?_,
      fun t3 _ => ⟨fun hc => by simp at hc, fun t4 _ => ⟨fun hc => by simp at hc, trivial⟩⟩⟩⟩⟩
    · by_contra hne
      have hc0 := (hF _ hne).1
      have e0 : pt (pkw 5 (1 * t0)) 0 = (1 * t0 * h) 0 := by
        rw [mul_fix hf0 _ hh]
        exact pt_pkw _ 0
      change C0 (pt (pkw 5 (1 * t0)) 0) = false at hc
      rw [e0, hc0] at hc
      exact absurd hc (by decide)
    · by_contra hne
      have hc1 := (hF _ hne).2.1
      have e0 : pt (pkw 5 (1 * t0 * t1)) 0 = (1 * t0 * t1 * h) 0 := by
        rw [mul_fix (fun T hT => hf0 T (List.mem_cons_of_mem _ hT)) _ hh]
        exact pt_pkw _ 0
      have e1' : pt (pkw 5 (1 * t0 * t1)) 1 = (1 * t0 * t1 * h) 1 := by
        rw [mul_fix hf1 _ hh]
        exact pt_pkw _ 1
      change C1 (pt (pkw 5 (1 * t0 * t1)) 0) (pt (pkw 5 (1 * t0 * t1)) 1) = false at hc
      rw [e0, e1', hc1] at hc
      exact absurd hc (by decide)
    · by_contra hne
      have hc2 := (hF _ hne).2.2
      have hsub0 : ∀ T ∈ [T3, T4], ∀ t ∈ T, t 0 = 0 := fun T hT =>
        hf0 T (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hT))
      have hsub1 : ∀ T ∈ [T3, T4], ∀ t ∈ T, t 1 = 1 := fun T hT =>
        hf1 T (List.mem_cons_of_mem _ hT)
      have e0 : pt (pkw 5 (1 * t0 * t1 * t2)) 0 = (1 * t0 * t1 * t2 * h) 0 := by
        rw [mul_fix hsub0 _ hh]
        exact pt_pkw _ 0
      have e1' : pt (pkw 5 (1 * t0 * t1 * t2)) 1 = (1 * t0 * t1 * t2 * h) 1 := by
        rw [mul_fix hsub1 _ hh]
        exact pt_pkw _ 1
      have e2' : pt (pkw 5 (1 * t0 * t1 * t2)) 2 = (1 * t0 * t1 * t2 * h) 2 := by
        rw [mul_fix hf2 _ hh]
        exact pt_pkw _ 2
      change C2 (pt (pkw 5 (1 * t0 * t1 * t2)) 0) (pt (pkw 5 (1 * t0 * t1 * t2)) 1)
        (pt (pkw 5 (1 * t0 * t1 * t2)) 2) = false at hc
      rw [e0, e1', e2', hc2] at hc
      exact absurd hc (by decide)
  have hc := ccnt_pkw (n := 22) (w := 5) (by norm_num) (by norm_num) F _ 1 0 hPr
  simp only [List.map_cons, List.map_nil, h0, h1, h2, h3, h4, KernelSpor.M22Syl.pk_one,
    mask_five, one_mul, Nat.zero_add] at hc
  rw [lev, hc, hE]
  refine congrArg List.sum (List.map_congr_left fun g _ => ?_)
  rw [hFd]

theorem m22Count_eq_wc (Q : (Fin 22 → Fin 22) → Prop)
    [DecidablePred Q] (d : Perm (Fin 22)) (hd : d ∈ M22) (D : Nat) (hD : pkw 5 d = D)
    (C0 : Nat → Bool) (C1 : Nat → Nat → Bool) (C2 : Nat → Nat → Nat → Bool)
    (hcov : ∀ σ : Perm (Fin 22), Q ⇑(σ * d) →
      C0 (σ 0).val = true ∧ C1 (σ 0).val (σ 1).val = true ∧
        C2 (σ 0).val (σ 1).val (σ 2).val = true) :
    m22Count Q = wc Q D C0 C1 C2 :=
  m22Count_eq_ccnt Q d hd (ind Q D) (fun σ => by rw [← hD, ind_pkw]) C0 C1 C2 hcov

theorem m22Count_eq_wcB (Q : (Fin 22 → Fin 22) → Prop)
    [DecidablePred Q] (b : Nat → Bool) (hb : ∀ τ : Perm (Fin 22), b (pkw 5 τ) = decide (Q ⇑τ))
    (d : Perm (Fin 22)) (hd : d ∈ M22) (D : Nat) (hD : pkw 5 d = D)
    (C0 : Nat → Bool) (C1 : Nat → Nat → Bool) (C2 : Nat → Nat → Nat → Bool)
    (hcov : ∀ σ : Perm (Fin 22), Q ⇑(σ * d) →
      C0 (σ 0).val = true ∧ C1 (σ 0).val (σ 1).val = true ∧
        C2 (σ 0).val (σ 1).val (σ 2).val = true) :
    m22Count Q = wcB b D C0 C1 C2 :=
  m22Count_eq_ccnt Q d hd (indB b D) (fun σ => by rw [← hD, indB_pkw b Q hb]) C0 C1 C2 hcov

end CertificateChecks.KernelLC.Witt

end
