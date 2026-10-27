module

public import Certificates.Kernel.Sporadic.Fi24P7.Mat
public import CFSG.Certificates.Kernel.Spor.Fi24G2dSound
public import CFSG.Certificates.Kernel.Spor.Fi24P7Sound

public section

namespace CertificateChecks.KernelFi24P7

open CertificateChecks.KernelFi24 CertificateChecks.KernelCo2 CertificateChecks.KernelFi24Fix
  CertificateChecks.KernelFi24Orb CertificateChecks.KernelFi24G2e CertificateChecks.KernelFi24Ext
  CertificateChecks.KernelFi24F3d CFSG.KC.Fi24FixC CFSG.KC.Fi24FixS CFSG.KC.Fi24FixK CFSG.KC.Loop
  CFSG.KC.Fi24G2eS CFSG.KC.Fi24G2dS CFSG.KC.Fi24Kn CFSG.KC.Fi24KnS CFSG.KC.Fi24P7S CFSG.Sporadic.Fi24
  CFSG.KD.Fi24P7

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local irreducible] CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24P7.TB

theorem act_xw_fix_iff {w : List ℕ} (hw : ∀ g ∈ w, g < 12) {r : ℕ} (hr : r < N) :
    act (xw w) (ψ r) = ψ r ↔ walk CFSG.KD.Fi24Fix.TG w r = r := by
  rw [← act_inv_eq_iff, act_xw_inv hw hr]
  exact ⟨ψ_inj (walk_lt hw hr) hr, fun h => by rw [h]⟩

theorem card_ptFix_xw {w : List ℕ} (hw : ∀ g ∈ w, g < 12) :
    Nat.card (ptFix (xw w)) =
      ((Finset.range 306936).filter fun r => walk CFSG.KD.Fi24Fix.TG w r = r).card := by
  classical
  have e : ptFix (xw w) = ↑(((Finset.range 306936).filter fun r =>
      walk CFSG.KD.Fi24Fix.TG w r = r).image ψ) := by
    ext V
    rw [mem_ptFix, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨hp, hV⟩
      obtain ⟨r, hr, rfl⟩ := (isPt_iff V).1 hp
      exact ⟨r, Finset.mem_filter.2 ⟨Finset.mem_range.2 hr, (act_xw_fix_iff hw hr).1 hV⟩, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨hr1, hr2⟩ := Finset.mem_filter.1 hr
      have hrN : r < N := Finset.mem_range.1 hr1
      exact ⟨(isPt_iff _).2 ⟨r, hrN, rfl⟩, (act_xw_fix_iff hw hrN).2 hr2⟩
  rw [e, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn]
  intro r hr r' hr' h
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hr hr'
  exact ψ_inj hr.1 hr'.1 h

theorem card_fix_okS {w K : List ℕ} (h : ∀ c < 75, okS w K c = true) :
    ((Finset.range 306936).filter fun r => walk CFSG.KD.Fi24Fix.TG w r = r).card =
      ∑ c ∈ Finset.range 75, K.getD c 0 := by
  refine card_fix_of_chunks _ w K (fun c hc => ?_) ?_
  · have h1 := h c (by omega)
    unfold okS at h1
    have hb : Nat.blt c 74 = true := by simpa using hc
    rw [hb, nthN_eq] at h1
    exact h1
  · have h1 := h 74 (by norm_num)
    unfold okS at h1
    have hb : Nat.blt 74 74 = false := rfl
    rw [hb, nthN_eq] at h1
    exact h1

theorem card_fix_nil :
    ((Finset.range 306936).filter fun r => walk CFSG.KD.Fi24Fix.TG [] r = r).card = 306936 := by
  have e : ((Finset.range 306936).filter fun r => walk CFSG.KD.Fi24Fix.TG [] r = r) =
      Finset.range 306936 := Finset.filter_true_of_mem fun r _ => rfl
  rw [e, Finset.card_range]

theorem xw_ne_one {w : List ℕ} (hw : ∀ g ∈ w, g < 12)
    (h : ((Finset.range 306936).filter fun r => walk CFSG.KD.Fi24Fix.TG w r = r).card ≠ 306936) :
    xw w ≠ 1 := by
  intro h1
  apply h
  have e1 := card_ptFix_xw hw
  have e0 := card_ptFix_xw (w := []) (by simp)
  have hx : xw ([] : List ℕ) = 1 := by simp [xw, wq]
  rw [h1, ← hx, e0, card_fix_nil] at e1
  exact e1.symm

@[instance_reducible] noncomputable def actM : MulAction (GL (Fin 781) (ZMod 3)) (Submodule (ZMod 3) (Fin 781 → ZMod 3)) where
  smul := act
  one_smul := act_one
  mul_smul := act_mul

@[instance_reducible] noncomputable def actM2 : MulAction (GL (Fin 781) (ZMod 3))
    (Submodule (ZMod 3) (Fin 781 → ZMod 3) × Submodule (ZMod 3) (Fin 781 → ZMod 3)) where
  smul g p := (act g p.1, act g p.2)
  one_smul p := by
    change (act 1 p.1, act 1 p.2) = p
    rw [act_one, act_one]
  mul_smul g h p := by
    change (act (g * h) p.1, act (g * h) p.2) = (act g (act h p.1), act g (act h p.2))
    rw [act_mul, act_mul]

theorem chunk_spec {f : ℕ → Bool} {m k : ℕ} (h : ∀ c < k, chunk f m c = true) (hm : m ≤ 1024 * k) :
    ∀ j < m, f j = true := by
  intro j hj
  have h0 := h (j / 1024) (by omega)
  unfold chunk at h0
  have h1 := allBelow_spec h0 (by norm_num) (j % 1024) (Nat.mod_lt _ (by norm_num))
  rw [letB_eqE] at h1
  have e : Nat.add (Nat.mul 1024 (j / 1024)) (j % 1024) = j := Nat.div_add_mod j 1024
  rw [e] at h1
  have hb : Nat.blt j m = true := by simpa using hj
  rw [hb] at h1
  exact h1

theorem dvd_of_pt {u v : List ℕ} (hu : ∀ g ∈ u, g < 12) (hv : ∀ g ∈ v, g < 12) {m : ℕ}
    {F PA PB PAR DEP : ℕ → ℕ} (hm : 0 < m)
    (hF : ∀ j < m, F j < N ∧ (j + 1 < m → F j < F (j + 1)))
    (hA : ∀ j < m, PA j < m ∧ walk CFSG.KD.Fi24Fix.TG u (F j) = F (PA j))
    (hB : ∀ j < m, PB j < m ∧ walk CFSG.KD.Fi24Fix.TG v (F j) = F (PB j))
    (ht : ∀ j < m, j = 0 ∨ (PAR j < m ∧ DEP (PAR j) < DEP j ∧ (PA (PAR j) = j ∨ PB (PAR j) = j))) :
    m ∣ Nat.card (Subgroup.closure ({xw u, xw v} : Set (GL (Fin 781) (ZMod 3)))) := by
  have hinj := inj_of_inc (fun j hj hj1 => (hF j hj).2 hj1)
  refine @dvd_card_closure_of_tree _ _ _ actM _ (xw u) (xw v) m (fun j => ψ (F j))
    (fun i hi j hj h => hinj i hi j hj (ψ_inj (hF i hi).1 (hF j hj).1 h)) PA PB PAR DEP
    (fun j hj => ⟨(hA j hj).1, ?_⟩) (fun j hj => ⟨(hB j hj).1, ?_⟩) 0 hm ht
  · change act (xw u)⁻¹ (ψ (F j)) = ψ (F (PA j))
    rw [act_xw_inv hu (hF j hj).1, (hA j hj).2]
  · change act (xw v)⁻¹ (ψ (F j)) = ψ (F (PB j))
    rw [act_xw_inv hv (hF j hj).1, (hB j hj).2]

theorem dvd_of_pairs {u v : List ℕ} (hu : ∀ g ∈ u, g < 12) (hv : ∀ g ∈ v, g < 12) {m1 M : ℕ}
    {F PA PB Q QA QB QP QD : ℕ → ℕ} (hM : 0 < M)
    (hF : ∀ j < m1, F j < N ∧ (j + 1 < m1 → F j < F (j + 1)))
    (hA : ∀ j < m1, PA j < m1 ∧ walk CFSG.KD.Fi24Fix.TG u (F j) = F (PA j))
    (hB : ∀ j < m1, PB j < m1 ∧ walk CFSG.KD.Fi24Fix.TG v (F j) = F (PB j))
    (hQ : ∀ k < M, Q k < m1 * m1 ∧ (k + 1 < M → Q k < Q (k + 1)))
    (hQA : ∀ k < M, QA k < M ∧ Q (QA k) = m1 * PA (Q k / m1) + PA (Q k % m1))
    (hQB : ∀ k < M, QB k < M ∧ Q (QB k) = m1 * PB (Q k / m1) + PB (Q k % m1))
    (ht : ∀ k < M, k = 0 ∨ (QP k < M ∧ QD (QP k) < QD k ∧ (QA (QP k) = k ∨ QB (QP k) = k))) :
    M ∣ Nat.card (Subgroup.closure ({xw u, xw v} : Set (GL (Fin 781) (ZMod 3)))) := by
  have hm1 : 0 < m1 := by
    rcases Nat.eq_zero_or_pos m1 with h | h
    · have := (hQ 0 hM).1
      rw [h] at this
      omega
    · exact h
  have hinjF := inj_of_inc (fun j hj hj1 => (hF j hj).2 hj1)
  have hinjQ := inj_of_inc (fun k hk hk1 => (hQ k hk).2 hk1)
  have hdiv : ∀ k < M, Q k / m1 < m1 := fun k hk =>
    (Nat.div_lt_iff_lt_mul hm1).2 (hQ k hk).1
  have hmod : ∀ k, Q k % m1 < m1 := fun k => Nat.mod_lt _ hm1
  have dec : ∀ {x y : ℕ}, x < m1 → y < m1 → (m1 * x + y) / m1 = x ∧ (m1 * x + y) % m1 = y := by
    intro x y hx hy
    constructor
    · rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hm1, Nat.div_eq_of_lt hy, zero_add]
    · rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  let e : ℕ → Submodule (ZMod 3) (Fin 781 → ZMod 3) × Submodule (ZMod 3) (Fin 781 → ZMod 3) :=
    fun k => (ψ (F (Q k / m1)), ψ (F (Q k % m1)))
  have he : ∀ i < M, ∀ j < M, e i = e j → i = j := by
    intro i hi j hj h
    have h1 := ψ_inj (hF _ (hdiv i hi)).1 (hF _ (hdiv j hj)).1 (congrArg Prod.fst h)
    have h2 := ψ_inj (hF _ (hmod i)).1 (hF _ (hmod j)).1 (congrArg Prod.snd h)
    have e1 := hinjF _ (hdiv i hi) _ (hdiv j hj) h1
    have e2 := hinjF _ (hmod i) _ (hmod j) h2
    apply hinjQ i hi j hj
    rw [← Nat.div_add_mod (Q i) m1, ← Nat.div_add_mod (Q j) m1, e1, e2]
  have step : ∀ {w : List ℕ} (_ : ∀ g ∈ w, g < 12) {P R : ℕ → ℕ}
      (_ : ∀ j < m1, P j < m1 ∧ walk CFSG.KD.Fi24Fix.TG w (F j) = F (P j))
      (_ : ∀ k < M, R k < M ∧ Q (R k) = m1 * P (Q k / m1) + P (Q k % m1)),
      ∀ k < M, R k < M ∧ @HSMul.hSMul _ _ _ (@instHSMul _ _ actM2.toSMul) (xw w)⁻¹ (e k) = e (R k) := by
    intro w hw P R hP hR k hk
    refine ⟨(hR k hk).1, ?_⟩
    have hd := dec (hP _ (hdiv k hk)).1 (hP _ (hmod k)).1
    change (act (xw w)⁻¹ (ψ (F (Q k / m1))), act (xw w)⁻¹ (ψ (F (Q k % m1)))) =
      (ψ (F (Q (R k) / m1)), ψ (F (Q (R k) % m1)))
    rw [act_xw_inv hw (hF _ (hdiv k hk)).1, act_xw_inv hw (hF _ (hmod k)).1, (hP _ (hdiv k hk)).2,
      (hP _ (hmod k)).2, (hR k hk).2, hd.1, hd.2]
  exact @dvd_card_closure_of_tree _ _ _ actM2 _ (xw u) (xw v) M e he QA QB QP QD
    (step hu hA hQA) (step hv hB hQB) 0 hM ht

theorem and4 {a b c d : Bool} (h : CFSG.KC.andB a (CFSG.KC.andB b (CFSG.KC.andB c d)) = true) :
    a = true ∧ b = true ∧ c = true ∧ d = true := by
  simp only [andB_eqE, Bool.and_eq_true] at h
  exact h

theorem and3 {a b c : Bool} (h : CFSG.KC.andB a (CFSG.KC.andB b c) = true) :
    a = true ∧ b = true ∧ c = true := by
  simp only [andB_eqE, Bool.and_eq_true] at h
  exact h

end CertificateChecks.KernelFi24P7

end
