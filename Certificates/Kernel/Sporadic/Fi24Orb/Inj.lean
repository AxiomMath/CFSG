
module

public import Certificates.Kernel.Sporadic.Fi24Orb.Psi
public import CFSG.Certificates.Kernel.Spor.Fi24OrbTheory
import Certificates.Kernel.Sporadic.Fi24Orb.Small

public section

namespace CertificateChecks.KernelFi24Orb

open CertificateChecks.KernelFi24 CertificateChecks.KernelFi24Fix TauCeti TauCeti.Sporadic
  CFSG.Sporadic.Bridge CFSG.KC.Fi24FixC CFSG.KC.Fi24FixS CFSG.KC.Fi24FixK CFSG.KC.Fi24Orb
  CFSG.KC.Fi24OrbS CFSG.KC.Fi24OrbT CFSG.KD.Fi24Orb

abbrev N : ℕ := 306936

theorem bnd {k : ℕ} (hk : k < N) :
    BindP OL NM NI VT CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24Fix.AW 306936 k := bind_all k hk

theorem andB_true {a b : Bool} (h : CFSG.KC.Fi24Orb.andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [CFSG.KC.Fi24Orb.andB]

@[expose] noncomputable def α (k : ℕ) : ℕ := oA (OL k)

@[expose] noncomputable def β (k : ℕ) : ℕ := oB (OL k)

theorem NM_lt {k : ℕ} (hk : k < N) : NM k < N := (bnd hk).1

theorem NI_NM {k : ℕ} (hk : k < N) : NI (NM k) = k := (bnd hk).2.1

theorem α_lt {k : ℕ} (hk : k < N) : α k < N := (bnd hk).2.2.1

theorem α_α {k : ℕ} (hk : k < N) : α (α k) = k := (bnd hk).2.2.2.1

theorem β_lt {k : ℕ} (hk : k < N) : β k < N := (bnd hk).2.2.2.2.2.1

theorem β_β_β {k : ℕ} (hk : k < N) : β (β (β k)) = k := (bnd hk).2.2.2.2.2.2.1

theorem tree {k : ℕ} (hk : k < N) (h0 : k ≠ 0) : oPar (OL k) < k ∧
    ((oLab (OL k) = 1 ∧ α (oPar (OL k)) = k) ∨ (oLab (OL k) = 2 ∧ β (oPar (OL k)) = k)) :=
  ((bnd hk).2.2.2.2.2.2.2.2).resolve_left h0

theorem NM_inj {i j : ℕ} (hi : i < N) (hj : j < N) (h : NM i = NM j) : i = j := by
  rw [← NI_NM hi, ← NI_NM hj, h]

theorem NM_surj {r : ℕ} (hr : r < N) : ∃ k < N, NM k = r := by
  have hsub : (Finset.range N).image NM ⊆ Finset.range N := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (NM_lt (Finset.mem_range.1 hk))
  have hcard : ((Finset.range N).image NM).card = N := by
    rw [Finset.card_image_of_injOn (fun i hi j hj h => NM_inj (Finset.mem_range.1 hi)
      (Finset.mem_range.1 hj) h), Finset.card_range]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
  have hm : r ∈ (Finset.range N).image NM := by rw [heq]; exact Finset.mem_range.2 hr
  obtain ⟨k, hk, e⟩ := Finset.mem_image.1 hm
  exact ⟨k, Finset.mem_range.1 hk, e⟩

@[expose] noncomputable def f (k : ℕ) : Submodule (ZMod 3) (Fin 781 → ZMod 3) := ψ (NM k)

theorem f_def (k : ℕ) : f k = ψ (NM k) := rfl

theorem f_α {k : ℕ} (hk : k < N) : f (α k) = act uA (f k) := by
  rw [f_def, f_def, α, (bnd hk).2.2.2.2.1]
  exact ψ_A (NM_lt hk)

theorem f_β {k : ℕ} (hk : k < N) : f (β k) = act uB (f k) := by
  rw [f_def, f_def, β, (bnd hk).2.2.2.2.2.2.2.1]
  exact ψ_B (NM_lt hk)

theorem f_zero : f 0 = (CFSG.Sporadic.Fi24.pt 0).sp := ψ_root

theorem act_inj (g : GL (Fin 781) (ZMod 3)) {W W' : Submodule (ZMod 3) (Fin 781 → ZMod 3)}
    (h : act g W = act g W') : W = W' := by
  rw [← act_inv_act g W, h, act_inv_act]

theorem act_stab_iff {g : GL (Fin 781) (ZMod 3)} (hg : g ∈ stab V0)
    (W : Submodule (ZMod 3) (Fin 781 → ZMod 3)) : act g W = V0 ↔ W = V0 := by
  constructor
  · intro h
    apply act_inj g
    rw [h, (mem_stab.1 hg)]
  · rintro rfl
    exact mem_stab.1 hg

theorem h0_stab {k : ℕ} (hk : k < 10) (hk8 : k ≠ 8) : xs k ∈ stab V0 := by
  apply xs_stab
  omega

theorem x8_contra {r : ℕ} (hr : r < N) (h1 : ψ r = V0)
    (h2 : ψ (tk CFSG.KD.Fi24Fix.TG 8 r) = V0) : False := by
  rw [ψ_tk (by norm_num) hr, h1] at h2
  apply x8_not_stab
  have : (xs 8)⁻¹ ∈ stab V0 := h2
  simpa using (stab V0).inv_mem this

theorem fibre_zero {i : ℕ} (hi : i < N) (h : ψ i = V0) : i = 0 := by
  by_contra h0
  have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.2 h0
  have hP : ∀ k p, k < 10 → k ≠ 8 → 1 ≤ p → p < N →
      ((fun r => ψ r = V0) (tk CFSG.KD.Fi24Fix.TG k p) ↔ (fun r => ψ r = V0) p) := by
    intro k p hk hk8 _ hp
    simp only
    rw [ψ_tk (by omega) hp]
    exact act_stab_iff ((stab V0).inv_mem (h0_stab hk hk8)) _
  have hcl := forest_closed forest_all (fun r => ψ r = V0) hP hi1 hi h
  obtain ⟨he11, he12⟩ := andB_true e1
  obtain ⟨he21, he22⟩ := andB_true e2
  have he1 := And.intro (Nat.eq_of_beq_eq_true he11) (Nat.eq_of_beq_eq_true he12)
  have he2 := And.intro (Nat.eq_of_beq_eq_true he21) (Nat.eq_of_beq_eq_true he22)
  rcases ((forest_all i hi1 hi).1) with hc | ⟨hc, -⟩
  ·
    have h2 : ψ 2 = V0 := hcl 2 (by norm_num) (by norm_num) (by rw [he1.1, hc])
    exact x8_contra (by norm_num) h2 (by rw [he1.2]; exact h2)
  ·
    have h7 : ψ 718 = V0 := hcl 718 (by norm_num) (by norm_num) (by rw [he2.1, hc])
    refine x8_contra (by norm_num) h7 ?_
    have hlt : tk CFSG.KD.Fi24Fix.TG 8 718 < N := tk_lt (by norm_num) (by norm_num)
    rcases Nat.eq_zero_or_pos (tk CFSG.KD.Fi24Fix.TG 8 718) with h0' | hpos
    · rw [h0', ψ_zero]
    · exact hcl _ hpos hlt (by rw [he2.2, hc])

@[expose] noncomputable def wP : List Bool → ℕ → ℕ
  | [] => fun i => i
  | b :: w => fun i => wP w (if b then β i else α i)

@[expose] noncomputable def uW : List Bool → GL (Fin 781) (ZMod 3)
  | [] => 1
  | b :: w => uW w * (if b then uB else uA)

theorem wP_lt : ∀ (w : List Bool) {i : ℕ}, i < N → wP w i < N
  | [], _, hi => hi
  | b :: w, i, hi => by
    cases b
    · exact wP_lt w (α_lt hi)
    · exact wP_lt w (β_lt hi)

theorem f_wP : ∀ (w : List Bool) {i : ℕ}, i < N → f (wP w i) = act (uW w) (f i)
  | [], i, _ => by simp [wP, uW, act_one]
  | b :: w, i, hi => by
    cases b
    · change f (wP w (α i)) = act (uW w * uA) (f i)
      rw [f_wP w (α_lt hi), act_mul, f_α hi]
    · change f (wP w (β i)) = act (uW w * uB) (f i)
      rw [f_wP w (β_lt hi), act_mul, f_β hi]

theorem wP_inj : ∀ (w : List Bool) {i j : ℕ}, i < N → j < N → wP w i = wP w j → i = j
  | [], _, _, _, _, h => h
  | b :: w, i, j, hi, hj, h => by
    cases b
    · have := wP_inj w (α_lt hi) (α_lt hj) h
      rw [← α_α hi, ← α_α hj, this]
    · have := wP_inj w (β_lt hi) (β_lt hj) h
      rw [← β_β_β hi, ← β_β_β hj, this]

@[expose] def invW : List Bool → List Bool
  | [] => []
  | b :: w => invW w ++ (if b then [true, true] else [false])

theorem wP_append (u v : List Bool) (i : ℕ) : wP (u ++ v) i = wP v (wP u i) := by
  induction u generalizing i with
  | nil => rfl
  | cons b u ih => exact ih _

theorem wP_invW : ∀ (w : List Bool) {i : ℕ}, i < N → wP (invW w) (wP w i) = i
  | [], _, _ => rfl
  | b :: w, i, hi => by
    rw [invW, wP_append]
    cases b
    · change wP [false] (wP (invW w) (wP w (α i))) = i
      rw [wP_invW w (α_lt hi)]
      exact α_α hi
    · change wP [true, true] (wP (invW w) (wP w (β i))) = i
      rw [wP_invW w (β_lt hi)]
      exact β_β_β hi

theorem reach_zero : ∀ k, k < N → ∃ w, wP w k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨[], rfl⟩
    · obtain ⟨hp, hl⟩ := tree hk (Nat.pos_iff_ne_zero.1 hpos)
      set p := oPar (OL k)
      have hpN : p < N := by omega
      obtain ⟨w, hw⟩ := ih p hp hpN
      rcases hl with ⟨-, he⟩ | ⟨-, he⟩
      · refine ⟨false :: w, ?_⟩
        change wP w (α k) = 0
        rw [← he, α_α hpN, hw]
      · refine ⟨true :: true :: w, ?_⟩
        change wP w (β (β k)) = 0
        rw [← he, β_β_β hpN, hw]

noncomputable def m0 : ℕ := NI 0

theorem m0_spec : m0 < N ∧ NM m0 = 0 := by
  obtain ⟨k, hk, e⟩ := NM_surj (r := 0) (by norm_num)
  have : m0 = k := by rw [m0, ← e, NI_NM hk]
  rw [this]
  exact ⟨hk, e⟩

theorem reach_m0 {k : ℕ} (hk : k < N) : ∃ w, wP w k = m0 := by
  obtain ⟨w1, h1⟩ := reach_zero k hk
  obtain ⟨w2, h2⟩ := reach_zero m0 m0_spec.1
  refine ⟨w1 ++ invW w2, ?_⟩
  rw [wP_append, h1, ← h2, wP_invW w2 m0_spec.1]

theorem f_inj {i j : ℕ} (hi : i < N) (hj : j < N) (h : f i = f j) : i = j := by
  obtain ⟨w, hw⟩ := reach_m0 hj
  have h1 : f (wP w i) = f (wP w j) := by rw [f_wP w hi, f_wP w hj, h]
  rw [hw, f_def, f_def, m0_spec.2, ψ_zero] at h1
  have h2 := fibre_zero (NM_lt (wP_lt w hi)) h1
  have h3 : wP w i = m0 := NM_inj (wP_lt w hi) m0_spec.1 (by rw [h2, m0_spec.2])
  exact wP_inj w hi hj (by rw [h3, hw])

theorem ψ_inj {r r' : ℕ} (hr : r < N) (hr' : r' < N) (h : ψ r = ψ r') : r = r' := by
  obtain ⟨k, hk, rfl⟩ := NM_surj hr
  obtain ⟨k', hk', rfl⟩ := NM_surj hr'
  rw [f_inj hk hk' h]

theorem mem_range_ψ (W : Submodule (ZMod 3) (Fin 781 → ZMod 3)) :
    (∃ r < N, ψ r = W) ↔ ∃ g ∈ Γ, act g V0 = W := by
  constructor
  · rintro ⟨r, -, rfl⟩
    obtain ⟨g, hg, e⟩ := F_mem (Rr r)
    exact ⟨g, hg, by rw [ψ_def, e]⟩
  · rintro ⟨g, ⟨u, rfl⟩, rfl⟩
    set e : E := fi24PrimeGroupMulEquivCommutator u
    obtain ⟨i, hi, hr⟩ := Rr_cov ((e⁻¹ : E) : Fi24AutomorphismGroup)
    refine ⟨i, hi, ?_⟩
    rw [ψ_def, ← F_rel hr]
    have := F_mul 1 e⁻¹
    rw [one_mul] at this
    rw [this, F_one, map_inv, inv_inv, σE_iso]

end CertificateChecks.KernelFi24Orb

end
