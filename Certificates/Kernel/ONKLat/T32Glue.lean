module

public import Certificates.Kernel.ONKLat.Code
public import Certificates.Kernel.ONKLat.Checks
public import Certificates.Kernel.ONKLat.T32Checks
public import Certificates.Kernel.Sporadic.OddCore.ON2129F
public import CFSG.Sporadic.Schreier.ONSylowCenter
public import CFSG.Certificates.Kernel.Enum.ZCSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONKL

open Equiv CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.ONSchreier
  CFSG.ONSchreier.Native CFSG.KC.Misc.ClosW CFSG.ComponentClassification.PSL3Four
  CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK CertificateChecks.KernelSpor
  CertificateChecks.KernelSpor.ON2129

noncomputable abbrev sT (j : ℕ) : Perm (Fin 32) := permOfArr 32 Data.T32Chain.generators[j]!

theorem nIf_ite (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem allN_false {n : ℕ} {f : ℕ → Bool} (h : allN n f = false) : ∃ t < n, f t = false := by
  by_contra hc
  have ht : allN n f = true := PK.allN_iff.2 fun t ht => by
    cases e : f t
    · exact absurd ⟨t, ht, e⟩ hc
    · rfl
  rw [ht] at h
  exact Bool.noConfusion h

theorem allN_bAnd_false {n : ℕ} {f g : ℕ → Bool}
    (h : allN n (fun t => Bool.rec (motive := fun _ => Bool) false (g t) (f t)) = false) :
    ∃ t < n, f t = false ∨ g t = false := by
  obtain ⟨t, ht, hf⟩ := allN_false h
  refine ⟨t, ht, ?_⟩
  have hf' : Bool.rec (motive := fun _ => Bool) false (g t) (f t) = false := hf
  cases e : f t
  · exact Or.inl rfl
  · rw [e] at hf'
    exact Or.inr hf'

theorem beq_false_of_ne {a b : Perm (Fin 32)} (h : a ≠ b) :
    Nat.beq (wcode 6 a) (wcode 6 b) = false := by
  cases e : Nat.beq (wcode 6 a) (wcode 6 b)
  · rfl
  · exact absurd ((beq_code henc32).1 e) h

theorem m6c (a b : Perm (Fin 32)) : m6 (wcode 6 a) (wcode 6 b) = wcode 6 (a * b) :=
  (henc32.enc_mul a b).symm

theorem i32c : i32 = wcode 6 (1 : Perm (Fin 32)) := henc32.enc_one.symm

theorem cm6c {a b : Perm (Fin 32)} : cm6 (wcode 6 a) (wcode 6 b) = true ↔ a * b = b * a := by
  unfold cm6
  rw [m6c, m6c, beq_code henc32]

theorem code_s {j : ℕ} (hj : j < 6) :
    wcode 6 (sT j) = T32E.G j := by
  have hk : T32E.k = 6 := rfl
  obtain ⟨e, hc⟩ := (gensOK_of t32_gens).2 j (by rw [hk]; exact hj)
  have hp := prep_t32_gens j (by rw [t32_gens_size]; exact hj)
  have hp' : PRep 32 (unpack 32 6 (T32E.G j)) (sT j) := fun x => by
    rw [← e]
    exact hp x
  exact wcode_of_prep (by norm_num) (shr_of_canon hc) hp'

theorem code_si {j : ℕ} (hj : j < 6) :
    wcode 6 (sT j)⁻¹ = gI j := by
  rw [← wcode_inv (by norm_num), code_s hj]
  rfl

theorem bind_parts : dP.length = 7 ∧
    (∀ i < 7, bindArrK onKD[i]! 32 6 (List.getD dP i 0) = true ∧
      permOK 32 6 (mask 6) (32 * 6) (List.getD dP i 0) (List.getD dP i 0) = true) ∧
    bindArrK onKE 32 6 eP = true ∧ bindArrK Data.T32z 32 6 zP = true ∧
    bindArrK onKY5 120 7 y5 = true ∧ bindArrK onKY7 120 7 y7 = true := by
  have h := ch812105_bind
  unfold bindOK at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun i hi => ?_, h3, h4, h5, h6⟩
  have h7 := allN_spec h2 i hi
  simp only [bAnd_iff] at h7
  exact h7

theorem zP_shr : zP >>> (32 * 6) = 0 := by decide +kernel

theorem code_z : wcode 6 onz32 = zP := by
  have hp := prep_z32
  rw [unpack_eq_of_bindArrK bind_parts.2.2.2.1] at hp
  exact wcode_of_prep (by norm_num) zP_shr hp

theorem code_d {i : ℕ} (hi : i < 7) : wcode 6 (onKPerm 32 onKD[i]!) = List.getD dP i 0 := by
  obtain ⟨hb, hp⟩ := bind_parts.2.1 i hi
  obtain ⟨h0, -, hf⟩ := CFSG.KC.EnumSound.permOK_sound hp
  rw [unpack_eq_of_bindArrK hb]
  exact wcode_of_prep (by norm_num) h0 (prep_onKPerm_inv hf)

theorem code_T
    {g : Perm (Fin 32)} (hg : g ∈ onT32Chain.originalSubgroup) :
    ∃ k < 512, wcode 6 g = T32E.T k := by
  obtain ⟨k, hk, hr⟩ := t32_enumerates.exists_pos hg
  rw [t32_cert.2.2.2.2.1] at hk
  have hc : k < T32E.cnt := hk
  rw [t32Enum_eq, rec_get hc] at hr
  exact ⟨k, hk, wcode_of_tab (by norm_num) (shr_of_canon (penumPt_canon (t32_pt hc))) hr⟩

theorem elt_T {k : ℕ}
    (hk : k < 512) : ∃ g ∈ onT32Chain.originalSubgroup, wcode 6 g = T32E.T k := by
  have hs : k < t32Enum.tabs.size := by rw [t32_cert.2.2.2.2.1]; exact hk
  obtain ⟨g, hg, hr⟩ := t32_enumerates.exists_elt hs
  have hc : k < T32E.cnt := hk
  rw [t32Enum_eq, rec_get hc] at hr
  exact ⟨g, hg, wcode_of_tab (by norm_num) (shr_of_canon (penumPt_canon (t32_pt hc))) hr⟩

theorem conjI_c {j : ℕ} (hj : j < 6) (t : Perm (Fin 32)) :
    conjI j (wcode 6 t) = wcode 6 (sT j * t * (sT j)⁻¹) := by
  unfold conjI
  rw [← code_s hj, ← code_si hj, m6c, m6c]

noncomputable def wP (t : ℕ) : Perm (Fin 32) :=
  if t < 36 then sT (t / 6) * sT (t % 6) * (sT (t / 6))⁻¹ * (sT (t % 6))⁻¹ else sT (t - 36) ^ 4

theorem wI_c {t : ℕ} (ht : t < 42) : wI t = wcode 6 (wP t) := by
  unfold wI wP
  rw [nIf_ite]
  by_cases h : t < 36
  · have hb : Nat.blt t 36 = true := Nat.blt_eq.mpr h
    rw [if_pos hb, if_pos h, ← code_s (j := t / 6) (by omega), ← code_s (j := t % 6) (by omega),
      ← code_si (j := t / 6) (by omega), ← code_si (j := t % 6) (by omega), m6c, m6c, m6c]
  · have e4 : sT (t - 36) ^ 4 = sT (t - 36) * (sT (t - 36) * (sT (t - 36) * (sT (t - 36) * 1))) := by
      rw [pow_succ', pow_succ', pow_succ', pow_succ', pow_zero]
    have hb : ¬ Nat.blt t 36 = true := fun e => h (Nat.blt_eq.mp e)
    rw [if_neg hb, if_neg h, e4, i32c, ← code_s (j := t - 36) (by omega), m6c, m6c, m6c, m6c]

theorem wP_cases {t : ℕ} (ht : t < 42) :
    (∃ a < 6, ∃ b < 6, wP t = sT a * sT b * (sT a)⁻¹ * (sT b)⁻¹) ∨ ∃ a < 6, wP t = sT a ^ 4 := by
  by_cases h : t < 36
  · exact Or.inl ⟨t / 6, by omega, t % 6, Nat.mod_lt _ (by norm_num), by rw [wP, if_pos h]⟩
  · exact Or.inr ⟨t - 36, by omega, by rw [wP, if_neg h]⟩

theorem inD_spec {t : ℕ} : ∀ {D : List ℕ}, inD D t = true → ∃ i < D.length, t = D.getD i 0
  | [], h => (Bool.false_ne_true h).elim
  | d :: D, h => by
    change Bool.rec (motive := fun _ => Bool) (inD D t) true (Nat.beq t d) = true at h
    cases hb : Nat.beq t d
    · rw [hb] at h
      obtain ⟨i, hi, he⟩ := inD_spec (h : inD D t = true)
      exact ⟨i + 1, by simp only [List.length_cons]; omega, by simpa using he⟩
    · exact ⟨0, by simp, by simpa using Nat.eq_of_beq_eq_true hb⟩

theorem tI_parts : allN 512 (invI dP) = true ∧
    allN 7 (fun a => allN 7 fun b => witI zP (List.getD dP a 0) (List.getD dP b 0)) = true := by
  have h := ch812105_tI
  unfold tIOK at h
  simp only [bAnd_iff] at h
  exact h

theorem t_parts : allN 512 (eK eP zP) = true ∧ Nat.beq (T32E.T (List.getD ePos 0 0)) eP = true ∧
    Nat.beq (m6 eP eP) i32 = true ∧
    Bool.rec (motive := fun _ => Bool) true false (Nat.beq eP i32) = true ∧
    Bool.rec (motive := fun _ => Bool) true false (Nat.beq eP zP) = true := by
  have h := ch812105_t
  unfold tOK at h
  simp only [bAnd_iff] at h
  obtain ⟨-, -, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h3, h4, h5, h6, h7⟩

theorem ePos_lt : List.getD ePos 0 0 < 512 := by decide +kernel

theorem inv_cases :
    ∀ g : Perm (Fin 32), g ∈ onT32Chain.originalSubgroup → g * g = 1 → g ≠ 1 →
      (∀ j < 6, g * (permOfArr 32 Data.T32Chain.generators[j]! * g *
          (permOfArr 32 Data.T32Chain.generators[j]!)⁻¹) =
        permOfArr 32 Data.T32Chain.generators[j]! * g *
          (permOfArr 32 Data.T32Chain.generators[j]!)⁻¹ * g) →
      ∃ i < 7, g = onKPerm 32 onKD[i]! := by
  intro g hg h2 h1 hc
  obtain ⟨k, hk, hgk⟩ := code_T hg
  have hp : invI dP k = true := allN_spec tI_parts.1 k hk
  unfold invI at hp
  rw [strictB_app', ← hgk] at hp
  have e1 : Nat.beq (m6 (wcode 6 g) (wcode 6 g)) i32 = true := by
    rw [m6c, i32c, beq_code henc32]
    exact h2
  have e2 : Nat.beq (wcode 6 g) i32 = false := by
    rw [i32c]
    exact beq_false_of_ne h1
  have e3 : allN 6 (fun j => cm6 (wcode 6 g) (conjI j (wcode 6 g))) = true :=
    PK.allN_iff.2 fun j hj => by
      rw [conjI_c hj, cm6c]
      exact hc j hj
  rw [e1, e2, e3] at hp
  obtain ⟨i, hi, he⟩ := inD_spec (hp : inD dP (wcode 6 g) = true)
  rw [bind_parts.1] at hi
  exact ⟨i, hi, henc32.inj (he.trans (code_d hi).symm)⟩

theorem witI_spec {z a b : ℕ} (h : witI z a b = true) (h0 : cm6 a b = true)
    (h1 : Nat.beq a z = false) (h2 : Nat.beq b z = false) (h3 : Nat.beq b a = false)
    (h4 : Nat.beq b (m6 a z) = false) :
    allN 42 (fun t => Bool.rec (motive := fun _ => Bool) false (cm6 (wI t) b) (cm6 (wI t) a)) =
      false := by
  unfold witI at h
  rw [h0, h1, h2, h3, h4] at h
  revert h
  cases allN 42 (fun t => Bool.rec (motive := fun _ => Bool) false (cm6 (wI t) b) (cm6 (wI t) a))
  · intro _
    rfl
  · intro h
    exact (Bool.false_ne_true h).elim

theorem allN_wit_false {a b : ℕ}
    (h : allN 42 (fun t => Bool.rec (motive := fun _ => Bool) false (cm6 (wI t) b)
      (cm6 (wI t) a)) = false) :
    ∃ t < 42, cm6 (wI t) a = false ∨ cm6 (wI t) b = false :=
  allN_bAnd_false h

theorem wit_gen {a b z : Perm (Fin 32)}
    (hp : witI (wcode 6 z) (wcode 6 a) (wcode 6 b) = true) (hc : a * b = b * a) (hiz : a ≠ z)
    (hjz : b ≠ z) (hji : b ≠ a) (hjiz : b ≠ a * z) :
    ∃ t < 42, ¬ (wP t * a = a * wP t ∧ wP t * b = b * wP t) := by
  have h4 : Nat.beq (wcode 6 b) (m6 (wcode 6 a) (wcode 6 z)) = false := by
    rw [m6c]
    exact beq_false_of_ne hjiz
  have hall := witI_spec hp (cm6c.2 hc) (beq_false_of_ne hiz) (beq_false_of_ne hjz)
    (beq_false_of_ne hji) h4
  obtain ⟨t, ht, hf⟩ := allN_wit_false hall
  refine ⟨t, ht, fun ⟨h1, h2⟩ => ?_⟩
  rcases hf with hf | hf
  · rw [wI_c ht, cm6c.2 h1] at hf
    exact Bool.noConfusion hf
  · rw [wI_c ht, cm6c.2 h2] at hf
    exact Bool.noConfusion hf

theorem witness :
    ∀ i j : ℕ, i < 7 → j < 7 →
      onKPerm 32 onKD[i]! * onKPerm 32 onKD[j]! = onKPerm 32 onKD[j]! * onKPerm 32 onKD[i]! →
      onKPerm 32 onKD[i]! ≠ onz32 → onKPerm 32 onKD[j]! ≠ onz32 →
      onKPerm 32 onKD[j]! ≠ onKPerm 32 onKD[i]! →
      onKPerm 32 onKD[j]! ≠ onKPerm 32 onKD[i]! * onz32 →
      ∃ w : Perm (Fin 32),
        ((∃ a < 6, ∃ b < 6, w = permOfArr 32 Data.T32Chain.generators[a]! *
            permOfArr 32 Data.T32Chain.generators[b]! *
            (permOfArr 32 Data.T32Chain.generators[a]!)⁻¹ *
            (permOfArr 32 Data.T32Chain.generators[b]!)⁻¹) ∨
          ∃ a < 6, w = permOfArr 32 Data.T32Chain.generators[a]! ^ 4) ∧
        ¬ (w * onKPerm 32 onKD[i]! = onKPerm 32 onKD[i]! * w ∧
          w * onKPerm 32 onKD[j]! = onKPerm 32 onKD[j]! * w) := by
  intro i j hi hj hc hiz hjz hji hjiz
  have hp : witI zP (List.getD dP i 0) (List.getD dP j 0) = true :=
    allN_spec (allN_spec tI_parts.2 i hi) j hj
  rw [← code_d hi, ← code_d hj, ← code_z] at hp
  obtain ⟨t, ht, hf⟩ := wit_gen hp hc hiz hjz hji hjiz
  exact ⟨wP t, wP_cases ht, hf⟩

theorem e_exists :
    ∃ e ∈ onT32Chain.originalSubgroup, e * e = 1 ∧ e ≠ 1 ∧ e ≠ onz32 ∧
      ∀ t ∈ onT32Chain.originalSubgroup, t * e = e * t ∨ t * e = e * onz32 * t := by
  obtain ⟨h3, h4, h5, h6, h7⟩ := t_parts
  obtain ⟨e, heT, he⟩ := elt_T ePos_lt
  rw [Nat.eq_of_beq_eq_true h4] at he
  refine ⟨e, heT, ?_, fun h => ?_, fun h => ?_, fun t ht => ?_⟩
  · rw [← he, m6c, i32c, beq_code henc32] at h5
    exact h5
  · rw [← he, i32c, h, Nat.beq_refl] at h6
    exact Bool.false_ne_true h6
  · rw [← he, ← code_z, h, Nat.beq_refl] at h7
    exact Bool.false_ne_true h7
  · obtain ⟨k, hk, htk⟩ := code_T ht
    have hc : eK eP zP k = true := allN_spec h3 k hk
    unfold eK at hc
    rw [strictB_app', ← htk, ← he, ← code_z] at hc
    cases hb : cm6 (wcode 6 t) (wcode 6 e)
    · rw [hb] at hc
      have hc' : Nat.beq (m6 (wcode 6 t) (wcode 6 e))
          (m6 (m6 (wcode 6 e) (wcode 6 onz32)) (wcode 6 t)) = true := hc
      rw [m6c, m6c, m6c, beq_code henc32] at hc'
      exact Or.inr hc'
    · exact Or.inl (cm6c.1 hb)

end CertificateChecks.KernelSpor.ONKL

end
