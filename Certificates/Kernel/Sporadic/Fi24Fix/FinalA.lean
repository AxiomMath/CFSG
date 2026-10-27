module

public import Certificates.Kernel.Sporadic.Fi24Fix.Final
import Certificates.Kernel.Sporadic.Fi24Fix.RootA

public section

namespace CertificateChecks.KernelFi24Fix

open CertificateChecks.KernelFi24 CertificateChecks.KernelCo2 TauCeti TauCeti.Sporadic
  CFSG.Sporadic.Bridge CFSG.KC.Fi24FixC CFSG.KC.Fi24FixS CFSG.KC.Fi24FixK CFSG.KD.Fi24Fix
  CFSG.KS.Mat3

theorem certificate1019_proof : ∃ Γ : Subgroup (GL (Fin 781) (ZMod 3)),
    (∀ g : GL (Fin 781) (ZMod 3), g.val = CFSG.Sporadic.Fi24.mA ∨ g.val = CFSG.Sporadic.Fi24.mB →
      g ∈ Γ) ∧
    ∀ P : Fin 306936 → Submodule (ZMod 3) (Fin 781 → ZMod 3), Function.Injective P →
      (∀ k, ∃ g ∈ Γ, P k = (CFSG.Sporadic.Fi24.pt 0).sp.map
        (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3)))) →
      ∃ Ψ : Finset (Fin 306936), Ψ.card = 31671 ∧ (∀ k ∈ Ψ, P k ≠ (CFSG.Sporadic.Fi24.pt 0).sp) ∧
        (∀ g ∈ Γ, (CFSG.Sporadic.Fi24.pt 0).sp.map
            (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3))) =
            (CFSG.Sporadic.Fi24.pt 0).sp →
          ∀ k ∈ Ψ, ∃ k' ∈ Ψ,
            (P k).map (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3))) = P k') ∧
        ∃ k ∈ Ψ, P k = (CFSG.Sporadic.Fi24.pt 0).sp.map
          (Matrix.mulVecLin CFSG.Sporadic.Fi24.mA) := by
  obtain ⟨x, hx, -, hrel, hcl, hstab, hroot, hA⟩ := matFacts
  obtain ⟨R, hR0, hT, hcov⟩ := rankFacts
  set σ := presHom fi24PrimePresentation x hrel with hσdef
  let σE : E →* GL (Fin 781) (ZMod 3) :=
    σ.comp fi24PrimeGroupMulEquivCommutator.symm.toMonoidHom
  have hσE : ∀ u, σE (fi24PrimeGroupMulEquivCommutator u) = σ u := by
    intro u
    simp [σE]
  have hσgen : ∀ k < 11, σ (presGen fi24PrimePresentation k) = x k := fun k hk =>
    presHom_presGen _ _ _ (by rw [gcount]; exact hk)
  have hst0 : ∀ (h : Fi24AutomorphismGroup), h ∈ H0 → ∀ hh : h ∈ E, σE ⟨h, hh⟩ ∈ stab V0 := by
    intro h hm
    induction hm using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      intro hh
      have hk : hgen j - 1 < 11 := by have := hgen_lt hj; omega
      have hg1 : 1 ≤ hgen j := by
        by_cases h8 : j = 8 <;> simp [hgen, h8]
      have e : (⟨g0 0 * g0 (hgen j), hh⟩ : E) =
          fi24PrimeGroupMulEquivCommutator (presGen fi24PrimePresentation (hgen j - 1)) := by
        apply Subtype.ext
        rw [iso_presGen hk, Nat.sub_add_cancel hg1]
      rw [e, hσE, hσgen _ hk]
      apply hstab
      by_cases h8 : j = 8
      · subst h8
        right
        rfl
      · left
        have : hgen j = j + 1 := by simp [hgen, h8]
        have hj9 : j < 9 := hj
        omega
    | one =>
      intro hh
      have : (⟨1, hh⟩ : E) = 1 := rfl
      rw [this, map_one]
      exact (stab V0).one_mem
    | mul y z hy hz ihy ihz =>
      intro hh
      have : (⟨y * z, hh⟩ : E) = ⟨y, H0_le_E hy⟩ * ⟨z, H0_le_E hz⟩ := rfl
      rw [this, map_mul]
      exact (stab V0).mul_mem (ihy (H0_le_E hy)) (ihz (H0_le_E hz))
    | inv y hy ihy =>
      intro hh
      have : (⟨y⁻¹, hh⟩ : E) = (⟨y, H0_le_E hy⟩ : E)⁻¹ := rfl
      rw [this, map_inv]
      exact (stab V0).inv_mem (ihy (H0_le_E hy))
  have hst : ∀ (h : Fi24AutomorphismGroup) (hh : h ∈ E), h ∈ H1 → σE ⟨h, hh⟩ ∈ stab V0 :=
    fun h hh hH => hst0 h (H1_inf_E hH hh) hh
  set F : Fi24AutomorphismGroup → Submodule (ZMod 3) (Fin 781 → ZMod 3) :=
    subOf E (g0 0) mem_E_or σE V0 with hFdef
  have hF : ∀ u v, u * v⁻¹ ∈ H1 → F u = F v := fun u v huv => subOf_eq_of_rel a_mem_H1 hst huv
  have hact : ∀ q (e : E), act (σE e) (F q) = F (q * e⁻¹) := by
    intro q e
    rw [hFdef, subOf_mul q e⁻¹, map_inv, inv_inv]
  have hσp : σE pE = wordProd x pv := by
    rw [hσE, presHom_wordProd _ _ _ _ (fun l hl => by rw [gcount]; exact pv_lt l hl)]
  have hFp : F pE = (CFSG.Sporadic.Fi24.pt 0).sp := by
    rw [hFdef, subOf_eq_of_mem _ pE.2]
    change act (σE pE)⁻¹ V0 = _
    rw [hσp, ← hroot, act_inv_act]
  refine ⟨σ.range, fun g hg => ?_, fun P hP hPg => ?_⟩
  · have hc := hcl g hg
    refine (Subgroup.closure_le _).2 ?_ hc
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨_, hσgen k hk⟩
  have hΓ : ∀ g ∈ σ.range, ∃ e : E, σE e = g := by
    rintro g ⟨u, rfl⟩
    exact ⟨fi24PrimeGroupMulEquivCommutator u, hσE u⟩
  have hmap : ∀ (g : GL (Fin 781) (ZMod 3)) (W : Submodule (ZMod 3) (Fin 781 → ZMod 3)),
      W.map (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3))) = act g W := fun _ _ => rfl
  have hPF : ∀ k, ∃ q, P k = F q := by
    intro k
    obtain ⟨g, hg, hk⟩ := hPg k
    obtain ⟨e, rfl⟩ := hΓ g hg
    refine ⟨(pE : Fi24AutomorphismGroup) * (e⁻¹ : E), ?_⟩
    rw [hk, hmap, ← hFp, hact]
  obtain ⟨hinj, hsep, hsurj⟩ := rel_of_eq R hcov F hF P hP hPF
  have hrr : ∀ r r', r < 306936 → r' < 306936 → R r * (R r')⁻¹ ∈ H1 → r = r' := by
    intro r r' hr hr' h
    have := @hinj ⟨r, hr⟩ ⟨r', hr'⟩ (hF _ _ h)
    exact congrArg Fin.val this
  choose kOf hkOf using hsurj
  have hW := walk_rel H1 R g0 TG hT
  have hPW : ∀ g ∈ PW, g < 12 := by decide
  have hAW : ∀ g ∈ AW, g < 12 := by decide
  have hψ : ∀ j < 31671, walk TG PW (S j) < 306936 ∧
      R (S j) * (pE : Fi24AutomorphismGroup) * (R (walk TG PW (S j)))⁻¹ ∈ H1 := by
    intro j hj
    rw [pE_eq]
    exact hW PW hPW (S j) (S_facts.1 j hj).2
  let kψ : ℕ → Fin 306936 := fun j =>
    if h : walk TG PW (S j) < 306936 then kOf ⟨walk TG PW (S j), h⟩ else 0
  have hkψ : ∀ j < 31671, P (kψ j) = F (R (walk TG PW (S j))) := by
    intro j hj
    have h := (hψ j hj).1
    simp only [kψ, dif_pos h]
    exact hkOf _
  have hkinj : Set.InjOn kψ (Finset.range 31671 : Set ℕ) := by
    intro j hj j' hj' h
    simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
    have e1 : F (R (walk TG PW (S j))) = F (R (walk TG PW (S j'))) := by
      rw [← hkψ j hj, ← hkψ j' hj', h]
    have e2 := @hinj ⟨_, (hψ j hj).1⟩ ⟨_, (hψ j' hj').1⟩ e1
    have e3 : walk TG PW (S j) = walk TG PW (S j') := congrArg Fin.val e2
    have a1 := (hψ j hj).2
    have a2 := (hψ j' hj').2
    rw [e3] at a1
    have e4 : R (S j) * (R (S j'))⁻¹ = (R (S j) * (pE : Fi24AutomorphismGroup) *
        (R (walk TG PW (S j')))⁻¹) * (R (S j') * (pE : Fi24AutomorphismGroup) *
        (R (walk TG PW (S j')))⁻¹)⁻¹ := by group
    have := hrr _ _ (S_facts.1 j hj).2 (S_facts.1 j' hj').2
      (by rw [e4]; exact H1.mul_mem a1 (H1.inv_mem a2))
    exact S_inj hj hj' this
  have hPk : ∀ j < 31671, P (kψ j) = F (R (S j) * (pE : Fi24AutomorphismGroup)) := by
    intro j hj
    rw [hkψ j hj]
    exact (hF _ _ (hψ j hj).2).symm
  have hmemΨ : ∀ k ∈ (Finset.range 31671).image kψ, ∃ j < 31671, k = kψ j := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hk
    exact ⟨j, Finset.mem_range.1 hj, rfl⟩
  refine ⟨(Finset.range 31671).image kψ, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hkinj, Finset.card_range]
  · intro k hk h
    obtain ⟨j, hj, rfl⟩ := hmemΨ k hk
    rw [hPk j hj, ← hFp] at h
    have h2 := hsep _ _ h
    have e : R (S j) * (pE : Fi24AutomorphismGroup) * (pE : Fi24AutomorphismGroup)⁻¹ =
        R (S j) * (R 0)⁻¹ := by rw [hR0]; group
    rw [e] at h2
    have := hrr _ _ (S_facts.1 j hj).2 (by norm_num) h2
    have := (S_facts.1 j hj).1
    omega
  · intro g hg hfix k hk
    obtain ⟨e, rfl⟩ := hΓ g hg
    obtain ⟨j, hj, rfl⟩ := hmemΨ k hk
    rw [hmap, ← hFp, hact] at hfix
    have h1 := hsep _ _ hfix
    set m : Fi24AutomorphismGroup :=
      (pE : Fi24AutomorphismGroup) * ((e⁻¹ : E) : Fi24AutomorphismGroup) * (pE : Fi24AutomorphismGroup)⁻¹
    have hmE : m ∈ E := E.mul_mem (E.mul_mem pE.2 (e⁻¹).2) (E.inv_mem pE.2)
    have hm : m ∈ H0 := H1_inf_E h1 hmE
    obtain ⟨i', hi', hr⟩ := closY R hT hrr hm j hj
    refine ⟨kψ i', Finset.mem_image.2 ⟨i', Finset.mem_range.2 hi', rfl⟩, ?_⟩
    rw [hmap, hPk j hj, hact, hPk i' hi']
    apply hF
    have e2 : R (S j) * (pE : Fi24AutomorphismGroup) * ((e⁻¹ : E) : Fi24AutomorphismGroup) *
        (R (S i') * (pE : Fi24AutomorphismGroup))⁻¹ = R (S j) * m * (R (S i'))⁻¹ := by
      simp only [m]
      group
    rw [e2]
    exact hr
  ·
    have hσA : σE eA = x 7 * x 10 := by
      rw [hσE, map_mul, hσgen 7 (by norm_num), hσgen 10 (by norm_num)]
    have hmA : CFSG.Sporadic.Fi24.mA =
        ((σE eA : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) := by
      rw [hσA, hA]
    refine ⟨kψ 1479, Finset.mem_image.2 ⟨1479, Finset.mem_range.2 (by norm_num), rfl⟩, ?_⟩
    rw [hkψ 1479 (by norm_num), hmA, hmap, ← hFp, hact]
    have hwalk : walk TG AW (walk TG PW 0) = walk TG PW (S 1479) := Nat.eq_of_beq_eq_true rootA
    obtain ⟨hr0, hp0⟩ := hW PW hPW 0 (by norm_num)
    obtain ⟨-, ha0⟩ := hW AW hAW (walk TG PW 0) hr0
    rw [← pE_eq, hR0, one_mul] at hp0
    rw [← eA_inv_eq, hwalk] at ha0
    apply hF
    have e : R (walk TG PW (S 1479)) * ((pE : Fi24AutomorphismGroup) *
        ((eA⁻¹ : E) : Fi24AutomorphismGroup))⁻¹ =
        (R (walk TG PW 0) * ((eA : Fi24AutomorphismGroup))⁻¹ *
          (R (walk TG PW (S 1479)))⁻¹)⁻¹ *
        ((pE : Fi24AutomorphismGroup) * (R (walk TG PW 0))⁻¹)⁻¹ := by
      rw [Subgroup.coe_inv]
      group
    rw [e]
    exact H1.mul_mem (H1.inv_mem ha0) (H1.inv_mem hp0)

end CertificateChecks.KernelFi24Fix

end
