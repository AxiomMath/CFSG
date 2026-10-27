module

public import Certificates.Kernel.L34Pk.A7036
public import Certificates.Kernel.L34Pk.K7077
public import Certificates.Kernel.LocalComp.WittCount

public section

namespace CertificateChecks.KernelL34

open Equiv CFSG.KS.PCnt CFSG.KC.L34 CFSG.KC.WCnt CFSG.Quasithin.L34Amalgam
  CFSG.Quasithin.Asc94 CFSG.ComponentClassification.WittDesign CertificateChecks.KernelLC.Witt

set_option maxRecDepth 100000

theorem fix012 {σ : Perm (Fin 22)} (h : ∀ y ∈ m22HexadL, (σ * 1) y = y) :
    Nat.beq (σ 0).val 0 = true ∧ Nat.beq (σ 1).val 1 = true ∧ Nat.beq (σ 2).val 2 = true := by
  simp only [mul_one] at h
  simp [h 0 (by decide), h 1 (by decide), h 2 (by decide)]

theorem mem_hex : ∀ x : Fin 22, x ∈ m22HexadL → inM 655879 x.val = true := by decide +kernel

theorem pow_eq_one {g : M22} {G : Nat} (hg : pkw 5 (g : Perm (Fin 22)) = G) (k : Nat)
    (h : Nat.beq (ppw 22 5 31 G k) pI = true) : g ^ (k + 1) = 1 :=
  Subtype.ext (pkw_inj (n := 22) (w := 5) (by norm_num) (by
    rw [SubmonoidClass.coe_pow, ← pkw_ppw (n := 22) (w := 5) (by norm_num) (by norm_num),
      mask_five, hg,
      OneMemClass.coe_one, pk_one']
    exact Nat.eq_of_beq_eq_true h))

set_option maxRecDepth 100000 in
theorem c2_pts : (∀ x : Fin 22, x ∈ m22HexadL → upk22 tA2 x ∈ m22HexadL) ∧
    (∀ x : Fin 22, x ∈ m22HexadL → upk22 tB2 x ∈ m22HexadL) ∧
    upk22 tA2 0 = 0 ∧ upk22 tA2 3 = 3 ∧ upk22 tB2 0 = 0 ∧ upk22 tB2 3 = 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cWords_ok : cWords.Nodup ∧ cWords.length = 60 := by decide +kernel

set_option maxRecDepth 100000 in
theorem a2_sq : Nat.beq (pm tA2 tA2) pI = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem b2_cube : Nat.beq (ppw 22 5 31 tB2 2) pI = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ab_five : Nat.beq (ppw 22 5 31 (pm tA2 tB2) 4) pI = true := by decide +kernel

theorem pk_c2OfWord_tab : ∀ s, encT (tab (c2OfWord s)) = pfold labC2 s.toList pI := fun s => by
  rw [encT_tab, pkw_c2OfWord]

theorem count_b2 :
    m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧
      (∀ x, σ ((b2r : Equiv.Perm (Fin 22)) x) = (b2r : Equiv.Perm (Fin 22)) (σ x)) ∧
        ¬ ∀ x, σ x = x) = 0 := by
  have e := coe_eq_upk pk_b2
  have hc : m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧
      (∀ x, σ ((b2r : Equiv.Perm (Fin 22)) x) = (b2r : Equiv.Perm (Fin 22)) (σ x)) ∧
        ¬ ∀ x, σ x = x) = m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧
      (∀ x, σ (upk22 tB2 x) = upk22 tB2 (σ x)) ∧ ¬ ∀ x, σ x = x) := by
    rw [← card_m22_subtype, ← card_m22_subtype]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by rw [e])
  rw [hc]
  exact (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun _ h => fix012 h.1).trans k77e

theorem count_a :
    m22Count (fun σ => ∀ y ∈ m22HexadL, σ y = y) = 16 :=
  (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun _ h => fix012 h).trans k77a

theorem count_sq :
    m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧ ¬ ∀ x, σ (σ x) = x) = 0 :=
  (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun _ h => fix012 h.1).trans k77b

theorem count_c :
    m22Count (fun σ => (σ 0 = 0 ∧ ∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧ σ 3 = 3) = 60 := by
  refine (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun σ h => ?_).trans k77c
  simp only [mul_one] at h
  refine ⟨?_, mem_hex _ (h.1.2 1 (by decide)), mem_hex _ (h.1.2 2 (by decide))⟩
  rw [h.1.1]
  rfl

theorem count_three :
    m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧ σ 3 = 3 ∧ ¬ ∀ x, σ x = x) = 0 :=
  (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun _ h => fix012 h.1).trans k77d

theorem c2_facts :
    (((a2r : Equiv.Perm (Fin 22)) 0 = 0 ∧
        ∀ p ∈ m22HexadL, (a2r : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧
          (a2r : Equiv.Perm (Fin 22)) 3 = 3) ∧
        (((b2r : Equiv.Perm (Fin 22)) 0 = 0 ∧
          ∀ p ∈ m22HexadL, (b2r : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧
            (b2r : Equiv.Perm (Fin 22)) 3 = 3) ∧
        a2r * a2r = 1 ∧ b2r ^ 3 = 1 ∧ (a2r * b2r) ^ 5 = 1 := by
  have hp := c2_pts
  rw [coe_eq_upk pk_a2, coe_eq_upk pk_b2]
  refine ⟨⟨⟨hp.2.2.1, hp.1⟩, hp.2.2.2.1⟩, ⟨⟨hp.2.2.2.2.1, hp.2.1⟩, hp.2.2.2.2.2⟩,
    sq_eq_one pk_a2 a2_sq, pow_eq_one pk_b2 2 b2_cube, ?_⟩
  have hab : pkw 5 ((a2r * b2r : M22) : Perm (Fin 22)) = pm tA2 tB2 := by
    rw [Subgroup.coe_mul, pkw_mul', pk_a2, pk_b2]
  exact pow_eq_one hab 4 ab_five

theorem c2P_nodup : (cWords.map fun s => pfold labC2 s.toList pI).Nodup := by
  rw [k_c2]
  exact k_c2L

theorem c2_map_eq : (cWords.map fun s => tab (c2OfWord s)).map encT =
    cWords.map fun s => pfold labC2 s.toList pI := by
  rw [List.map_map]
  refine List.map_congr_left fun s _ => ?_
  rw [Function.comp_apply]
  exact pk_c2OfWord_tab s

theorem c2_nodup : (cWords.map fun s => tab (c2OfWord s)).Nodup := by
  have h : ((cWords.map fun s => tab (c2OfWord s)).map encT).Nodup := by
    rw [c2_map_eq]
    exact c2P_nodup
  refine (nodup_map_encT (fun T hT => ?_)).1 h
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hT
  exact V_tab _

theorem facts7077 :
    (m22Count (fun σ => ∀ y ∈ m22HexadL, σ y = y) = 16)
    ∧ (m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧ ¬ ∀ x, σ (σ x) = x) = 0)
    ∧ (m22Count (fun σ => (σ 0 = 0 ∧ ∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧ σ 3 = 3) = 60)
    ∧ (m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧ σ 3 = 3 ∧ ¬ ∀ x, σ x = x) = 0)
    ∧ (m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧
        (∀ x, σ ((b2r : Equiv.Perm (Fin 22)) x) = (b2r : Equiv.Perm (Fin 22)) (σ x)) ∧
          ¬ ∀ x, σ x = x) = 0)
    ∧ ((((a2r : Equiv.Perm (Fin 22)) 0 = 0 ∧
        ∀ p ∈ m22HexadL, (a2r : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧
          (a2r : Equiv.Perm (Fin 22)) 3 = 3) ∧
        (((b2r : Equiv.Perm (Fin 22)) 0 = 0 ∧
          ∀ p ∈ m22HexadL, (b2r : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧
            (b2r : Equiv.Perm (Fin 22)) 3 = 3) ∧
        a2r * a2r = 1 ∧ b2r ^ 3 = 1 ∧ (a2r * b2r) ^ 5 = 1)
    ∧ (cWords.Nodup ∧ cWords.length = 60)
    ∧ ((cWords.map fun s => tab (c2OfWord s)).Nodup) :=
  ⟨count_a, count_sq, count_c, count_three, count_b2, c2_facts, cWords_ok, c2_nodup⟩

end CertificateChecks.KernelL34

end
