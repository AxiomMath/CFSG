
module

public import Certificates.Kernel.Sporadic.Fi22.C3151ABase

public import CFSG.Monster.B.Fischer.Fi22CoverBase1

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22C3151

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Text
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22F2
open CertificateChecks.KernelSpor.Fi22LabA (unpack_get' strictB_eq' tr3_eq tlev offs_parts)

theorem prod_apply (x : Fin 1024 × Fin 32 × Fin 4) (p : Fin 3510) :
    (fi22TProd x p : Nat) = g3 x.1 x.2.1 x.2.2 p := by
  rw [fi22TProd_apply, g3_eq x.1.2 x.2.1.2 x.2.2.2 p.2]

theorem gI_eq {I : Nat} (h : I < 131072) (p : Fin 3510) :
    gI I p = (fi22TProd (xF I) p : Nat) := by
  rw [prod_apply]
  unfold gI xF
  simp only [div_eq', mod_eq']
  rw [Nat.mod_eq_of_lt (by omega : I / 128 < 1024)]

theorem gI_eq' {I p : Nat} (h : I < 131072) (hp : p < 3510) :
    gI I p = (fi22TProd (xF I) ⟨p, hp⟩ : Nat) := gI_eq h ⟨p, hp⟩

theorem sepT'
    {g : Equiv.Perm (Fin 3510)} (hg : g ∈ fi22OuterT)
    (h : ∀ t (ht : t < 6), (g ⟨bT t, bT_lt ht⟩ : Nat) = bT t) : g = 1 := by
  refine Fi22C3150.sepP (fi22OuterT_le hg) fun r hr hrl => Fin.ext ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h 0 (by norm_num)
  · exact h 1 (by norm_num)
  · exact h 2 (by norm_num)
  · exact h 3 (by norm_num)
  · exact h 5 (by norm_num)
  · exact h 4 (by norm_num)

theorem one_iff
    (x : Fin 1024 × Fin 32 × Fin 4) :
    allN 6 (fun t => Nat.beq (g3 x.1 x.2.1 x.2.2 (bT t)) (bT t)) = true ↔ fi22TProd x = 1 := by
  constructor
  · intro h
    refine sepT' (fi22TProd_mem x) fun t ht => ?_
    rw [prod_apply]
    exact Nat.eq_of_beq_eq_true (allN_spec h t ht)
  · intro h
    refine allN_of_forall fun t ht => ?_
    have e := prod_apply x ⟨bT t, bT_lt ht⟩
    rw [h] at e
    rw [← e]
    exact Nat.beq_refl _

theorem sq_iff
    (x : Fin 1024 × Fin 32 × Fin 4) :
    allN 6 (fun t => Nat.beq (g3 x.1 x.2.1 x.2.2 (g3 x.1 x.2.1 x.2.2 (bT t))) (bT t)) = true ↔
      fi22TProd x * fi22TProd x = 1 := by
  have e : ∀ t (ht : t < 6), g3 x.1 x.2.1 x.2.2 (g3 x.1 x.2.1 x.2.2 (bT t)) =
      ((fi22TProd x * fi22TProd x) ⟨bT t, bT_lt ht⟩ : Nat) := fun t ht => by
    rw [Equiv.Perm.mul_apply, prod_apply x (fi22TProd x _), prod_apply x ⟨bT t, bT_lt ht⟩]
  constructor
  · intro h
    refine sepT' (Subgroup.mul_mem _ (fi22TProd_mem x) (fi22TProd_mem x)) fun t ht => ?_
    rw [← e t ht]
    exact Nat.eq_of_beq_eq_true (allN_spec h t ht)
  · intro h
    refine allN_of_forall fun t ht => ?_
    rw [e t ht, h]
    exact Nat.beq_refl _

theorem invB_iff
    (x : Fin 1024 × Fin 32 × Fin 4) :
    invB x.1 x.2.1 x.2.2 = true ↔ isInv3 fi22TLevels 3510 x.1 x.2.1 x.2.2 = true := by
  rw [isInv3_iff, orderOf_eq_prime_iff, pow_two, ne_eq, ← one_iff, ← sq_iff]
  unfold invB
  cases allN 6 (fun t => Nat.beq (g3 x.1 x.2.1 x.2.2 (bT t)) (bT t)) <;>
    cases allN 6 (fun t => Nat.beq (g3 x.1 x.2.1 x.2.2 (g3 x.1 x.2.1 x.2.2 (bT t))) (bT t)) <;>
    simp

theorem invB_xF
    {I : Nat} (h : I < 131072) :
    invB (I / 128) (I / 4 % 32) (I % 4) = true ↔
      isInv3 fi22TLevels 3510 (xF I).1 (xF I).2.1 (xF I).2.2 = true := by
  rw [← invB_iff]
  have e := xF_val h
  simp only [xN, Prod.mk.injEq] at e
  rw [e.1, e.2.1, e.2.2]

theorem sv_inv
    (hS : ScanOK) {k : Nat} (hk : k < 3263) :
    isInv3 fi22TLevels 3510 (xF (SV k)).1 (xF (SV k)).2.1 (xF (SV k)).2.2 = true := by
  obtain ⟨hl, hp⟩ := sv_parts hk
  obtain ⟨-, h2, -⟩ := scan_parts (hS _ hl)
  rw [← invB_xF hl]
  cases e : invB (SV k / 128) (SV k / 4 % 32) (SV k % 4)
  · have := h2 e
    omega
  · rfl

theorem card_inv
    (hS : ScanOK) :
    (Finset.univ.filter fun x : Fin 1024 × Fin 32 × Fin 4 =>
      isInv3 fi22TLevels 3510 x.1 x.2.1 x.2.2 = true).card = 3263 := by
  rw [← Finset.card_range 3263]
  refine Finset.card_nbij' (fun x => PPf (iX x)) (fun k => xF (SV k)) (fun x hx => ?_)
    (fun k hk => ?_) (fun x hx => ?_) (fun k hk => ?_)
  · rw [Finset.coe_filter, Set.mem_setOf_eq] at hx
    have hl := iX_lt x
    have hx' := hx.2
    rw [← xF_iX x, ← invB_xF hl] at hx'
    exact Finset.mem_coe.2 (Finset.mem_range.2 ((scan_parts (hS _ hl)).1 hx').1)
  · have hk' := Finset.mem_range.1 (Finset.mem_coe.1 hk)
    rw [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨Finset.mem_univ _, sv_inv hS hk'⟩
  · rw [Finset.coe_filter, Set.mem_setOf_eq] at hx
    have hl := iX_lt x
    have hx' := hx.2
    rw [← xF_iX x, ← invB_xF hl] at hx'
    simp only
    rw [((scan_parts (hS _ hl)).1 hx').2, xF_iX]
  · have hk' := Finset.mem_range.1 (Finset.mem_coe.1 hk)
    obtain ⟨hl, hp⟩ := sv_parts hk'
    simp only
    rw [iX_xF hl, hp]

end CertificateChecks.KernelSpor.Fi22C3151

end
