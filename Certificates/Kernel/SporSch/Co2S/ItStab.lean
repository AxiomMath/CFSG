module

public import Certificates.Kernel.SporSch.Co2S.ItOrb
public import Certificates.Kernel.SporSch.Co2S.ItHead
public import Certificates.Kernel.SporSch.Co2S.ItCount
public import Certificates.Kernel.Sporadic.Co2.Order
public import CFSG.Certificates.Kernel.SporSch.BaseBoundSound
public import CFSG.Sporadic.Co2Cert.Order
public import CFSG.Certificates.NativeSetOrbit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2It

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.SporSch.Co2SFix
open CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open scoped Pointwise

theorem gens : allN 2 (fun k => Nat.beq (Co2ItC.S k) (Co2A.S k)) = true := by quickRfl

theorem hG : co2P = Subgroup.closure (Set.range fun j : Fin 2 =>
    permOfArr 2300 (unpack 2300 12 (Co2ItC.S j))) := by
  rw [Co2Order.range_two (fun j => permOfArr 2300 (unpack 2300 12 (Co2ItC.S j))),
    Nat.eq_of_beq_eq_true (allN_spec gens 0 (by norm_num)),
    Nat.eq_of_beq_eq_true (allN_spec gens 1 (by norm_num)), ← Co2Order.a_eq 0 (by norm_num),
    ← Co2Order.a_eq 1 (by norm_num)]
  rfl

theorem orbits : ((List.range 9).map fun i => rcnt (Co2ItC.LR i)).prod = 42305421312000 := by
  decide

theorem stab_le :
    Nat.card {g : co2P // ∀ x : Fin 2300, x.val ∈ co2ItNat →
      ((g : Equiv.Perm (Fin 2300)) x).val ∈ co2ItNat} ≤ 41287680 := by
  have h := baseBound_sound (nb := 9) (NS := 36) (CH := 64) hG Co2ItC.head Co2ItC.ho
    (by norm_num) (by norm_num) (le_of_eq (by rw [card_co2P, orbits])) mk
  rw [Nat.eq_of_beq_eq_true bb] at h
  exact h

theorem orbit_card :
    1024650 ≤ (Set.range fun g : co2P => g • finSet 2300 co2ItNat).ncard := by
  let S := finSet 2300 co2ItNat
  have hstab : Nat.card (MulAction.stabilizer co2P S) ≤ 41287680 := by
    refine le_trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_))) stab_le
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hg x hx
      have : (g : Equiv.Perm (Fin 2300)) x ∈ g • S := Set.smul_mem_smul_set (a := g) hx
      rw [hg] at this
      exact this
    · intro hg
      have hsub : g • S ⊆ S := by
        rintro _ ⟨x, hx, rfl⟩
        exact hg x hx
      have hfin : S.Finite := Set.toFinite S
      exact Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_smul_set]) hfin
  have h1 := MulAction.index_stabilizer co2P S
  have h2 := (MulAction.stabilizer co2P S).card_mul_index
  rw [card_co2P, h1] at h2
  have hpos : 0 < Nat.card (MulAction.stabilizer co2P S) := Nat.card_pos
  have : 1024650 ≤ (MulAction.orbit co2P S).ncard := by
    by_contra hlt
    push Not at hlt
    have := Nat.mul_le_mul hstab (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hlt))
    nlinarith
  exact this

end CertificateChecks.KernelSporSch.Co2It

end
