
module

public import Certificates.Kernel.J4Count.FixCEEltBase1

public import Certificates.Kernel.J4Count.StarsBase2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.FixCE

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
open CFSG.Quasithin.J4M2 CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.J4FixCE CFSG.KD.J4FixCE
open CFSG.KS.SporSch.C11 MulAction CertificateChecks.KernelJ4Q
open CFSG.Sporadic.SmallF2 (toVecD toVecD_apply)
open CFSG.Sporadic.J4Schreier (app11)

section H

theorem cE_mem_H : cE ∈ CFSG.Sporadic.J4Schreier.H := by
  rw [← CertificateChecks.KernelJ4Count.stabilizer_v]
  exact cE_smul_v

theorem H_eq_Hj : CFSG.Sporadic.J4Schreier.H = Hj := CertificateChecks.KernelJ4Count.H_eq_Hj'

theorem cE_mem_Hj : cE ∈ Hj := by
  rw [← H_eq_Hj]
  exact cE_mem_H

theorem N_eq_Eg : CFSG.Sporadic.J4Schreier.N = Eg uJ 11 := by
  classical
  have hNH : CFSG.Sporadic.J4Schreier.N ≤ Hj := by
    rw [← H_eq_Hj]
    exact CFSG.Sporadic.J4Schreier.N_le_H
  set N' : Subgroup Hj := CFSG.Sporadic.J4Schreier.N.subgroupOf Hj
  have hn : N'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : J) ∈ CFSG.Sporadic.J4Schreier.H := by
      rw [H_eq_Hj]
      exact g.2
    simpa using CFSG.Sporadic.J4Schreier.conj_mem_N_of_mem_H _ hg _ hn
  set E' : Subgroup Hj := (Eg uJ 11).subgroupOf Hj
  let φ := QuotientGroup.mk' E'
  have hs := Stars.isSimpleGroup_Hj_quotient
  have hm : (N'.map φ).Normal := hn.map φ (QuotientGroup.mk'_surjective _)
  have hcN : Nat.card N' = 2 ^ 11 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact CFSG.Sporadic.J4Schreier.card_N
  have : Finite J := CertificateChecks.KernelJ4Hub.finite_J
  have hle : N' ≤ E' := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.map φ) with h | h
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    · exfalso
      have h1 : Nat.card (N'.map φ) ≤ Nat.card N' :=
        Nat.card_le_card_of_surjective _ (φ.subgroupMap_surjective N')
      rw [h, Subgroup.card_top, Stars.card_Hj_quotient,
        hcN] at h1
      norm_num at h1
  have hle' : CFSG.Sporadic.J4Schreier.N ≤ Eg uJ 11 := fun x hx => by
    have := hle (show (⟨x, hNH hx⟩ : Hj) ∈ N' from hx)
    exact this
  refine Subgroup.eq_of_le_of_card_ge hle' ?_
  rw [card_Eg_uJ matFacts, CFSG.Sporadic.J4Schreier.card_N]

end H

section E

end E

section Final

theorem card_cent_N :
    Nat.card ↥(Subgroup.centralizer {cE} ⊓ CFSG.Sporadic.J4Schreier.N) = 32 := by
  rw [N_eq_Eg, inf_comm]
  exact card_cent_E

end Final

end CertificateChecks.KernelJ4Count.FixCE

end
