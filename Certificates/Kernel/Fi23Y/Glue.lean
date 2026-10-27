module

public import Certificates.Kernel.Fi23Y.Sound
import Certificates.Kernel.Fi23Y.ChkE
import Certificates.Kernel.Fi23Y.ChkC
import Certificates.Kernel.Fi23O4.Glue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Y

open CFSG.KC.Enum CFSG.KC.Fi23Y CFSG.KD.Fi23Y CFSG.KD.Fi23S CFSG.KD.Fi23K CFSG.KS.Raw.Orb
open CFSG.ComponentClassification.RankTwoSporadic.Fi23

theorem roots_all : (∀ i < 3, rootY CFSG.KD.Fi23Y.GL CD LS FW i = true) ∧
    ∀ r < 96, repY CD FW r = true := by
  have h := roots_ok
  unfold rootsF at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact ⟨allN_iff.1 h.1, allN_iff.1 h.2⟩

theorem cen_all : ∀ l < 262144, cenY CFSG.KD.Fi23Y.GL CD FJ FW l = true := by
  intro l hl
  have hs : ∀ s < 8, cenF s = true := by
    intro s hs
    interval_cases s
    exacts [cen0_ok, cen1_ok, cen2_ok, cen3_ok, cen4_ok, cen5_ok, cen6_ok, cen7_ok]
  have h := hs (l / 32768) (by omega)
  unfold cenF at h
  have h' := allN_iff.1 h (l % 32768) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq] at h'
  have e : Nat.add (Nat.mul (l / 32768) 32768) (l % 32768) = l := by
    change l / 32768 * 32768 + l % 32768 = l
    omega
  rwa [e] at h'

theorem ent_all : ∀ i < 3, ∀ r < 96, entY CFSG.KD.Fi23Y.GL TR CD FW i r = true := by
  intro i hi
  have h : entF i = true := by
    interval_cases i
    exacts [ent0_ok, ent1_ok, ent2_ok]
  exact allN_iff.1 h

theorem facts_Xc :
    Fi23CensusFactsOn Xc :=
  facts_of_K roots_all.1 roots_all.2 cen_all ent_all

theorem closure_gens_eq :
    Subgroup.closure (CFSG.RankThree.Native.permsA 31671 fi23Gens) = Xc := by
  have hg : fi23Gens = #[orbLit.alpha.map UInt32.toNat, orbLit.beta.map UInt32.toNat] := by
    unfold fi23Gens
    rw [CFSG.KD.Fi23K.orbitData_eq']
  have hle : Subgroup.closure (CFSG.RankThree.Native.permsA 31671 fi23Gens) ≤ Xc := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 2 := by rw [hg] at hk; simpa using hk
    rw [hg]
    interval_cases k
    · change CFSG.Monster.B.Co2.permOfArr 31671 (orbLit.alpha.map UInt32.toNat) ∈ Xc
      rw [CFSG.RankThree.Native.permOfArr_eq_of_rep CertificateChecks.KernelFi23O4.rep_alpha]
      exact CertificateChecks.KernelFi23R.phiX_mem' _
    · change CFSG.Monster.B.Co2.permOfArr 31671 (orbLit.beta.map UInt32.toNat) ∈ Xc
      rw [CFSG.RankThree.Native.permOfArr_eq_of_rep CertificateChecks.KernelFi23O4.rep_beta]
      exact CertificateChecks.KernelFi23R.phiX_mem' _
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_Xc_eq, ← fi23P_eq_closure_permsA, card_fi23P]

theorem fi23_facts :
    Fi23CensusFacts := by
  unfold Fi23CensusFacts
  rw [closure_gens_eq]
  exact facts_Xc

end CertificateChecks.KernelFi23Y

end
