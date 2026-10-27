module

public import Certificates.Kernel.HNLocal.Regs
public import CFSG.Certificates.Kernel.J4Hub.PcNormal
public import CFSG.Certificates.Kernel.HNLocalSound
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import Certificates.Kernel.HNLocal.Fix
import Certificates.Kernel.HNLocal.Checks.R
import Certificates.Kernel.HNLocal.Checks.Cen0
import Certificates.Kernel.HNLocal.Checks.Cen1
import Certificates.Kernel.HNLocal.Checks.Cen2
import Certificates.Kernel.HNLocal.Checks.Cen3
import Certificates.Kernel.HNLocal.Checks.Cen4
import Certificates.Kernel.HNLocal.Checks.Cen5
import Certificates.Kernel.HNLocal.Checks.Cen6
import Certificates.Kernel.HNLocal.Checks.Cen7
import Certificates.Kernel.HN3166.Ord
import CFSG.Certificates.Kernel.Orders.HN.Checks.S2
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Open.Defs

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHNLocal

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub CFSG.KC.HNLocal CFSG.KD.HNLocal CFSG.Sporadic.F5
open CFSG.Sporadic.HN.LocalK
open scoped Matrix

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

local notation "S2PR" => (nat_lit 0x153014a013d01340127011a010f010200fb00f300e900e100d500cc)

noncomputable abbrev Q2 : Subgroup (GL (Fin (Dt).d) (ZMod 5)) :=
  pcSub 5 (Dt).d 13 1729 CFSG.KD.OrdHN.RW S2PR 0 14

open CFSG.KD.OrdHN in
theorem Q2_normal : Nat.card Q2 = 2 ^ 14 ∧ ∀ g ∈ Q2, ∃ e : Nat → Nat, (∀ k, e k < 2) ∧
    ((g : GL (Fin (Dt).d) (ZMod 5)) : Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5)) =
      nfProd 5 (Dt).d 13 1729 RW S2PR e 0 14 :=
  pcSub_normal (p := nat_lit 5) (d := nat_lit 0x85) (w := nat_lit 13) (S := nat_lit 0x6c1)
    (T := nat_lit 9) (q := 2)
    (nb := nat_lit 229957) (hnb := rfl) (PR := CFSG.KD.OrdHN.S2.PR)
    (PW := CFSG.KD.OrdHN.S2.PW) (n := nat_lit 14) (pb := nat_lit 1)
    (Cs := CFSG.KD.OrdHN.S2.PC)
    consts CertificateChecks.KernelHN.o_regs
    Nat.prime_two s2_pr s2_pw s2_pc CertificateChecks.KernelHN.s2_blocks

open CFSG.KD.OrdHN in
theorem Q2_le : Q2 ≤ J Dt :=
  pcSub_le (nb := nat_lit 229957) rfl consts CertificateChecks.KernelHN.o_regs s2_pr 0

noncomputable abbrev QJ : Subgroup (J Dt) := Q2.subgroupOf (J Dt)

theorem card_QJ : Nat.card QJ = 2 ^ 14 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q2_le).toEquiv]
  exact Q2_normal.1

theorem PC_eq (k : Nat) (hk : k < 14) : PC k = CFSG.KD.OrdHN.RW (at16 S2PR k) := by
  interval_cases k
  · exact Nat.eq_of_beq_eq_true pc0
  · exact Nat.eq_of_beq_eq_true pc1
  · exact Nat.eq_of_beq_eq_true pc2
  · exact Nat.eq_of_beq_eq_true pc3
  · exact Nat.eq_of_beq_eq_true pc4
  · exact Nat.eq_of_beq_eq_true pc5
  · exact Nat.eq_of_beq_eq_true pc6
  · exact Nat.eq_of_beq_eq_true pc7
  · exact Nat.eq_of_beq_eq_true pc8
  · exact Nat.eq_of_beq_eq_true pc9
  · exact Nat.eq_of_beq_eq_true pc10
  · exact Nat.eq_of_beq_eq_true pc11
  · exact Nat.eq_of_beq_eq_true pc12
  · exact Nat.eq_of_beq_eq_true pc13

theorem regsIn_s2 : ∀ k < 14, 0 < at16 S2PR k ∧ at16 S2PR k < 799 :=
  regsIn_spec CFSG.KD.OrdHN.s2_pr

theorem canon_PC (k : Nat) (hk : k < 14) : Canon 5 133 13 (PC k) := by
  rw [PC_eq k hk]
  obtain ⟨h0, h1⟩ := regsIn_s2 k hk
  exact canon_of_valid (CertificateChecks.KernelHN.o_regs _ h0 h1).1

theorem canon_RP (a : Nat) (ha : a < 32) : Canon 5 133 13 (RP a) :=
  canon_root (r := 16 + a) (by omega) (by omega)

theorem nfProd_eq (e : Nat → Nat) :
    nfProd 5 (Dt).d 13 1729 CFSG.KD.OrdHN.RW S2PR e 0 14 = CFSG.KS.HNLocal.nfE PC 14 e := by
  unfold nfProd CFSG.KS.HNLocal.nfE
  refine congrArg List.prod (List.map_congr_left fun k hk => ?_)
  rw [List.mem_range'] at hk
  unfold pcMat
  rw [PC_eq k (by omega)]
  rfl

theorem census_nf (e : Nat → Nat) (he : ∀ k, e k < 2) :
    CFSG.KS.HNLocal.nfE PC 14 e = 1 ∨ CFSG.KS.HNLocal.nfE PC 14 e * CFSG.KS.HNLocal.nfE PC 14 e ≠ 1 ∨
      ∃ a < 32, ∃ q, q % 2 = 1 ∧ (CFSG.KS.HNLocal.nfE PC 14 e * CFSG.KS.HNLocal.OM (RP a)) ^ q = 1 := by
  have hc : ∀ m < 16, cenAt mul vm PC RP TG 32 CFSG.KD.OrdHN.ONE CFSG.KD.OrdHN.RM m 4 10 = true := by
    intro m hm
    interval_cases m
    · exact ce0
    · exact ce1
    · exact ce2
    · exact ce3
    · exact ce4
    · exact ce5
    · exact ce6
    · exact ce7
    · exact ce8
    · exact ce9
    · exact ce10
    · exact ce11
    · exact ce12
    · exact ce13
    · exact ce14
    · exact ce15
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  have hm : e 0 + 2 * e 1 + 4 * e 2 + 8 * e 3 < 16 := by omega
  exact CFSG.KS.HNLocal.cenAt_sound consts (fun i hi => canon_PC i (by omega)) canon_RP
    (by norm_num; omega) (hc _ hm) e he (fun i hi => by interval_cases i <;> omega)

theorem census : ∀ g ∈ QJ, g ^ 2 = 1 → g ≠ 1 →
    ∃ (i : Fin 2) (h : J Dt) (m : ℕ), m % 2 = 1 ∧ (g * (h * wG (12 + i.val) * h⁻¹)) ^ m = 1 := by
  intro g hg hg2 hg1
  obtain ⟨e, he, hge⟩ := Q2_normal.2 g.1 hg
  have hmat : mat Dt g = CFSG.KS.HNLocal.nfE PC 14 e := by
    rw [← nfProd_eq]; exact hge
  have hsq : mat Dt g * mat Dt g = 1 := by
    rw [← CertificateChecks.KernelHN.mat_mul', ← pow_two, hg2]
    rfl
  rcases census_nf e he with h1 | h2 | ⟨a, ha, q, hq, hpow⟩
  · have e1 : mat Dt g = mat Dt 1 := by
      rw [hmat, h1]
      rfl
    exact absurd (mat_injective Dt e1) hg1
  · exact (h2 (by rw [← hmat]; exact hsq)).elim
  · obtain ⟨hR, hidx⟩ := mat_partner ha
    refine ⟨⟨pIdx a, hidx⟩, hP a, q, hq, mat_injective Dt ?_⟩
    have e1 : mat Dt ((g * (hP a * wG (12 + pIdx a) * (hP a)⁻¹)) ^ q) =
        (mat Dt g * mat Dt (hP a * wG (12 + pIdx a) * (hP a)⁻¹)) ^ q := by
      rw [CertificateChecks.KernelHN.mat_pow', CertificateChecks.KernelHN.mat_mul']
    rw [e1, ← hR, hmat]
    exact hpow.trans rfl

end CertificateChecks.KernelHNLocal

end
