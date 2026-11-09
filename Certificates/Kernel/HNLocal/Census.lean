module

public import Certificates.Kernel.HNLocal.Regs
public import CFSG.Certificates.Kernel.J4Hub.PcNormal
public import CFSG.Certificates.Kernel.HNLocalSound
import CFSG.Certificates.Kernel.HNLocal.CenV
import CFSG.Certificates.Kernel.HNLocal.CenD
public import Certificates.Data.Kernel.HNLocalD
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import Certificates.Kernel.HNLocal.Fix
import Certificates.Kernel.HNLocal.Checks.R
import Certificates.Kernel.HNLocal.Checks.Cen0
import Certificates.Kernel.HNLocal.Checks.Cen1
import Certificates.Kernel.HNLocal.Checks.Cen3
import Certificates.Kernel.HNLocal.Checks.Cen4
import Certificates.Kernel.HNLocal.Checks.Cen7
import Certificates.Kernel.HNLocal.Checks.CenD0a
import Certificates.Kernel.HNLocal.Checks.CenD0b
import Certificates.Kernel.HNLocal.Checks.CenD0c
import Certificates.Kernel.HNLocal.Checks.CenD0d
import Certificates.Kernel.HNLocal.Checks.CenD0e
import Certificates.Kernel.HNLocal.Checks.CenD0f
import Certificates.Kernel.HNLocal.Checks.CenD0g
import Certificates.Kernel.HNLocal.Checks.CenD0h
import Certificates.Kernel.HNLocal.Checks.CenD0i
import Certificates.Kernel.HNLocal.Checks.CenD0j
import Certificates.Kernel.HNLocal.Checks.CenD0k
import Certificates.Kernel.HNLocal.Checks.CenD0l
import Certificates.Kernel.HNLocal.Checks.CenD0m
import Certificates.Kernel.HNLocal.Checks.CenD0n
import Certificates.Kernel.HNLocal.Checks.CenD4
import Certificates.Kernel.HNLocal.Checks.CenD4b
import Certificates.Kernel.HNLocal.Checks.CenD4c
import Certificates.Kernel.HNLocal.Checks.CenD8
import Certificates.Kernel.HNLocal.Checks.CenD8b
import Certificates.Kernel.HNLocal.Checks.CenD8c
import Certificates.Kernel.HNLocal.Checks.CenD12
import Certificates.Kernel.HNLocal.Checks.CenD12b
import Certificates.Kernel.HNLocal.Checks.CenD12c
import Certificates.Kernel.HNLocal.Checks.CenD5
import Certificates.Kernel.HNLocal.Checks.CenD5b
import Certificates.Kernel.HNLocal.Checks.CenD6
import Certificates.Kernel.HNLocal.Checks.CenD6b
import Certificates.Kernel.HNLocal.Checks.CenD10
import Certificates.Kernel.HNLocal.Checks.CenD10b
import Certificates.Kernel.HNLocal.Checks.CenD11
import Certificates.Kernel.HNLocal.Checks.CenD11b
import Certificates.Kernel.HNLocal.Checks.CenD13
import Certificates.Kernel.HNLocal.Checks.CenD13b
import Certificates.Kernel.HNLocal.Checks.CenD15
import Certificates.Kernel.HNLocal.Checks.CenD15b
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

noncomputable abbrev Q2M (x : GL (Fin (Dt).d) (ZMod 5)) : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  (x : Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5))

theorem Q2M_one : Q2M 1 = 1 := rfl

theorem partner_lift {N : Matrix (Fin 133) (Fin 133) (ZMod 5)} :
    N = 1 ∨ N * N ≠ 1 ∨ (∃ a < 32, ∃ q, q % 2 = 1 ∧ (N * CFSG.KS.HNLocal.OM (RP a)) ^ q = 1) →
      N = 1 ∨ N * N ≠ 1 ∨ ∃ x ∈ Q2, ∃ a < 32, ∃ q, q % 2 = 1 ∧
        (N * (Q2M x * CFSG.KS.HNLocal.OM (RP a) * Q2M x⁻¹)) ^ q = 1
  | Or.inl h => Or.inl h
  | Or.inr (Or.inl h) => Or.inr (Or.inl h)
  | Or.inr (Or.inr ⟨a, ha, q, hq, h⟩) => Or.inr (Or.inr ⟨1, Q2.one_mem, a, ha, q, hq, by
      rw [inv_one, Q2M_one, one_mul, mul_one]
      exact h⟩)

def DListOK (D : List Nat) : Prop :=
  ∀ d ∈ D, ∀ e : Nat → Nat, (∀ i, e i < 2) → (∀ i < 14, e i = d / 2 ^ i % 2) →
    CFSG.KS.HNLocal.nfE PC 14 e = 1 ∨
      CFSG.KS.HNLocal.nfE PC 14 e * CFSG.KS.HNLocal.nfE PC 14 e ≠ 1 ∨
      ∃ a < 32, ∃ q, q % 2 = 1 ∧
        (CFSG.KS.HNLocal.nfE PC 14 e * CFSG.KS.HNLocal.OM (RP a)) ^ q = 1

theorem DListOK_of {D : List Nat}
    (h : CFSG.KC.HNLocal.cenDL mul vm PC RP TG 32 CFSG.KD.OrdHN.ONE CFSG.KD.OrdHN.RM 14 D = true) :
    DListOK D :=
  CFSG.KS.HNLocal.cenDL_sound (k := 14) consts (fun i hi => canon_PC i hi) canon_RP h

theorem DListOK_append {A B : List Nat} (hA : DListOK A) (hB : DListOK B) : DListOK (A ++ B) :=
  fun d hd => (List.mem_append.1 hd).elim (hA d) (hB d)

theorem block_DL {m : Nat} (hm : m < 2 ^ 4) {D : List Nat}
    (hV : CFSG.KC.HNLocal.cenVDAt vm PC TG D 0 m 4 10 = true) (hD : DListOK D) :
    ∀ e : Nat → Nat, (∀ i, e i < 2) → (∀ i < 4, e i = m / 2 ^ i % 2) →
      CFSG.KS.HNLocal.nfE PC 14 e = 1 ∨
        CFSG.KS.HNLocal.nfE PC 14 e * CFSG.KS.HNLocal.nfE PC 14 e ≠ 1 ∨
        ∃ a < 32, ∃ q, q % 2 = 1 ∧
          (CFSG.KS.HNLocal.nfE PC 14 e * CFSG.KS.HNLocal.OM (RP a)) ^ q = 1 := by
  intro e he hek
  have hPC : ∀ i < 4 + 10, Canon 5 133 13 (PC i) := fun i hi => canon_PC i (by omega)
  rcases CFSG.KS.HNLocal.cenVDAt_sound (k := 4) (n := 10) consts hPC (by norm_num) hm hV e he hek
    with h | ⟨d, hd, hb⟩
  · exact Or.inr (Or.inl h)
  · exact hD d hd e he hb

theorem census_nf (e : Nat → Nat) (he : ∀ k, e k < 2) :
    CFSG.KS.HNLocal.nfE PC 14 e = 1 ∨ CFSG.KS.HNLocal.nfE PC 14 e * CFSG.KS.HNLocal.nfE PC 14 e ≠ 1 ∨
      ∃ x ∈ Q2, ∃ a < 32, ∃ q, q % 2 = 1 ∧
        (CFSG.KS.HNLocal.nfE PC 14 e * (Q2M x * CFSG.KS.HNLocal.OM (RP a) * Q2M x⁻¹)) ^ q = 1 := by
  have hPC : ∀ i < 4 + 10, Canon 5 133 13 (PC i) := fun i hi => canon_PC i (by omega)
  have hc : ∀ m < 16, ∀ e : Nat → Nat, (∀ i, e i < 2) → (∀ i < 4, e i = m / 2 ^ i % 2) →
      CFSG.KS.HNLocal.nfE PC 14 e = 1 ∨
        CFSG.KS.HNLocal.nfE PC 14 e * CFSG.KS.HNLocal.nfE PC 14 e ≠ 1 ∨
        ∃ a < 32, ∃ q, q % 2 = 1 ∧
          (CFSG.KS.HNLocal.nfE PC 14 e * CFSG.KS.HNLocal.OM (RP a)) ^ q = 1 := by
    intro m hm
    interval_cases m
    · refine block_DL (by norm_num) ceV0 ?_
      refine DListOK_append (DListOK_of ceD0a) (DListOK_append (DListOK_of ceD0b)
        (DListOK_append (DListOK_of ceD0c) (DListOK_append (DListOK_of ceD0d)
        (DListOK_append (DListOK_of ceD0e) (DListOK_append (DListOK_of ceD0f)
        (DListOK_append (DListOK_of ceD0g) (DListOK_append (DListOK_of ceD0h)
        (DListOK_append (DListOK_of ceD0i) (DListOK_append (DListOK_of ceD0j)
        (DListOK_append (DListOK_of ceD0k) (DListOK_append (DListOK_of ceD0l)
        (DListOK_append (DListOK_of ceD0m) (DListOK_of ceD0n)))))))))))))
    · exact fun e he hek => Or.inr (Or.inl
        (CFSG.KS.HNLocal.cenVAt_sound (k := 4) (n := 10) consts hPC (by norm_num)
          (by norm_num) ce1 e he hek))
    · exact fun e he hek => Or.inr (Or.inl
        (CFSG.KS.HNLocal.cenVAt_sound (k := 4) (n := 10) consts hPC (by norm_num)
          (by norm_num) ce2 e he hek))
    · exact fun e he hek => Or.inr (Or.inl
        (CFSG.KS.HNLocal.cenVAt_sound (k := 4) (n := 10) consts hPC (by norm_num)
          (by norm_num) ce3 e he hek))
    · exact block_DL (by norm_num) ceV4 (DListOK_append (DListOK_of ceD4a)
        (DListOK_append (DListOK_of ceD4b) (DListOK_of ceD4c)))
    · exact block_DL (by norm_num) ceV5 (DListOK_append (DListOK_of ceD5a) (DListOK_of ceD5b))
    · exact block_DL (by norm_num) ceV6 (DListOK_append (DListOK_of ceD6a) (DListOK_of ceD6b))
    · exact fun e he hek => Or.inr (Or.inl
        (CFSG.KS.HNLocal.cenVAt_sound (k := 4) (n := 10) consts hPC (by norm_num)
          (by norm_num) ce7 e he hek))
    · exact block_DL (by norm_num) ceV8 (DListOK_append (DListOK_of ceD8a)
        (DListOK_append (DListOK_of ceD8b) (DListOK_of ceD8c)))
    · exact fun e he hek => Or.inr (Or.inl
        (CFSG.KS.HNLocal.cenVAt_sound (k := 4) (n := 10) consts hPC (by norm_num)
          (by norm_num) ce9 e he hek))
    · exact block_DL (by norm_num) ceV10 (DListOK_append (DListOK_of ceD10a) (DListOK_of ceD10b))
    · exact block_DL (by norm_num) ceV11 (DListOK_append (DListOK_of ceD11a) (DListOK_of ceD11b))
    · exact block_DL (by norm_num) ceV12 (DListOK_append (DListOK_of ceD12a)
        (DListOK_append (DListOK_of ceD12b) (DListOK_of ceD12c)))
    · exact block_DL (by norm_num) ceV13 (DListOK_append (DListOK_of ceD13a) (DListOK_of ceD13b))
    · exact fun e he hek => Or.inr (Or.inl
        (CFSG.KS.HNLocal.cenVAt_sound (k := 4) (n := 10) consts hPC (by norm_num)
          (by norm_num) ce14 e he hek))
    · exact block_DL (by norm_num) ceV15 (DListOK_append (DListOK_of ceD15a) (DListOK_of ceD15b))
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  have hm : e 0 + 2 * e 1 + 4 * e 2 + 8 * e 3 < 16 := by omega
  exact partner_lift (hc _ hm e he (fun i hi => by interval_cases i <;> omega))

theorem census : ∀ g ∈ QJ, g ^ 2 = 1 → g ≠ 1 →
    ∃ (i : Fin 2) (h : J Dt) (m : ℕ), m % 2 = 1 ∧ (g * (h * wG (12 + i.val) * h⁻¹)) ^ m = 1 := by
  intro g hg hg2 hg1
  obtain ⟨e, he, hge⟩ := Q2_normal.2 g.1 hg
  have hmat : mat Dt g = CFSG.KS.HNLocal.nfE PC 14 e := by
    rw [← nfProd_eq]; exact hge
  have hsq : mat Dt g * mat Dt g = 1 := by
    rw [← CertificateChecks.KernelHN.mat_mul', ← pow_two, hg2]
    rfl
  rcases census_nf e he with h1 | h2 | ⟨x, hx, a, ha, q, hq, hpow⟩
  · have e1 : mat Dt g = mat Dt 1 := by
      rw [hmat, h1]
      rfl
    exact absurd (mat_injective Dt e1) hg1
  · exact (h2 (by rw [← hmat]; exact hsq)).elim
  · obtain ⟨hR, hidx⟩ := mat_partner ha
    let y : J Dt := ⟨x, Q2_le hx⟩
    refine ⟨⟨pIdx a, hidx⟩, y * hP a, q, hq, mat_injective Dt ?_⟩
    have e2 : mat Dt (y * hP a * wG (12 + pIdx a) * (y * hP a)⁻¹) =
        mat Dt y * mat Dt (hP a * wG (12 + pIdx a) * (hP a)⁻¹) * mat Dt y⁻¹ := by
      rw [mul_inv_rev, ← mul_assoc, ← CertificateChecks.KernelHN.mat_mul',
        ← CertificateChecks.KernelHN.mat_mul']
      simp only [mul_assoc]
    have e1 : mat Dt ((g * (y * hP a * wG (12 + pIdx a) * (y * hP a)⁻¹)) ^ q) =
        (mat Dt g * mat Dt (y * hP a * wG (12 + pIdx a) * (y * hP a)⁻¹)) ^ q := by
      rw [CertificateChecks.KernelHN.mat_pow', CertificateChecks.KernelHN.mat_mul']
    rw [e1, e2, ← hR, hmat]
    exact hpow

end CertificateChecks.KernelHNLocal

end
