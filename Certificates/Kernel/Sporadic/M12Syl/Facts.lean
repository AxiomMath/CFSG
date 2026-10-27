module

public import Certificates.Kernel.Sporadic.M12Syl.Checks
public import CFSG.Certificates.Kernel.Spor.MSylowSound
public import CFSG.Sporadic.Schreier.MathieuSylowAutM12Inputs
public import CFSG.Sporadic.Schreier.MathieuSylowAutM12Derivs
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M12
public meta import CFSG.Sporadic.Schreier.M12Pinned
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv

public section

namespace CertificateChecks.KernelSpor.M12Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PCnt CFSG.KS.MSyl CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.Certificates CFSG.Sporadic.Th.Native

set_option maxRecDepth 100000

@[expose] def z0 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [1, 7] * List.formPerm [4, 10] * List.formPerm [6, 8]

theorem natTbl_z0 : natTbl 12 m12SylowZ = toTable z0 := by
  have h : ∀ i : Fin 12, UInt32.ofNat (m12SylowZ.getD i.val 0) = UInt32.ofNat (z0 i).val := by
    decide +kernel
  unfold natTbl toTable
  exact congrArg _ (funext h)

theorem pk_one : pk (1 : Equiv.Perm (Fin 12)) = I := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_a : pk m12gA = A := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_ai : pk m12gA⁻¹ = A := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_b : pk m12gB = B := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_bi : pk m12gB⁻¹ = Bi := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_z : pk z0 = Z := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_zi : pk z0⁻¹ = Z := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_zb : pk (z0 * m12gB * z0⁻¹) = ZB := Nat.eq_of_beq_eq_true (by quickRfl)

theorem exprs_eq : m12SylowExprs = ES := rfl

@[expose] def lv : List (List (Equiv.Perm (Fin 12))) :=
  (List.finRange m12Certificate.baseCount).map (levelTransversals m12Certificate)

theorem lv_pk : (lv.map fun T => T.map pk) = [L0, L1, L2, L3, L4] := by decide +kernel

theorem pt_eq : exprsV 12 4 (mask 4) I (slpP 12 4 (mask 4) I A A B Bi m12Derivs) ES = PT :=
  eq_of_beq pt

theorem cnt_zero {t : Nat} (ht : t ∈ L0) : cnt t = 0 := by
  have key : ∀ t ∈ L0, Nat.beq (cnt t) 0 = true := by
    rw [L0]
    simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    exact ⟨surv0, surv1, surv2, surv3, surv4, surv5, surv6, surv7, surv8, surv9, surv10, surv11⟩
  exact Nat.eq_of_beq_eq_true (key t ht)

theorem survF_zero : ∀ g ∈ enumeration m12Certificate,
    survF 12 4 (mask 4) I A A B ZB m12Derivs ES PT 11 6 3 (pk g) = 0 := by
  have hn : (12 : Nat) ≤ 16 := by norm_num
  obtain ⟨T0, T1, T2, T3, T4, hlv, h0, h1, h2, h3, h4⟩ : ∃ T0 T1 T2 T3 T4, lv = [T0, T1, T2, T3, T4] ∧
      T0.map pk = L0 ∧ T1.map pk = L1 ∧ T2.map pk = L2 ∧ T3.map pk = L3 ∧ T4.map pk = L4 := by
    have h := lv_pk
    rcases hl : lv with _ | ⟨T0, _ | ⟨T1, _ | ⟨T2, _ | ⟨T3, _ | ⟨T4, _ | ⟨T5, rest⟩⟩⟩⟩⟩⟩ <;>
      rw [hl] at h <;> simp at h
    exact ⟨T0, T1, T2, T3, T4, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  intro g hg
  have hE : enumeration m12Certificate = products lv := rfl
  rw [hE, hlv, products, List.mem_flatMap] at hg
  obtain ⟨t, ht, hg⟩ := hg
  rw [List.mem_map] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  have hc := cnt_zero (t := pk t) (h0 ▸ List.mem_map_of_mem ht)
  have hsum := pcnt_pk hn (survF 12 4 (mask 4) I A A B ZB m12Derivs ES PT 11 6 3)
    [[t], T1, T2, T3, T4] 1 0
  simp only [List.map_cons, List.map_nil, h1, h2, h3, h4, pk_one, one_mul, Nat.zero_add] at hsum
  rw [cnt] at hc
  rw [hc] at hsum
  have hz := List.sum_eq_zero_iff.1 hsum.symm
  refine hz _ (List.mem_map.2 ⟨t * h, ?_, rfl⟩)
  simp only [products, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map]
  exact ⟨h, hh, rfl⟩

theorem facts : (sylowAutOK 12 (toTable m12gA) (toTable m12gB) m12Derivs
      m12SylowExprs (natTbl 12 m12SylowZ) 80 95040 6 = true)
    ∧ (survivorsOK 12 (toTable m12gA) (toTable m12gB) (natTbl 12 m12SylowZ)
      m12Derivs m12SylowExprs 11 6 3 (orderTables m12Certificate 3) = true) := by
  have hn : (12 : Nat) ≤ 16 := by norm_num
  rw [natTbl_z0, exprs_eq]
  refine ⟨sylowAutP_sound hn m12gA m12gB z0 m12Derivs ES 80 95040 6 ?_,
    survF_sound hn m12Certificate m12gA m12gB z0 m12Derivs ES (by norm_num) (by norm_num)
      (by norm_num) ?_⟩
  · rw [pk_one, pk_a, pk_ai, pk_b, pk_bi, pk_z, pk_zi]
    exact syl
  · rw [pk_one, pk_a, pk_ai, pk_b, pk_bi, pk_zb, pt_eq]
    exact survF_zero

end CertificateChecks.KernelSpor.M12Syl

end
