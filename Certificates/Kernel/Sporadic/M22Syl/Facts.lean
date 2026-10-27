module

public import Certificates.Kernel.Sporadic.M22Syl.Surv0
public import Certificates.Kernel.Sporadic.M22Syl.Surv1
public import Certificates.Kernel.Sporadic.M22Syl.Surv2
public import Certificates.Kernel.Sporadic.M22Syl.Surv3
public import CFSG.Certificates.Kernel.Spor.MSylowSound
public import CFSG.Certificates.Kernel.Spor.MSylowSoundW
public import CFSG.Sporadic.Schreier.MathieuSylowAutM22Inputs
public import CFSG.Sporadic.Schreier.MathieuSylowAutM22Derivs
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M22
public meta import CFSG.Monster.B.Mathieu.M22Check
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.PCountW
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv

public section

namespace CertificateChecks.KernelSpor.M22Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PCnt CFSG.KS.MSyl CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.Certificates CFSG.Sporadic.Th.Native

set_option maxRecDepth 100000

@[expose] def z0 : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 5] * List.formPerm [2, 11] * List.formPerm [3, 15] * List.formPerm [4, 18] *
    List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [12, 21] *
    List.formPerm [19, 20]

theorem natTbl_z0 : natTbl 22 m22SylowZ = toTable z0 := by
  have h : ∀ i : Fin 22, UInt32.ofNat (m22SylowZ.getD i.val 0) = UInt32.ofNat (z0 i).val := by
    decide +kernel
  unfold natTbl toTable
  exact congrArg _ (funext h)

theorem pk_one : pkw 5 (1 : Equiv.Perm (Fin 22)) = I := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_a : pkw 5 m22gA = A := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_ai : pkw 5 m22gA⁻¹ = Ai := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_b : pkw 5 m22gB = B := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_bi : pkw 5 m22gB⁻¹ = Bi := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_z : pkw 5 z0 = Z := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_zi : pkw 5 z0⁻¹ = Zi := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_zb : pkw 5 (z0 * m22gB * z0⁻¹) = ZB := Nat.eq_of_beq_eq_true (by quickRfl)

@[expose] def lv : List (List (Equiv.Perm (Fin 22))) :=
  (List.finRange m22Certificate.baseCount).map (levelTransversals m22Certificate)

theorem lv_pk : (lv.map fun T => T.map (pkw 5)) = [L0, L1, L2, L3, L4] := by decide +kernel

theorem pt_eq : exprsV 22 5 (mask 5) I (slpP 22 5 (mask 5) I A Ai B Bi m22Derivs) ES = PT :=
  eq_of_beq pt

theorem len_L0 : L0.length = 22 := by decide +kernel

theorem cnt_zero {t : Nat} (ht : t ∈ L0) : cnt t = 0 := by
  have hc : ∀ k < 8, chunkOK k = true := by
    intro k hk
    interval_cases k
    exacts [c0, c1, c2, c3, c4, c5, c6, c7]
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  have hi' : i < 22 := len_L0 ▸ hi
  have h := (allL_iff _ _).1 (hc (i / 3) (by omega)) L0[i] (by
    rw [List.mem_take_iff_getElem]
    refine ⟨i % 3, ?_, ?_⟩
    · simp only [List.length_drop, len_L0]
      omega
    · simp only [List.getElem_drop]
      congr 1
      omega)
  exact Nat.eq_of_beq_eq_true h

theorem survF_zero : ∀ g ∈ enumeration m22Certificate,
    survF 22 5 (mask 5) I A Ai B ZB m22Derivs ES PT 11 6 4 (pkw 5 g) = 0 := by
  have hn32 : (22 : Nat) < 2 ^ 32 := by norm_num
  have hw : (22 : Nat) ≤ 2 ^ 5 := by norm_num
  obtain ⟨T0, T1, T2, T3, T4, hlv, h0, h1, h2, h3, h4⟩ : ∃ T0 T1 T2 T3 T4,
      lv = [T0, T1, T2, T3, T4] ∧ T0.map (pkw 5) = L0 ∧ T1.map (pkw 5) = L1 ∧
        T2.map (pkw 5) = L2 ∧ T3.map (pkw 5) = L3 ∧ T4.map (pkw 5) = L4 := by
    have h := lv_pk
    rcases hl : lv with _ | ⟨T0, _ | ⟨T1, _ | ⟨T2, _ | ⟨T3, _ | ⟨T4, _ | ⟨T5, rest⟩⟩⟩⟩⟩⟩ <;>
      rw [hl] at h <;> simp at h
    exact ⟨T0, T1, T2, T3, T4, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  intro g hg
  have hE : enumeration m22Certificate = products lv := rfl
  rw [hE, hlv, products, List.mem_flatMap] at hg
  obtain ⟨t, ht, hg⟩ := hg
  rw [List.mem_map] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  have hc := cnt_zero (t := pkw 5 t) (h0 ▸ List.mem_map_of_mem ht)
  have hsum := pcnt_pkw hw hn32 (survF 22 5 (mask 5) I A Ai B ZB m22Derivs ES PT 11 6 4)
    [[t], T1, T2, T3, T4] 1 0
  simp only [List.map_cons, List.map_nil, h1, h2, h3, h4, pk_one, one_mul, Nat.zero_add] at hsum
  rw [cnt] at hc
  rw [hc] at hsum
  have hz := List.sum_eq_zero_iff.1 hsum.symm
  refine hz _ (List.mem_map.2 ⟨t * h, ?_, rfl⟩)
  simp only [products, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map]
  exact ⟨h, hh, rfl⟩

theorem facts : (sylowAutOK 22 (toTable m22gA) (toTable m22gB) m22Derivs
      m22SylowExprs (natTbl 22 m22SylowZ) 150 443520 7 = true)
    ∧ (survivorsOK 22 (toTable m22gA) (toTable m22gB) (natTbl 22 m22SylowZ)
      m22Derivs m22SylowExprs 11 6 4 (orderTables m22Certificate 4) = true) := by
  have hn32 : (22 : Nat) < 2 ^ 32 := by norm_num
  have hw : (22 : Nat) ≤ 2 ^ 5 := by norm_num
  have hes : m22SylowExprs = ES := rfl
  rw [natTbl_z0, hes]
  refine ⟨sylowAutP_sound_w hn32 hw m22gA m22gB z0 m22Derivs ES 150 443520 7 ?_,
    survF_sound_w hn32 hw m22Certificate m22gA m22gB z0 m22Derivs ES (by norm_num) (by norm_num)
      (by norm_num) ?_⟩
  · rw [pk_one, pk_a, pk_ai, pk_b, pk_bi, pk_z, pk_zi]
    exact syl
  · rw [pk_one, pk_a, pk_ai, pk_b, pk_bi, pk_zb, pt_eq]
    exact survF_zero

end CertificateChecks.KernelSpor.M22Syl

end
