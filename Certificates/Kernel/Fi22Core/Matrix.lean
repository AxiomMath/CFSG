module

public import Certificates.Kernel.Fi22Core.Data
public import CFSG.Certificates.Kernel.Spor.F3LaneSound
public import CFSG.Certificates.Kernel.Spor.F3R
public import CFSG.F3.ConjSpec
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22C

open CFSG.F3.Native CFSG.KS CFSG.KS.F3L CFSG.KS.F3R CFSG.KC.Enum CFSG.Sporadic.Fi22.Native

set_option Elab.async false

theorem seedA_ok : seedK (nat_lit 77) LA SeedA.chars = true := by quickRfl
theorem seedB_ok : seedK (nat_lit 77) LB SeedB.chars = true := by quickRfl

theorem canon_ok : bAnd(canonF LA, bAnd(canonF LB, bAnd(canonF LBi, bAnd(canonF LI,
    canonF (mulF LA LB))))) = true := by quickRfl

theorem id_ok : eqMK 77 (idM 77) (unlane 77 LI) = true := by decide +kernel

theorem a2_ok : eqF (mulF LA LA) LI = true := by quickRfl
theorem bi_ok : eqF (powF LB 12) LBi = true := by quickRfl
theorem bbi_ok : eqF (mulF LB LBi) LI = true := by quickRfl
theorem b13_ok : eqF (powF LB 13) LI = true := by quickRfl
theorem ab11_ok : eqF (powF (mulF LA LB) 11) LI = true := by quickRfl
theorem ne_ok : bAnd(Bool.not (eqF LA LI), bAnd(Bool.not (eqF LB LI), Bool.not (eqF (mulF LA LB) LI))) =
    true := by quickRfl

theorem eqF_iff {X Y : V} : eqF X Y = true ↔ X = Y := by
  unfold eqF
  rw [bAnd_iff, Nat.beq_eq, Nat.beq_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact V.ext' h1 h2
  · rintro rfl
    exact ⟨rfl, rfl⟩

structure Canon (X : V) : Prop where
  wf : X.wf = true
  p : X.p < 2 ^ (77 * 77)
  m : X.m < 2 ^ (77 * 77)

set_option exponentiation.threshold 6000 in
theorem canonF_spec {X : V} (h : canonF X = true) : Canon X := by
  unfold canonF at h
  rw [bAnd_iff, bAnd_iff, Nat.beq_eq, Nat.blt_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e : Nat.shiftLeft 1 5929 = 2 ^ (77 * 77) := Nat.one_shiftLeft (77 * 77)
  refine ⟨?_, lt_of_lt_of_eq h2 e, lt_of_lt_of_eq h3 e⟩
  unfold V.wf
  rw [beq_iff_eq]
  exact h1

theorem canons : Canon LA ∧ Canon LB ∧ Canon LBi ∧ Canon LI ∧ Canon (mulF LA LB) := by
  have h := canon_ok
  simp only [bAnd_iff] at h
  exact ⟨canonF_spec h.1, canonF_spec h.2.1, canonF_spec h.2.2.1, canonF_spec h.2.2.2.1,
    canonF_spec h.2.2.2.2⟩

theorem matA_eq : matA () = unlane 77 LA := by
  unfold matA
  rw [SeedA.eq]
  exact rowsOf_seed seedA_ok

theorem matB_eq : matB () = unlane 77 LB := by
  unfold matB
  rw [SeedB.eq]
  exact rowsOf_seed seedB_ok

theorem idM_eq : idM 77 = unlane 77 LI := by
  have h : eqM 77 (idM 77) (unlane 77 LI) = true := by rw [eqM_eq]; exact id_ok
  exact eq_of_canonM (canonM_idM 77) (canonM_unlane 77 canons.2.2.2.1.wf) (toMat_eq_of_eqM h)

theorem mul_eq' (X Y : V) : mul 77 (unlane 77 X) (unlane 77 Y) = unlane 77 (mulF X Y) :=
  mul_unlane (by norm_num) X Y

theorem powM_eq' (X : V) (e : Nat) : powM 77 (unlane 77 X) e = unlane 77 (powF X e) :=
  powM_unlane (by norm_num) idM_eq X e

theorem matBi_eq : matBi () = unlane 77 LBi := by
  unfold matBi
  rw [matB_eq, powM_eq', (eqF_iff.1 bi_ok)]

theorem unlane_size' (X : V) : (unlane 77 X).size = 77 := unlane_size 77 X

theorem ne_of_lane {X Y : V} (hX : Canon X) (hY : Canon Y) (h : X ≠ Y) :
    eqM 77 (unlane 77 X) (unlane 77 Y) = false := by
  cases e : eqM 77 (unlane 77 X) (unlane 77 Y)
  · rfl
  · exact absurd (eqM_unlane hX.wf hY.wf hX.p hX.m hY.p hY.m e) h

theorem matrix_ok : matrixChecks () = true := by
  obtain ⟨cA, cB, -, cI, cAB⟩ := canons
  have hne := ne_ok
  simp only [bAnd_iff] at hne
  obtain ⟨n1, n2, n3⟩ := hne
  rw [Bool.not_eq_true', ← Bool.not_eq_true, eqF_iff] at n1 n2 n3
  unfold matrixChecks
  rw [matA_eq, matB_eq, matBi_eq, idM_eq, mul_eq', mul_eq', mul_eq', powM_eq', powM_eq',
    eqF_iff.1 a2_ok, eqF_iff.1 bbi_ok, eqF_iff.1 b13_ok, eqF_iff.1 ab11_ok,
    canonM_unlane 77 cA.wf, canonM_unlane 77 cB.wf, canonM_unlane 77 cI.wf,
    canonM_unlane 77 cAB.wf, eqM_self (unlane_size' _), ne_of_lane cA cI n1, ne_of_lane cB cI n2,
    ne_of_lane cAB cI n3]
  rfl

end CertificateChecks.KernelFi22C

end
