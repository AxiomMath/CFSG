module

public import CFSG.YGroups.Exact.Y432Inputs
public import CFSG.YGroups.Model432FInputs
public import Certificates.Kernel.YModel.Basic
public import CFSG.Certificates.Kernel.YModel.Y432.Data
import CFSG.Certificates.Kernel.YModel.Y432.CheckL
import CFSG.Certificates.Kernel.YModel.Y432.CheckR
import CFSG.Certificates.Kernel.YModel.Y432.CheckW
import CFSG.Certificates.Kernel.YModel.Y432.CheckC

public section

namespace CertificateChecks.KernelYModel

open CFSG.KC.YModel
open CFSG.YGroups

set_option maxRecDepth 100000

theorem y432_arrays_eq : y432Arrays = linesA (fun _ => 31673) 32 (fun c => signExt 31671 (CFSG.KD.YM432P.F c)) 10 := by
  have h := decBind_perms CFSG.KD.YM432P.ok
  rw [← charsOf_eq, ← CFSG.KD.YM432P.eq] at h
  rw [y432Arrays, h]
  change ModelNative.withSign (linesA (lget CFSG.KD.YM432P.El) 32 (CFSG.KD.YM432P.F) 10) = _
  rw [linesA_congr (n' := fun _ => 31671) (fun L hL => by
    interval_cases L
    exacts [Nat.eq_of_beq_eq_true CFSG.KD.YMY432.e0, Nat.eq_of_beq_eq_true CFSG.KD.YMY432.e1, Nat.eq_of_beq_eq_true CFSG.KD.YMY432.e2, Nat.eq_of_beq_eq_true CFSG.KD.YMY432.e3, Nat.eq_of_beq_eq_true CFSG.KD.YMY432.e4, Nat.eq_of_beq_eq_true CFSG.KD.YMY432.e5, Nat.eq_of_beq_eq_true CFSG.KD.YMY432.e6, Nat.eq_of_beq_eq_true CFSG.KD.YMY432.e7, Nat.eq_of_beq_eq_true CFSG.KD.YMY432.e8, Nat.eq_of_beq_eq_true CFSG.KD.YMY432.e9])]
  refine withSign_linesA (n := 31671) (m := 10) (fun c hc => ?_) (by norm_num)
  interval_cases c
  exacts [lt_of_blt CFSG.KD.YMY432.h0, lt_of_blt CFSG.KD.YMY432.h1, lt_of_blt CFSG.KD.YMY432.h2, lt_of_blt CFSG.KD.YMY432.h3, lt_of_blt CFSG.KD.YMY432.h4, lt_of_blt CFSG.KD.YMY432.h5, lt_of_blt CFSG.KD.YMY432.h6, lt_of_blt CFSG.KD.YMY432.h7, lt_of_blt CFSG.KD.YMY432.h8, lt_of_blt CFSG.KD.YMY432.h9]

theorem y432_let : ∀ c < 10, letOK 15 31673 ((fun c => signExt 31671 (CFSG.KD.YM432P.F c)) c) (CFSG.KD.YMY432.Nf c) = true := by
  intro c hc
  interval_cases c
  exacts [CFSG.KD.YMY432.l0, CFSG.KD.YMY432.l1, CFSG.KD.YMY432.l2, CFSG.KD.YMY432.l3, CFSG.KD.YMY432.l4, CFSG.KD.YMY432.l5, CFSG.KD.YMY432.l6, CFSG.KD.YMY432.l7, CFSG.KD.YMY432.l8, CFSG.KD.YMY432.l9]

theorem y432_rels : relsOK 15 10 CFSG.KD.YMY432.Nf (yRels 4 3 2) = true := by
  have e : yRels 4 3 2 = CFSG.KD.YMY432.rels := by decide +kernel
  rw [e]
  apply relsOK_of_weqK
  apply forall_mem_of_lgetL
  intro i hi
  change i < 56 at hi
  interval_cases i
  exacts [CFSG.KD.YMY432.r0, CFSG.KD.YMY432.r1, CFSG.KD.YMY432.r2, CFSG.KD.YMY432.r3, CFSG.KD.YMY432.r4, CFSG.KD.YMY432.r5, CFSG.KD.YMY432.r6, CFSG.KD.YMY432.r7, CFSG.KD.YMY432.r8, CFSG.KD.YMY432.r9, CFSG.KD.YMY432.r10, CFSG.KD.YMY432.r11, CFSG.KD.YMY432.r12, CFSG.KD.YMY432.r13, CFSG.KD.YMY432.r14, CFSG.KD.YMY432.r15, CFSG.KD.YMY432.r16, CFSG.KD.YMY432.r17, CFSG.KD.YMY432.r18, CFSG.KD.YMY432.r19, CFSG.KD.YMY432.r20, CFSG.KD.YMY432.r21, CFSG.KD.YMY432.r22, CFSG.KD.YMY432.r23, CFSG.KD.YMY432.r24, CFSG.KD.YMY432.r25, CFSG.KD.YMY432.r26, CFSG.KD.YMY432.r27, CFSG.KD.YMY432.r28, CFSG.KD.YMY432.r29, CFSG.KD.YMY432.r30, CFSG.KD.YMY432.r31, CFSG.KD.YMY432.r32, CFSG.KD.YMY432.r33, CFSG.KD.YMY432.r34, CFSG.KD.YMY432.r35, CFSG.KD.YMY432.r36, CFSG.KD.YMY432.r37, CFSG.KD.YMY432.r38, CFSG.KD.YMY432.r39, CFSG.KD.YMY432.r40, CFSG.KD.YMY432.r41, CFSG.KD.YMY432.r42, CFSG.KD.YMY432.r43, CFSG.KD.YMY432.r44, CFSG.KD.YMY432.r45, CFSG.KD.YMY432.r46, CFSG.KD.YMY432.r47, CFSG.KD.YMY432.r48, CFSG.KD.YMY432.r49, CFSG.KD.YMY432.r50, CFSG.KD.YMY432.r51, CFSG.KD.YMY432.r52, CFSG.KD.YMY432.r53, CFSG.KD.YMY432.r54, CFSG.KD.YMY432.r55]

theorem y432_perms : ModelNative.permsOK 31673 y432Arrays = true := by
  rw [y432_arrays_eq]
  exact permsOK_of_letOK y432_let

theorem y432_relators : ModelNative.relatorsOK 31673 y432Arrays (yRels 4 3 2) = true := by
  rw [y432_arrays_eq]
  exact relatorsOK_of_relsOK y432_let y432_rels

theorem y432_size : y432Arrays.size = 10 := by
  rw [y432_arrays_eq, size_linesA]

theorem y432_w_falt : CFSG.Monster.B.Co2.Native.eqA 31673 (ModelNative.evalW 31673 y432Arrays (F432Word))
    (ModelNative.evalW 31673 y432Arrays (F432AltWord)) = true := by
  rw [y432_arrays_eq, eqA_of_weqK _ _ y432_let]
  exact CFSG.KD.YMY432.w_falt

theorem y432_w_fne : CFSG.Monster.B.Co2.Native.eqA 31673 (ModelNative.evalW 31673 y432Arrays (F432Word))
    (ModelNative.evalW 31673 y432Arrays ([])) = false := by
  rw [y432_arrays_eq, eqA_of_weqK _ _ y432_let]
  have h := CFSG.KD.YMY432.w_fne
  simp only [Bool.not_eq_true'] at h
  exact h

theorem y432_W0 : y432Words = linesW (fun L => CFSG.KD.YMY432.WL0 (L - 1)) 32
    (fun L => CFSG.KD.YMY432.WP0 (L - 1)) (16 + 1) := by
  have h := (decBind_chain (by decide) CFSG.KD.YM432C.ok).2
  rw [← charsOf_eq, ← CFSG.KD.YM432C.eq] at h
  rw [y432Words, h]
  rfl

theorem y432_base0 : y432Base = unpackA 10 32 (CFSG.KD.YM432C.F 0) := by
  have h := (decBind_chain (by decide) CFSG.KD.YM432C.ok).1
  rw [← charsOf_eq, ← CFSG.KD.YM432C.eq] at h
  rw [y432Base, h]
  rfl

theorem y432_chain0 : ModelNative.chainOK 31673 y432Arrays y432Words y432Base = true ∧
    ModelNative.chainSizes 31673 y432Arrays y432Words y432Base = [2, 31671, 28160, 3159, 288, 35, 12, 3, 2, 2] := by
  have h := chainOK_of_checks (m := 10) (nw := 16) (T := CFSG.KD.YMY432.T0) (R := CFSG.KD.YMY432.R0) (M := CFSG.KD.YMY432.M0)
    (Z := CFSG.KD.YMY432.Z0) (w := 32) (WP := CFSG.KD.YMY432.WP0) (WL := CFSG.KD.YMY432.WL0)
    (fun c hc => y432_let c (by omega)) y432_W0 y432_base0
    (by intro c hc; interval_cases c <;> rfl)
    (by
      intro i hi
      interval_cases i
      exacts [CFSG.KD.YMY432.c0_w0, CFSG.KD.YMY432.c0_w1, CFSG.KD.YMY432.c0_w2, CFSG.KD.YMY432.c0_w3, CFSG.KD.YMY432.c0_w4, CFSG.KD.YMY432.c0_w5, CFSG.KD.YMY432.c0_w6, CFSG.KD.YMY432.c0_w7, CFSG.KD.YMY432.c0_w8, CFSG.KD.YMY432.c0_w9, CFSG.KD.YMY432.c0_w10, CFSG.KD.YMY432.c0_w11, CFSG.KD.YMY432.c0_w12, CFSG.KD.YMY432.c0_w13, CFSG.KD.YMY432.c0_w14, CFSG.KD.YMY432.c0_w15])
    (by
      intro i hi
      interval_cases i
      exacts [CFSG.KD.YMY432.c0_l0, CFSG.KD.YMY432.c0_l1, CFSG.KD.YMY432.c0_l2, CFSG.KD.YMY432.c0_l3, CFSG.KD.YMY432.c0_l4, CFSG.KD.YMY432.c0_l5, CFSG.KD.YMY432.c0_l6, CFSG.KD.YMY432.c0_l7, CFSG.KD.YMY432.c0_l8, CFSG.KD.YMY432.c0_l9])
  rw [y432_arrays_eq]
  exact ⟨h.1, h.2.trans rfl⟩

end CertificateChecks.KernelYModel

end
