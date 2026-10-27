module

public import CFSG.YGroups.Model432FInputs
public import Certificates.Kernel.YModel.Basic
public import CFSG.Certificates.Kernel.YModel.Y432F.Data
import CFSG.Certificates.Kernel.YModel.Y432F.CheckL
import CFSG.Certificates.Kernel.YModel.Y432F.CheckR
import CFSG.Certificates.Kernel.YModel.Y432F.CheckW
import CFSG.Certificates.Kernel.YModel.Y432F.CheckC

public section

namespace CertificateChecks.KernelYModel

open CFSG.KC.YModel
open CFSG.YGroups

set_option maxRecDepth 100000

theorem y432F_arrays_eq : y432FArrays = linesA (fun _ => 31671) 32 (CFSG.KD.YM432P.F) 10 := by
  have h := decBind_perms CFSG.KD.YM432P.ok
  rw [← charsOf_eq, ← CFSG.KD.YM432P.eq] at h
  rw [y432FArrays, ModelNative.y432FPermText, h]
  change linesA (lget CFSG.KD.YM432P.El) 32 (CFSG.KD.YM432P.F) 10 = _
  apply linesA_congr
  intro L hL
  interval_cases L
  exacts [Nat.eq_of_beq_eq_true CFSG.KD.YMY432F.e0, Nat.eq_of_beq_eq_true CFSG.KD.YMY432F.e1, Nat.eq_of_beq_eq_true CFSG.KD.YMY432F.e2, Nat.eq_of_beq_eq_true CFSG.KD.YMY432F.e3, Nat.eq_of_beq_eq_true CFSG.KD.YMY432F.e4, Nat.eq_of_beq_eq_true CFSG.KD.YMY432F.e5, Nat.eq_of_beq_eq_true CFSG.KD.YMY432F.e6, Nat.eq_of_beq_eq_true CFSG.KD.YMY432F.e7, Nat.eq_of_beq_eq_true CFSG.KD.YMY432F.e8, Nat.eq_of_beq_eq_true CFSG.KD.YMY432F.e9]

theorem y432F_let : ∀ c < 10, letOK 15 31671 ((CFSG.KD.YM432P.F) c) (CFSG.KD.YMY432F.Nf c) = true := by
  intro c hc
  interval_cases c
  exacts [CFSG.KD.YMY432F.l0, CFSG.KD.YMY432F.l1, CFSG.KD.YMY432F.l2, CFSG.KD.YMY432F.l3, CFSG.KD.YMY432F.l4, CFSG.KD.YMY432F.l5, CFSG.KD.YMY432F.l6, CFSG.KD.YMY432F.l7, CFSG.KD.YMY432F.l8, CFSG.KD.YMY432F.l9]

theorem y432F_rels : relsOK 15 10 CFSG.KD.YMY432F.Nf (yRels 4 3 2) = true := by
  have e : yRels 4 3 2 = CFSG.KD.YMY432F.rels := by decide +kernel
  rw [e]
  apply relsOK_of_weqK
  apply forall_mem_of_lgetL
  intro i hi
  change i < 56 at hi
  interval_cases i
  exacts [CFSG.KD.YMY432F.r0, CFSG.KD.YMY432F.r1, CFSG.KD.YMY432F.r2, CFSG.KD.YMY432F.r3, CFSG.KD.YMY432F.r4, CFSG.KD.YMY432F.r5, CFSG.KD.YMY432F.r6, CFSG.KD.YMY432F.r7, CFSG.KD.YMY432F.r8, CFSG.KD.YMY432F.r9, CFSG.KD.YMY432F.r10, CFSG.KD.YMY432F.r11, CFSG.KD.YMY432F.r12, CFSG.KD.YMY432F.r13, CFSG.KD.YMY432F.r14, CFSG.KD.YMY432F.r15, CFSG.KD.YMY432F.r16, CFSG.KD.YMY432F.r17, CFSG.KD.YMY432F.r18, CFSG.KD.YMY432F.r19, CFSG.KD.YMY432F.r20, CFSG.KD.YMY432F.r21, CFSG.KD.YMY432F.r22, CFSG.KD.YMY432F.r23, CFSG.KD.YMY432F.r24, CFSG.KD.YMY432F.r25, CFSG.KD.YMY432F.r26, CFSG.KD.YMY432F.r27, CFSG.KD.YMY432F.r28, CFSG.KD.YMY432F.r29, CFSG.KD.YMY432F.r30, CFSG.KD.YMY432F.r31, CFSG.KD.YMY432F.r32, CFSG.KD.YMY432F.r33, CFSG.KD.YMY432F.r34, CFSG.KD.YMY432F.r35, CFSG.KD.YMY432F.r36, CFSG.KD.YMY432F.r37, CFSG.KD.YMY432F.r38, CFSG.KD.YMY432F.r39, CFSG.KD.YMY432F.r40, CFSG.KD.YMY432F.r41, CFSG.KD.YMY432F.r42, CFSG.KD.YMY432F.r43, CFSG.KD.YMY432F.r44, CFSG.KD.YMY432F.r45, CFSG.KD.YMY432F.r46, CFSG.KD.YMY432F.r47, CFSG.KD.YMY432F.r48, CFSG.KD.YMY432F.r49, CFSG.KD.YMY432F.r50, CFSG.KD.YMY432F.r51, CFSG.KD.YMY432F.r52, CFSG.KD.YMY432F.r53, CFSG.KD.YMY432F.r54, CFSG.KD.YMY432F.r55]

theorem y432F_perms : ModelNative.permsOK 31671 y432FArrays = true := by
  rw [y432F_arrays_eq]
  exact permsOK_of_letOK y432F_let

theorem y432F_relators : ModelNative.relatorsOK 31671 y432FArrays (yRels 4 3 2) = true := by
  rw [y432F_arrays_eq]
  exact relatorsOK_of_relsOK y432F_let y432F_rels

theorem y432F_size : y432FArrays.size = 10 := by
  rw [y432F_arrays_eq, size_linesA]

theorem y432F_w_fid : CFSG.Monster.B.Co2.Native.eqA 31671 (ModelNative.evalW 31671 y432FArrays (F432Word))
    (ModelNative.evalW 31671 y432FArrays ([])) = true := by
  rw [y432F_arrays_eq, eqA_of_weqK _ _ y432F_let]
  exact CFSG.KD.YMY432F.w_fid

theorem y432F_W0 : y432FWords = linesW (fun L => CFSG.KD.YMY432F.WL0 (L - 1)) 32
    (fun L => CFSG.KD.YMY432F.WP0 (L - 1)) (16 + 1) := by
  have h := (decBind_chain (by decide) CFSG.KD.YM432FC.ok).2
  rw [← charsOf_eq, ← CFSG.KD.YM432FC.eq] at h
  rw [y432FWords, h]
  rfl

theorem y432F_base0 : y432FBase = unpackA 9 32 (CFSG.KD.YM432FC.F 0) := by
  have h := (decBind_chain (by decide) CFSG.KD.YM432FC.ok).1
  rw [← charsOf_eq, ← CFSG.KD.YM432FC.eq] at h
  rw [y432FBase, h]
  rfl

theorem y432F_chain0 : ModelNative.chainOK 31671 y432FArrays y432FWords y432FBase = true ∧
    ModelNative.chainSizes 31671 y432FArrays y432FWords y432FBase = [31671, 28160, 3159, 288, 35, 12, 3, 2, 2] := by
  have h := chainOK_of_checks (m := 10) (nw := 16) (T := CFSG.KD.YMY432F.T0) (R := CFSG.KD.YMY432F.R0) (M := CFSG.KD.YMY432F.M0)
    (Z := CFSG.KD.YMY432F.Z0) (w := 32) (WP := CFSG.KD.YMY432F.WP0) (WL := CFSG.KD.YMY432F.WL0)
    (fun c hc => y432F_let c (by omega)) y432F_W0 y432F_base0
    (by intro c hc; interval_cases c <;> rfl)
    (by
      intro i hi
      interval_cases i
      exacts [CFSG.KD.YMY432F.c0_w0, CFSG.KD.YMY432F.c0_w1, CFSG.KD.YMY432F.c0_w2, CFSG.KD.YMY432F.c0_w3, CFSG.KD.YMY432F.c0_w4, CFSG.KD.YMY432F.c0_w5, CFSG.KD.YMY432F.c0_w6, CFSG.KD.YMY432F.c0_w7, CFSG.KD.YMY432F.c0_w8, CFSG.KD.YMY432F.c0_w9, CFSG.KD.YMY432F.c0_w10, CFSG.KD.YMY432F.c0_w11, CFSG.KD.YMY432F.c0_w12, CFSG.KD.YMY432F.c0_w13, CFSG.KD.YMY432F.c0_w14, CFSG.KD.YMY432F.c0_w15])
    (by
      intro i hi
      interval_cases i
      exacts [CFSG.KD.YMY432F.c0_l0, CFSG.KD.YMY432F.c0_l1, CFSG.KD.YMY432F.c0_l2, CFSG.KD.YMY432F.c0_l3, CFSG.KD.YMY432F.c0_l4, CFSG.KD.YMY432F.c0_l5, CFSG.KD.YMY432F.c0_l6, CFSG.KD.YMY432F.c0_l7, CFSG.KD.YMY432F.c0_l8])
  rw [y432F_arrays_eq]
  exact ⟨h.1, h.2.trans rfl⟩

end CertificateChecks.KernelYModel

end
