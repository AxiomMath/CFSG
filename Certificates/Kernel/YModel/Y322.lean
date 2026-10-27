module

public import CFSG.YGroups.Y322CentralInputs
public import Certificates.Kernel.YModel.Basic
public import CFSG.Certificates.Kernel.YModel.Y322.Data
import CFSG.Certificates.Kernel.YModel.Y322.CheckL
import CFSG.Certificates.Kernel.YModel.Y322.CheckR
import CFSG.Certificates.Kernel.YModel.Y322.CheckW
import CFSG.Certificates.Kernel.YModel.Y322.CheckC

public section

namespace CertificateChecks.KernelYModel

open CFSG.KC.YModel
open CFSG.YGroups

set_option maxRecDepth 100000

theorem y322_arrays_eq : y322Arrays = linesA (fun _ => 728) 32 (CFSG.KD.YM322P.F) 8 := by
  have h := decBind_perms CFSG.KD.YM322P.ok
  rw [← charsOf_eq, ← CFSG.KD.YM322P.eq] at h
  rw [y322Arrays, h]
  change linesA (lget CFSG.KD.YM322P.El) 32 (CFSG.KD.YM322P.F) 8 = _
  apply linesA_congr
  intro L hL
  interval_cases L
  exacts [Nat.eq_of_beq_eq_true CFSG.KD.YMY322.e0, Nat.eq_of_beq_eq_true CFSG.KD.YMY322.e1, Nat.eq_of_beq_eq_true CFSG.KD.YMY322.e2, Nat.eq_of_beq_eq_true CFSG.KD.YMY322.e3, Nat.eq_of_beq_eq_true CFSG.KD.YMY322.e4, Nat.eq_of_beq_eq_true CFSG.KD.YMY322.e5, Nat.eq_of_beq_eq_true CFSG.KD.YMY322.e6, Nat.eq_of_beq_eq_true CFSG.KD.YMY322.e7]

theorem y322_let : ∀ c < 8, letOK 10 728 ((CFSG.KD.YM322P.F) c) (CFSG.KD.YMY322.Nf c) = true := by
  intro c hc
  interval_cases c
  exacts [CFSG.KD.YMY322.l0, CFSG.KD.YMY322.l1, CFSG.KD.YMY322.l2, CFSG.KD.YMY322.l3, CFSG.KD.YMY322.l4, CFSG.KD.YMY322.l5, CFSG.KD.YMY322.l6, CFSG.KD.YMY322.l7]

theorem y322_rels : relsOK 10 8 CFSG.KD.YMY322.Nf (yRels 3 2 2) = true := by
  have e : yRels 3 2 2 = CFSG.KD.YMY322.rels := by decide +kernel
  rw [e]
  apply relsOK_of_weqK
  apply forall_mem_of_lgetL
  intro i hi
  change i < 37 at hi
  interval_cases i
  exacts [CFSG.KD.YMY322.r0, CFSG.KD.YMY322.r1, CFSG.KD.YMY322.r2, CFSG.KD.YMY322.r3, CFSG.KD.YMY322.r4, CFSG.KD.YMY322.r5, CFSG.KD.YMY322.r6, CFSG.KD.YMY322.r7, CFSG.KD.YMY322.r8, CFSG.KD.YMY322.r9, CFSG.KD.YMY322.r10, CFSG.KD.YMY322.r11, CFSG.KD.YMY322.r12, CFSG.KD.YMY322.r13, CFSG.KD.YMY322.r14, CFSG.KD.YMY322.r15, CFSG.KD.YMY322.r16, CFSG.KD.YMY322.r17, CFSG.KD.YMY322.r18, CFSG.KD.YMY322.r19, CFSG.KD.YMY322.r20, CFSG.KD.YMY322.r21, CFSG.KD.YMY322.r22, CFSG.KD.YMY322.r23, CFSG.KD.YMY322.r24, CFSG.KD.YMY322.r25, CFSG.KD.YMY322.r26, CFSG.KD.YMY322.r27, CFSG.KD.YMY322.r28, CFSG.KD.YMY322.r29, CFSG.KD.YMY322.r30, CFSG.KD.YMY322.r31, CFSG.KD.YMY322.r32, CFSG.KD.YMY322.r33, CFSG.KD.YMY322.r34, CFSG.KD.YMY322.r35, CFSG.KD.YMY322.r36]

theorem y322_perms : ModelNative.permsOK 728 y322Arrays = true := by
  rw [y322_arrays_eq]
  exact permsOK_of_letOK y322_let

theorem y322_relators : ModelNative.relatorsOK 728 y322Arrays (yRels 3 2 2) = true := by
  rw [y322_arrays_eq]
  exact relatorsOK_of_relsOK y322_let y322_rels

theorem y322_size : y322Arrays.size = 8 := by
  rw [y322_arrays_eq, size_linesA]

theorem y322_w_f12 : CFSG.Monster.B.Co2.Native.eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1))
    (ModelNative.evalW 728 y322Arrays (y322WordF2)) = true := by
  rw [y322_arrays_eq, eqA_of_weqK _ _ y322_let]
  exact CFSG.KD.YMY322.w_f12

theorem y322_w_fc0 : CFSG.Monster.B.Co2.Native.eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ [0]))
    (ModelNative.evalW 728 y322Arrays (0 :: y322WordF1)) = true := by
  rw [y322_arrays_eq, eqA_of_weqK _ _ y322_let]
  exact CFSG.KD.YMY322.w_fc0

theorem y322_w_fc1 : CFSG.Monster.B.Co2.Native.eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ [1]))
    (ModelNative.evalW 728 y322Arrays (1 :: y322WordF1)) = true := by
  rw [y322_arrays_eq, eqA_of_weqK _ _ y322_let]
  exact CFSG.KD.YMY322.w_fc1

theorem y322_w_fc2 : CFSG.Monster.B.Co2.Native.eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ [2]))
    (ModelNative.evalW 728 y322Arrays (2 :: y322WordF1)) = true := by
  rw [y322_arrays_eq, eqA_of_weqK _ _ y322_let]
  exact CFSG.KD.YMY322.w_fc2

theorem y322_w_fc3 : CFSG.Monster.B.Co2.Native.eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ [3]))
    (ModelNative.evalW 728 y322Arrays (3 :: y322WordF1)) = true := by
  rw [y322_arrays_eq, eqA_of_weqK _ _ y322_let]
  exact CFSG.KD.YMY322.w_fc3

theorem y322_w_fc4 : CFSG.Monster.B.Co2.Native.eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ [4]))
    (ModelNative.evalW 728 y322Arrays (4 :: y322WordF1)) = true := by
  rw [y322_arrays_eq, eqA_of_weqK _ _ y322_let]
  exact CFSG.KD.YMY322.w_fc4

theorem y322_w_fc5 : CFSG.Monster.B.Co2.Native.eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ [5]))
    (ModelNative.evalW 728 y322Arrays (5 :: y322WordF1)) = true := by
  rw [y322_arrays_eq, eqA_of_weqK _ _ y322_let]
  exact CFSG.KD.YMY322.w_fc5

theorem y322_w_fc6 : CFSG.Monster.B.Co2.Native.eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ [6]))
    (ModelNative.evalW 728 y322Arrays (6 :: y322WordF1)) = true := by
  rw [y322_arrays_eq, eqA_of_weqK _ _ y322_let]
  exact CFSG.KD.YMY322.w_fc6

theorem y322_w_fc7 : CFSG.Monster.B.Co2.Native.eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ [7]))
    (ModelNative.evalW 728 y322Arrays (7 :: y322WordF1)) = true := by
  rw [y322_arrays_eq, eqA_of_weqK _ _ y322_let]
  exact CFSG.KD.YMY322.w_fc7

theorem y322_w_ff : CFSG.Monster.B.Co2.Native.eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ y322WordF1))
    (ModelNative.evalW 728 y322Arrays ([])) = true := by
  rw [y322_arrays_eq, eqA_of_weqK _ _ y322_let]
  exact CFSG.KD.YMY322.w_ff

theorem y322_W0 : y322Words = linesW (fun L => CFSG.KD.YMY322.WL0 (L - 1)) 32
    (fun L => CFSG.KD.YMY322.WP0 (L - 1)) (0 + 1) := by
  have h := (decBind_chain (by decide) CFSG.KD.YM322C.ok).2
  rw [← charsOf_eq, ← CFSG.KD.YM322C.eq] at h
  rw [y322Words, h]
  rfl

theorem y322_base0 : y322Base = unpackA 7 32 (CFSG.KD.YM322C.F 0) := by
  have h := (decBind_chain (by decide) CFSG.KD.YM322C.ok).1
  rw [← charsOf_eq, ← CFSG.KD.YM322C.eq] at h
  rw [y322Base, h]
  rfl

theorem y322_chain0 : ModelNative.chainOK 728 y322Arrays y322Words y322Base = true ∧
    ModelNative.chainSizes 728 y322Arrays y322Words y322Base = [728, 243, 72, 20, 9, 2, 2] := by
  have h := chainOK_of_checks (m := 8) (nw := 0) (T := CFSG.KD.YMY322.T0) (R := CFSG.KD.YMY322.R0) (M := CFSG.KD.YMY322.M0)
    (Z := CFSG.KD.YMY322.Z0) (w := 32) (WP := CFSG.KD.YMY322.WP0) (WL := CFSG.KD.YMY322.WL0)
    (fun c hc => y322_let c (by omega)) y322_W0 y322_base0
    (by intro c hc; interval_cases c <;> rfl)
    (by intro i hi; omega)
    (by
      intro i hi
      interval_cases i
      exacts [CFSG.KD.YMY322.c0_l0, CFSG.KD.YMY322.c0_l1, CFSG.KD.YMY322.c0_l2, CFSG.KD.YMY322.c0_l3, CFSG.KD.YMY322.c0_l4, CFSG.KD.YMY322.c0_l5, CFSG.KD.YMY322.c0_l6])
  rw [y322_arrays_eq]
  exact ⟨h.1, h.2.trans rfl⟩


theorem y322_y322HSubArrays_eq : y322HSubArrays = linesA (fun _ => 728) 32 (CFSG.KD.YM322P.F) 7 := by
  rw [y322HSubArrays, y322_arrays_eq, extract_linesA (by decide)]

theorem y322_chain1 : ModelNative.chainOK 728 y322HSubArrays #[] #[0, 1, 2, 3, 4, 5] = true ∧
    ModelNative.chainSizes 728 y322HSubArrays #[] #[0, 1, 2, 3, 4, 5] = [56, 27, 16, 10, 6, 2] := by
  have h := chainOK_of_checks (m := 7) (nw := 0) (T := CFSG.KD.YMY322.T1) (R := CFSG.KD.YMY322.R1) (M := CFSG.KD.YMY322.M1)
    (Z := CFSG.KD.YMY322.Z1) (w := 32) (WP := CFSG.KD.YMY322.WP1) (WL := CFSG.KD.YMY322.WL1)
    (fun c hc => y322_let c (by omega)) (rfl : (#[] : Array (List Int)) = linesW (fun L => CFSG.KD.YMY322.WL1 (L - 1)) 32 (fun L => CFSG.KD.YMY322.WP1 (L - 1)) (0 + 1)) (by decide +kernel : (#[0, 1, 2, 3, 4, 5] : Array Nat) = unpackA 6 32 CFSG.KD.YMY322.B1)
    (by intro c hc; interval_cases c <;> rfl)
    (by intro i hi; omega)
    (by
      intro i hi
      interval_cases i
      exacts [CFSG.KD.YMY322.c1_l0, CFSG.KD.YMY322.c1_l1, CFSG.KD.YMY322.c1_l2, CFSG.KD.YMY322.c1_l3, CFSG.KD.YMY322.c1_l4, CFSG.KD.YMY322.c1_l5])
  rw [y322_y322HSubArrays_eq]
  exact ⟨h.1, h.2.trans rfl⟩

end CertificateChecks.KernelYModel

end
