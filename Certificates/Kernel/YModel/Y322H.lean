module

public import CFSG.YGroups.Y322CentralInputs
public import Certificates.Kernel.YModel.Basic
public import CFSG.Certificates.Kernel.YModel.Y322H.Data
import CFSG.Certificates.Kernel.YModel.Y322H.CheckL
import CFSG.Certificates.Kernel.YModel.Y322H.CheckR
import CFSG.Certificates.Kernel.YModel.Y322H.CheckC
import CFSG.Certificates.Kernel.YModel.Y322H.CheckX

public section

namespace CertificateChecks.KernelYModel

open CFSG.KC.YModel
open CFSG.YGroups

set_option maxRecDepth 100000

theorem y322H_arrays_eq : y322HActArrays = linesA (fun _ => 3159) 32 (CFSG.KD.YM322H.F) 8 := by
  have h := decBind_perms CFSG.KD.YM322H.ok
  rw [← charsOf_eq, ← CFSG.KD.YM322H.eq] at h
  rw [y322HActArrays, h]
  change linesA (lget CFSG.KD.YM322H.El) 32 (CFSG.KD.YM322H.F) 8 = _
  apply linesA_congr
  intro L hL
  interval_cases L
  exacts [Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.e0, Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.e1, Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.e2, Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.e3, Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.e4, Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.e5, Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.e6, Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.e7]

theorem y322H_let : ∀ c < 8, letOK 12 3159 ((CFSG.KD.YM322H.F) c) (CFSG.KD.YMY322H.Nf c) = true := by
  intro c hc
  interval_cases c
  exacts [CFSG.KD.YMY322H.l0, CFSG.KD.YMY322H.l1, CFSG.KD.YMY322H.l2, CFSG.KD.YMY322H.l3, CFSG.KD.YMY322H.l4, CFSG.KD.YMY322H.l5, CFSG.KD.YMY322H.l6, CFSG.KD.YMY322H.l7]

theorem y322H_rels : relsOK 12 8 CFSG.KD.YMY322H.Nf (yRels 3 2 2) = true := by
  have e : yRels 3 2 2 = CFSG.KD.YMY322H.rels := by decide +kernel
  rw [e]
  apply relsOK_of_weqK
  apply forall_mem_of_lgetL
  intro i hi
  change i < 37 at hi
  interval_cases i
  exacts [CFSG.KD.YMY322H.r0, CFSG.KD.YMY322H.r1, CFSG.KD.YMY322H.r2, CFSG.KD.YMY322H.r3, CFSG.KD.YMY322H.r4, CFSG.KD.YMY322H.r5, CFSG.KD.YMY322H.r6, CFSG.KD.YMY322H.r7, CFSG.KD.YMY322H.r8, CFSG.KD.YMY322H.r9, CFSG.KD.YMY322H.r10, CFSG.KD.YMY322H.r11, CFSG.KD.YMY322H.r12, CFSG.KD.YMY322H.r13, CFSG.KD.YMY322H.r14, CFSG.KD.YMY322H.r15, CFSG.KD.YMY322H.r16, CFSG.KD.YMY322H.r17, CFSG.KD.YMY322H.r18, CFSG.KD.YMY322H.r19, CFSG.KD.YMY322H.r20, CFSG.KD.YMY322H.r21, CFSG.KD.YMY322H.r22, CFSG.KD.YMY322H.r23, CFSG.KD.YMY322H.r24, CFSG.KD.YMY322H.r25, CFSG.KD.YMY322H.r26, CFSG.KD.YMY322H.r27, CFSG.KD.YMY322H.r28, CFSG.KD.YMY322H.r29, CFSG.KD.YMY322H.r30, CFSG.KD.YMY322H.r31, CFSG.KD.YMY322H.r32, CFSG.KD.YMY322H.r33, CFSG.KD.YMY322H.r34, CFSG.KD.YMY322H.r35, CFSG.KD.YMY322H.r36]

theorem y322H_perms : ModelNative.permsOK 3159 y322HActArrays = true := by
  rw [y322H_arrays_eq]
  exact permsOK_of_letOK y322H_let

theorem y322H_relators : ModelNative.relatorsOK 3159 y322HActArrays (yRels 3 2 2) = true := by
  rw [y322H_arrays_eq]
  exact relatorsOK_of_relsOK y322H_let y322H_rels

theorem y322H_size : y322HActArrays.size = 8 := by
  rw [y322H_arrays_eq, size_linesA]


theorem y322H_chain0 : ModelNative.chainOK 3159 y322HActArrays #[] #[0, 1, 2, 3, 4, 5, 6] = true ∧
    ModelNative.chainSizes 3159 y322HActArrays #[] #[0, 1, 2, 3, 4, 5, 6] = [3159, 288, 35, 12, 3, 2, 2] := by
  have h := chainOK_of_checks (m := 8) (nw := 0) (T := CFSG.KD.YMY322H.T0) (R := CFSG.KD.YMY322H.R0) (M := CFSG.KD.YMY322H.M0)
    (Z := CFSG.KD.YMY322H.Z0) (w := 32) (WP := CFSG.KD.YMY322H.WP0) (WL := CFSG.KD.YMY322H.WL0)
    (fun c hc => y322H_let c (by omega)) (rfl : (#[] : Array (List Int)) = linesW (fun L => CFSG.KD.YMY322H.WL0 (L - 1)) 32 (fun L => CFSG.KD.YMY322H.WP0 (L - 1)) (0 + 1)) (by decide +kernel : (#[0, 1, 2, 3, 4, 5, 6] : Array Nat) = unpackA 7 32 CFSG.KD.YMY322H.B0)
    (by intro c hc; interval_cases c <;> rfl)
    (by intro i hi; omega)
    (by
      intro i hi
      interval_cases i
      exacts [CFSG.KD.YMY322H.c0_l0, CFSG.KD.YMY322H.c0_l1, CFSG.KD.YMY322H.c0_l2, CFSG.KD.YMY322H.c0_l3, CFSG.KD.YMY322H.c0_l4, CFSG.KD.YMY322H.c0_l5, CFSG.KD.YMY322H.c0_l6])
  rw [y322H_arrays_eq]
  exact ⟨h.1, h.2.trans rfl⟩

theorem y322H_fix0 : ∀ c < 7, (y322HActArrays[c]!)[0]! = 0 := by
  intro c hc
  rw [y322H_arrays_eq]
  interval_cases c
  all_goals rw [getElem!_linesA (by decide), getElem!_unpackA (by decide)]
  exacts [Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.x0, Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.x1, Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.x2, Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.x3, Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.x4, Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.x5, Nat.eq_of_beq_eq_true CFSG.KD.YMY322H.x6]

end CertificateChecks.KernelYModel

end
