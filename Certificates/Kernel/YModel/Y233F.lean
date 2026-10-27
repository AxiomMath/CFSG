module

public import CFSG.YGroups.Model233FInputs
public import Certificates.Kernel.YModel.Basic
public import CFSG.Certificates.Kernel.YModel.Y233F.Data
import CFSG.Certificates.Kernel.YModel.Y233F.CheckL
import CFSG.Certificates.Kernel.YModel.Y233F.CheckR

public section

namespace CertificateChecks.KernelYModel

open CFSG.KC.YModel
open CFSG.YGroups

set_option maxRecDepth 100000

theorem y233F_arrays_eq : y233FArrays = linesA (fun _ => 3510) 32 (CFSG.KD.YM233F.F) 9 := by
  have h := decBind_perms CFSG.KD.YM233F.ok
  rw [← charsOf_eq, ← CFSG.KD.YM233F.eq] at h
  rw [y233FArrays, h]
  change linesA (lget CFSG.KD.YM233F.El) 32 (CFSG.KD.YM233F.F) 9 = _
  apply linesA_congr
  intro L hL
  interval_cases L
  exacts [Nat.eq_of_beq_eq_true CFSG.KD.YMY233F.e0, Nat.eq_of_beq_eq_true CFSG.KD.YMY233F.e1, Nat.eq_of_beq_eq_true CFSG.KD.YMY233F.e2, Nat.eq_of_beq_eq_true CFSG.KD.YMY233F.e3, Nat.eq_of_beq_eq_true CFSG.KD.YMY233F.e4, Nat.eq_of_beq_eq_true CFSG.KD.YMY233F.e5, Nat.eq_of_beq_eq_true CFSG.KD.YMY233F.e6, Nat.eq_of_beq_eq_true CFSG.KD.YMY233F.e7, Nat.eq_of_beq_eq_true CFSG.KD.YMY233F.e8]

theorem y233F_let : ∀ c < 9, letOK 12 3510 ((CFSG.KD.YM233F.F) c) (CFSG.KD.YMY233F.Nf c) = true := by
  intro c hc
  interval_cases c
  exacts [CFSG.KD.YMY233F.l0, CFSG.KD.YMY233F.l1, CFSG.KD.YMY233F.l2, CFSG.KD.YMY233F.l3, CFSG.KD.YMY233F.l4, CFSG.KD.YMY233F.l5, CFSG.KD.YMY233F.l6, CFSG.KD.YMY233F.l7, CFSG.KD.YMY233F.l8]

theorem y233F_rels : relsOK 12 9 CFSG.KD.YMY233F.Nf (yRels 2 3 3) = true := by
  have e : yRels 2 3 3 = CFSG.KD.YMY233F.rels := by decide +kernel
  rw [e]
  apply relsOK_of_weqK
  apply forall_mem_of_lgetL
  intro i hi
  change i < 46 at hi
  interval_cases i
  exacts [CFSG.KD.YMY233F.r0, CFSG.KD.YMY233F.r1, CFSG.KD.YMY233F.r2, CFSG.KD.YMY233F.r3, CFSG.KD.YMY233F.r4, CFSG.KD.YMY233F.r5, CFSG.KD.YMY233F.r6, CFSG.KD.YMY233F.r7, CFSG.KD.YMY233F.r8, CFSG.KD.YMY233F.r9, CFSG.KD.YMY233F.r10, CFSG.KD.YMY233F.r11, CFSG.KD.YMY233F.r12, CFSG.KD.YMY233F.r13, CFSG.KD.YMY233F.r14, CFSG.KD.YMY233F.r15, CFSG.KD.YMY233F.r16, CFSG.KD.YMY233F.r17, CFSG.KD.YMY233F.r18, CFSG.KD.YMY233F.r19, CFSG.KD.YMY233F.r20, CFSG.KD.YMY233F.r21, CFSG.KD.YMY233F.r22, CFSG.KD.YMY233F.r23, CFSG.KD.YMY233F.r24, CFSG.KD.YMY233F.r25, CFSG.KD.YMY233F.r26, CFSG.KD.YMY233F.r27, CFSG.KD.YMY233F.r28, CFSG.KD.YMY233F.r29, CFSG.KD.YMY233F.r30, CFSG.KD.YMY233F.r31, CFSG.KD.YMY233F.r32, CFSG.KD.YMY233F.r33, CFSG.KD.YMY233F.r34, CFSG.KD.YMY233F.r35, CFSG.KD.YMY233F.r36, CFSG.KD.YMY233F.r37, CFSG.KD.YMY233F.r38, CFSG.KD.YMY233F.r39, CFSG.KD.YMY233F.r40, CFSG.KD.YMY233F.r41, CFSG.KD.YMY233F.r42, CFSG.KD.YMY233F.r43, CFSG.KD.YMY233F.r44, CFSG.KD.YMY233F.r45]

theorem y233F_perms : ModelNative.permsOK 3510 y233FArrays = true := by
  rw [y233F_arrays_eq]
  exact permsOK_of_letOK y233F_let

theorem y233F_relators : ModelNative.relatorsOK 3510 y233FArrays (yRels 2 3 3) = true := by
  rw [y233F_arrays_eq]
  exact relatorsOK_of_relsOK y233F_let y233F_rels

theorem y233F_size : y233FArrays.size = 9 := by
  rw [y233F_arrays_eq, size_linesA]

end CertificateChecks.KernelYModel

end
