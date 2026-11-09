module

public import Certificates.Kernel.OmegaEight.N3PW
public import CFSG.Certificates.Kernel.O8N3Sound
public import Certificates.Kernel.OmegaEight.PnSWEq
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.O8CommUnitSound
import CFSG.Certificates.Kernel.O8CentOrbSound
import CFSG.Certificates.Kernel.O8ColFixSound
import CFSG.Certificates.Kernel.O8ParFixSound
import Certificates.Kernel.OmegaEight.N3PCentS2
public import CFSG.Certificates.Kernel.O8MinusSound
public import CFSG.Certificates.Kernel.O8NodeSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split
  CFSG.EvenSmallLie.OmegaEight.N3Split.PlusW

set_option maxHeartbeats 0 in
theorem s2_okN3P : s2Chk wN3P = true := by
  have hS : sortedK (decE EnN3PS2.D EnN3PS2.m).keys = true := (Enum.of_enumOK s2E_okN3P).2.1
  have hM : sortedK (decE EnN3PM2.D EnN3PM2.m).keys = true := (Enum.of_enumOK m2E_okN3P).2.1
  simp only [s2Chk, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, s2E_okN3P⟩, ?_⟩, ?_⟩, ?_⟩, m2E_okN3P⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [gensOK, N3Split.Plus.s2Gens, N3Split.Plus.sGens0, slpGens, runK_eq, fpowK_eq,
      invPair, mulK_eq, idK_eq, ← Array.all_toList, N3Split.Plus.base, N3Split.Plus.cGens,
      N3Split.Plus.tGens, splitCGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [wN3P, decE_keys_size]
    decide +kernel
  · simp only [wN3P, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList,
      N3Split.Plus.tGens, splitTGens, kronK_eq]
    quickRfl
  · rw [classCertW, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp only [mulK_sq_bne (j := 10) (by norm_num)]
      simp only [wN3P, decE_getD, decE_keys_size, mulK_eq, idK_eq, fixLB_eq_P]
      refine all_range_of_blocks (m := EnN3PS2.m) (s := 9) (nb := 64) (by decide +kernel)
        fun b hb => ?_
      interval_cases b <;> decide +kernel
    · rw [List.all_eq_true]
      intro r hr
      simp only [N3Split.Plus.s2Reps, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
      refine ⟨?_, ?_⟩
      · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;>
          (simp only [wN3P, memK_decE_eq hS (by decide +kernel)]; quickRfl)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · right
        decide +kernel
      · left
        have hc := mulK_comm_grp (r := 11151734559601905357258116650136646539321349)
          [(0, 4), (1, 8), (4, 80), (5, 160), (6, 80), (7, 160), (8, 1024), (9, 2048)]
          [(2, 1), (3, 4096), (4, 4722366764344621924352), (5, 19342814266755571402145792),
          (6, 4722366764344621924352), (7, 19342814266755571402145792),
          (10, 79228162514264337593543950336), (11, 324518553658426726783156020576256)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 80]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 1 []) (centKsN3P.getD 1 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_eighty_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734559601906904909931568249302799130629)
          [(0, 4), (1, 8), (5, 240), (7, 240), (8, 1024), (9, 2048)]
          [(2, 1), (3, 4096), (4, 19342814266755571402145792), (5, 19342814266755571402145792),
          (6, 19342814266755571402145792), (7, 19342814266755571402145792),
          (10, 79228162514264337593543950336), (11, 324518553658426726783156020576256)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 2 []) (centKsN3P.getD 2 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151733894906777826385573516678082064294145)
          [(0, 256), (1, 512), (2, 1024), (3, 2048), (4, 80), (5, 160), (6, 80), (7, 160)]
          [(4, 4722366764344621924352), (5, 19342814266755571402145792),
          (6, 4722366764344621924352), (7, 19342814266755571402145792), (8, 1), (9, 4096),
          (10, 16777216), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 80]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 3 []) (centKsN3P.getD 3 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_eighty_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151733894906779374037388434790738324103425)
          [(0, 256), (1, 512), (2, 1024), (3, 2048), (5, 240), (7, 240)]
          [(4, 19342814266755571402145792), (5, 19342814266755571402145792),
          (6, 19342814266755571402145792), (7, 19342814266755571402145792), (8, 1), (9, 4096),
          (10, 16777216), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 4 []) (centKsN3P.getD 4 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294909815367779787098715966955525)
          [(0, 4), (1, 196), (4, 80), (5, 3152), (6, 80), (7, 80), (8, 1024), (9, 1024)]
          [(2, 4097), (4, 19347536633519916024070144), (6, 19347536633519916024074240), (7, 4096),
          (10, 324597781820942144042254171373568), (11, 1152921504606846976)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 5 []) (centKsN3P.getD 5 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734559601906904909931568319688728421637)
          [(0, 1284), (1, 1288), (2, 1024), (3, 1024), (5, 240), (7, 240), (8, 1024), (9, 2048)]
          [(2, 1), (3, 4096), (4, 19342814266755571402145792), (5, 19342814266755571402145792),
          (6, 19342814266755571402145792), (7, 19342814266755571402145792), (8, 4097),
          (10, 79228162514264337662280208385), (11, 324518553658426726783156020576256)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 6 []) (centKsN3P.getD 6 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151733894906779374037683654757910835110145)
          [(0, 256), (1, 512), (2, 1088), (3, 2112), (4, 256), (5, 496), (7, 240)]
          [(4, 19342814266755571402145792), (5, 19342814266755571402145792),
          (6, 19342814266755640138399744), (7, 19342814266755571402145792),
          (8, 1153202979583557633), (9, 4096), (10, 16777216), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 7 []) (centKsN3P.getD 7 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294906411029148424325636143736069)
          [(0, 1284), (1, 1540), (2, 1024), (3, 2048), (4, 80), (5, 160), (6, 80), (7, 160),
          (8, 1024), (9, 1024)]
          [(2, 4097), (4, 4722366764344621924352), (5, 19342814266755571402145792),
          (6, 4722366764344621924352), (7, 19342814266755571402145792), (8, 1), (9, 4096),
          (10, 324597781820940991120749581307905), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 8 []) (centKsN3P.getD 8 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294907958680963342438292403545349)
          [(0, 1284), (1, 1540), (2, 1024), (3, 2048), (5, 240), (7, 240), (8, 1024), (9, 1024)]
          [(2, 4097), (4, 19342814266755571402145792), (5, 19342814266755571402145792),
          (6, 19342814266755571402145792), (7, 19342814266755571402145792), (8, 1), (9, 4096),
          (10, 324597781820940991120749581307905), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 9 []) (centKsN3P.getD 9 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294949434283559894335688186422357)
          [(0, 1108), (1, 2212), (4, 1104), (5, 2128), (6, 1104), (7, 2128), (8, 1024), (9, 1024)]
          [(2, 4097), (4, 19347536633519916024070145), (5, 4096), (6, 19347536633519916024070145),
          (7, 4096), (10, 324597781825663357885094186450945), (11, 19342814266755571402149888)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 10 []) (centKsN3P.getD 10 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151733894906799185914901159184746976453969)
          [(0, 1360), (1, 1616), (2, 1024), (3, 2048), (4, 1024), (5, 1264), (6, 1024), (7, 1264)]
          [(4, 19342814266755571402149889), (5, 19342814266755571402145792),
          (6, 19342814266755571402149889), (7, 19342814266755571402145792), (8, 1), (9, 4096),
          (10, 19347536633519916040851457), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 11 []) (centKsN3P.getD 11 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294907958680963342508643964706821)
          [(0, 4), (1, 772), (3, 3072), (5, 240), (7, 240), (8, 1024), (9, 1024)]
          [(2, 4097), (4, 19342814266755571402145792), (5, 19342814266755571402145792),
          (6, 19342814266755571402145792), (7, 19342814266755571402145792), (8, 4096), (9, 4096),
          (10, 324597781820940991120818284003328), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 12 []) (centKsN3P.getD 12 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151733894906784327006766615912335867388161)
          [(0, 256), (1, 512), (2, 1360), (3, 2384), (4, 256), (5, 496), (6, 256), (7, 496)]
          [(4, 19342814266755640138399744), (5, 19342814266755571402145792),
          (6, 19342814266755640138399744), (7, 19342814266755571402145792),
          (8, 19347536633519984760324097), (9, 4096), (10, 16777216), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 13 []) (centKsN3P.getD 13 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294919720095249362658623532326981)
          [(0, 68), (1, 68), (2, 336), (3, 672), (4, 1360), (5, 1616), (6, 336), (7, 592),
          (8, 1024), (9, 1024)]
          [(2, 4097), (4, 19347536633519916040847360), (5, 68719476736),
          (6, 19347536633519916040851457), (7, 68719476736), (8, 4722366764344638701568),
          (9, 19342814266755640121622528), (10, 324597781820942144323729148084224)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 14 []) (centKsN3P.getD 14 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294909815365123455965295930269701)
          [(0, 4), (1, 4), (3, 192), (4, 80), (5, 848), (6, 80), (7, 80), (8, 1024), (9, 1024)]
          [(2, 4097), (4, 19347536633519916024070144), (6, 19347536633519984743546880),
          (7, 68719476736), (8, 1152921504606846976), (9, 1152921504606846976),
          (10, 324597781820940991120749564526592)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 15 []) (centKsN3P.getD 15 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294909815364238012377318406776069)
          [(0, 1284), (1, 1540), (2, 1024), (3, 2048), (4, 80), (5, 80), (6, 80), (7, 80),
          (8, 1024), (9, 1024)]
          [(2, 4097), (4, 19347536633519916024070144), (6, 19347536633519916024070144), (8, 1),
          (9, 4096), (10, 324597781820940991120749581307905), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 16 []) (centKsN3P.getD 16 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151733894906779374038569314641831887380801)
          [(0, 320), (1, 576), (2, 1024), (3, 2048), (4, 1024), (5, 1264), (7, 240)]
          [(4, 19342814266755571402145792), (5, 19342814266755571402145792),
          (6, 19342814266755571402149889), (7, 19342814266755571402145792), (8, 1), (9, 4096),
          (10, 1153202979600334848), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3P (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3P.getD 17 []) (centKsN3P.getD 17 [])
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3P, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3P, decE_keys_size]; decide +kernel)
  · simp only [wN3P, decE_keys_size]
    decide +kernel
  · simp only [wN3P, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wN3P, memK_decE_eq hM (by decide +kernel)]
    quickRfl

end CertificateChecks.KernelO8
