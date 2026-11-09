module

public import Certificates.Kernel.OmegaEight.N3MW
public import CFSG.Certificates.Kernel.O8N3Sound
public import Certificates.Kernel.OmegaEight.PnSWEq
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.O8CommUnitSound
import CFSG.Certificates.Kernel.O8CentOrbSound
import CFSG.Certificates.Kernel.O8ColFixSound
import CFSG.Certificates.Kernel.O8ParFixSound
import Certificates.Kernel.OmegaEight.N3MCentS2
public import CFSG.Certificates.Kernel.O8MinusSound
public import CFSG.Certificates.Kernel.O8NodeSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split
  CFSG.EvenSmallLie.OmegaEight.N3Split.MinusW

set_option maxHeartbeats 0 in
theorem s2_okN3M : s2Chk wN3M = true := by
  have hS : sortedK (decE EnN3MS2.D EnN3MS2.m).keys = true := (Enum.of_enumOK s2E_okN3M).2.1
  have hM : sortedK (decE EnN3MM2.D EnN3MM2.m).keys = true := (Enum.of_enumOK m2E_okN3M).2.1
  simp only [s2Chk, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, s2E_okN3M⟩, ?_⟩, ?_⟩, ?_⟩, m2E_okN3M⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [gensOK, N3Split.Minus.s2Gens, N3Split.Minus.sGens0, slpGens, runK_eq, fpowK_eq,
      invPair, mulK_eq, idK_eq, ← Array.all_toList, N3Split.Minus.base, N3Split.Minus.cGens,
      N3Split.Minus.tGens, splitCGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [wN3M, decE_keys_size]
    decide +kernel
  · simp only [wN3M, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList,
      N3Split.Minus.tGens, splitTGens, kronK_eq]
    quickRfl
  · rw [classCertW, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp only [mulK_sq_bne (j := 10) (by norm_num)]
      simp only [wN3M, decE_getD, decE_keys_size, mulK_eq, idK_eq, fixLB_eq_P]
      refine all_range_of_blocks (m := EnN3MS2.m) (s := 9) (nb := 64) (by decide +kernel)
        fun b hb => ?_
      interval_cases b <;> decide +kernel
    · rw [List.all_eq_true]
      intro r hr
      simp only [N3Split.Minus.s2Reps, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
      refine ⟨?_, ?_⟩
      · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;>
          (simp only [wN3M, memK_decE_eq hS (by decide +kernel)]; quickRfl)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · right
        decide +kernel
      · left
        have hc := mulK_comm_grp (r := 11151733894906779683522342933917984429711617)
          [(0, 256), (1, 512), (2, 1024), (3, 2048), (4, 64), (5, 128)]
          [(6, 281474976710656), (7, 1152921504606846976), (8, 1), (9, 4096), (10, 16777216),
          (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 16]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 1 []) (centKsN3M.getD 1 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_sixteen_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151733894906779683522269146941689591505153)
          [(0, 256), (1, 512), (2, 1024), (3, 2048), (4, 64), (5, 64)]
          [(6, 1153202979583557632), (8, 1), (9, 4096), (10, 16777216), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 2 []) (centKsN3M.getD 2 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734559601907214394886067376548904738821)
          [(0, 4), (1, 8), (4, 64), (5, 128), (8, 1024), (9, 2048)]
          [(2, 1), (3, 4096), (6, 281474976710656), (7, 1152921504606846976),
          (10, 79228162514264337593543950336), (11, 324518553658426726783156020576256)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 16]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 3 []) (centKsN3M.getD 3 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_sixteen_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734559601907214394812280400254066532357)
          [(0, 4), (1, 8), (4, 64), (5, 64), (8, 1024), (9, 2048)]
          [(2, 1), (3, 4096), (6, 1153202979583557632), (10, 79228162514264337593543950336),
          (11, 324518553658426726783156020576256)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 4 []) (centKsN3M.getD 4 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151733894906779683523597582730974325908801)
          [(0, 1344), (1, 1600), (2, 1024), (3, 2048), (4, 1024), (5, 1216)]
          [(6, 1152921504606851073), (7, 1152921504606846976), (8, 1), (9, 4096),
          (10, 1153202979600338945), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 5 []) (centKsN3M.getD 5 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151733894906779683522711922864649750454529)
          [(0, 256), (1, 512), (2, 1344), (3, 2368), (4, 256), (5, 448)]
          [(6, 1152921573343100928), (7, 1152921504606846976), (8, 1153203048319811585), (9, 4096),
          (10, 16777216), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 6 []) (centKsN3M.getD 6 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734559601907214394812280541008745243909)
          [(0, 1284), (1, 2568), (2, 1024), (3, 2048), (4, 64), (5, 64), (8, 1024), (9, 2048)]
          [(2, 1), (3, 4096), (6, 1153202979583557632), (8, 1), (9, 4096),
          (10, 79228162514264337593560727553), (11, 324518553658426726783224740057088)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 7 []) (centKsN3M.getD 7 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151733894906784636491499664034305790714113)
          [(0, 256), (1, 512), (2, 1296), (3, 2320), (5, 192), (6, 256), (7, 256)]
          [(4, 68736253952), (6, 1152921504606846976), (7, 1152921504606846976),
          (8, 19347535480317005176766465), (9, 4096), (10, 16777216), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 8 []) (centKsN3M.getD 8 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294908268165917841565538509153541)
          [(0, 1284), (1, 1540), (2, 1024), (3, 2048), (4, 64), (5, 128), (8, 1024), (9, 1024)]
          [(2, 4097), (6, 281474976710656), (7, 1152921504606846976), (8, 1), (9, 4096),
          (10, 324597781820940991120749581307905), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 9 []) (centKsN3M.getD 9 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294947887083099685060571467768853)
          [(0, 1044), (1, 2084), (2, 320), (3, 320), (4, 320), (5, 320), (6, 1024), (7, 2048),
          (8, 1024), (9, 1024)]
          [(2, 4097), (4, 1), (5, 4096), (6, 1153203048319811584), (8, 1153203048319811584),
          (10, 324597781825663357603619209740289), (11, 19342813113834066795302912)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 10 []) (centKsN3M.getD 10 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294908268166729498229997752573957)
          [(0, 4), (1, 4), (3, 960), (4, 64), (5, 832), (8, 1024), (9, 1024)]
          [(2, 4097), (6, 1153203048303034368), (7, 68719476736), (8, 1152921573326323712),
          (9, 1152921573326323712), (10, 324597781820940991120749564526592)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 11 []) (centKsN3M.getD 11 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294908268165991610527434837878021)
          [(0, 1284), (1, 1540), (2, 1024), (3, 2048), (5, 192), (8, 1024), (9, 1024)]
          [(2, 4097), (6, 1152921504606846976), (7, 1152921504606846976), (8, 1), (9, 4096),
          (10, 324597781820940991120749581307905), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 12 []) (centKsN3M.getD 12 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294908268168205525920299979662405)
          [(0, 1092), (1, 2180), (4, 1088), (5, 2112), (8, 1024), (9, 1024)]
          [(2, 4097), (6, 1153202979583557633), (7, 4096), (10, 324597781820940991402224541237249),
          (11, 1152921504606851072)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 13 []) (centKsN3M.getD 13 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294923123446315479067862878937093)
          [(0, 4), (1, 4), (3, 816), (4, 64), (5, 64), (7, 768), (8, 1024), (9, 1024)]
          [(2, 4097), (4, 68719476736), (5, 68719476736), (6, 1153202979583557632),
          (8, 19342813113834135514775552), (9, 19342813113834135514775552),
          (10, 324597781820940991120749564526592)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 14 []) (centKsN3M.getD 14 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294908268165844054589243670947077)
          [(0, 1284), (1, 1540), (2, 1024), (3, 2048), (4, 64), (5, 64), (8, 1024), (9, 1024)]
          [(2, 4097), (6, 1153202979583557632), (8, 1), (9, 4096),
          (10, 324597781820940991120749581307905), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 15 []) (centKsN3M.getD 15 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151734227294908268165991610597786399039493)
          [(0, 4), (1, 772), (3, 3072), (5, 192), (8, 1024), (9, 1024)]
          [(2, 4097), (6, 1152921504606846976), (7, 1152921504606846976), (8, 4096), (9, 4096),
          (10, 324597781820940991120818284003328), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 16 []) (centKsN3M.getD 16 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        have hc := mulK_comm_grp (r := 11151733894906799495398748547422795847509265)
          [(0, 1296), (1, 1552), (2, 1024), (3, 2048), (5, 192), (6, 1024), (7, 1024)]
          [(4, 4097), (6, 1152921504606846976), (7, 1152921504606846976), (8, 1), (9, 4096),
          (10, 19347535480316936457293825), (11, 68719476736)]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        exact candB_false_of_cent s2E_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTsN3M.getD 17 []) (centKsN3M.getD 17 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [hc, wN3M, decE_getD, decE_keys_size, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
  · simp only [wN3M, decE_keys_size]
    decide +kernel
  · simp only [wN3M, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wN3M, memK_decE_eq hM (by decide +kernel)]
    quickRfl

end CertificateChecks.KernelO8
