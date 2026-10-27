module

public import Certificates.Kernel.YModel.Basic
public import CFSG.Certificates.Kernel.YModel.S233F.Data
import CFSG.Certificates.Kernel.YModel.S233F.CheckL
import CFSG.Certificates.Kernel.YModel.S233F.CheckG
import CFSG.Certificates.Kernel.YModel.S233F.CheckP
import CFSG.Certificates.Kernel.YModel.S233F.CheckT
import CFSG.Certificates.Kernel.YModel.S233F.CheckS0
import CFSG.Certificates.Kernel.YModel.S233F.CheckS1
import CFSG.Certificates.Kernel.YModel.S233F.CheckS2
import CFSG.Certificates.Kernel.YModel.S233F.CheckS3
import CFSG.Certificates.Kernel.YModel.S233F.CheckS4
import CFSG.Certificates.Kernel.YModel.S233F.CheckS5
import CFSG.Certificates.Kernel.YModel.S233F.CheckS6
import CFSG.Certificates.Kernel.YModel.S233F.CheckS7
import CFSG.Certificates.Kernel.YModel.S233F.CheckS8

public section

namespace CertificateChecks.KernelYModel

open CFSG.KC.YModel

set_option maxRecDepth 100000

theorem s233F_card : Nat.card (CFSG.YGroups.arrClosure 3510 (linesA (fun _ => 3510) 32 CFSG.KD.YMS233F.LF 9)) =
    64561751654400 := by
  have h := card_arrClosure_of_sch (k := 12) (n := 3510) (m := 9) (w := 8) (t := 7)
    (F := CFSG.KD.YMS233F.LF) (Nf := CFSG.KD.YMS233F.Nf) (U := CFSG.KD.YMS233F.U) (WP := CFSG.KD.YMS233F.GP) (WL := CFSG.KD.YMS233F.GL) (TT := CFSG.KD.YMS233F.TT)
    (off := CFSG.KC.YModel.lget [9, 12, 15, 19, 24, 29, 33, 36]) (bp := CFSG.KC.YModel.lget [0, 1, 2, 3, 5, 9, 12]) (Z := CFSG.KC.YModel.lget [3510, 2816, 567, 120, 24, 2, 2])
    (LP := CFSG.KC.YModel.lget [265451974305672421710364, 5384768576820354190727177154098537447417699525543466516, 320957218896979558741695676796273642866040642074, 96780020681246174854439264058203559514179493959188, 1099703661289854530530856782536736, 66, 20271291307386394995190834228507699691262176335893526, 87355372269390207969407020, 72]) (LL := CFSG.KC.YModel.lget [10, 23, 20, 21, 14, 1, 22, 11, 1])
    (by intro c hc; interval_cases c; exacts [CFSG.KD.YMS233F.l0, CFSG.KD.YMS233F.l1, CFSG.KD.YMS233F.l2, CFSG.KD.YMS233F.l3, CFSG.KD.YMS233F.l4, CFSG.KD.YMS233F.l5, CFSG.KD.YMS233F.l6, CFSG.KD.YMS233F.l7, CFSG.KD.YMS233F.l8])
    (by intro c hc; interval_cases c <;> rfl)
    rfl (by decide)
    (by
      intro j h1 h2
      change 9 ≤ j at h1
      change j < 12 at h2
      interval_cases j
      exacts [CFSG.KD.YMS233F.g9, CFSG.KD.YMS233F.g10, CFSG.KD.YMS233F.g11])
    (by
      intro i hi1 hi2
      interval_cases i
      · intro j h1 h2
        change 12 ≤ j at h1
        change j < 15 at h2
        interval_cases j
        exacts [CFSG.KD.YMS233F.g12, CFSG.KD.YMS233F.g13, CFSG.KD.YMS233F.g14]
      · intro j h1 h2
        change 15 ≤ j at h1
        change j < 19 at h2
        interval_cases j
        exacts [CFSG.KD.YMS233F.g15, CFSG.KD.YMS233F.g16, CFSG.KD.YMS233F.g17, CFSG.KD.YMS233F.g18]
      · intro j h1 h2
        change 19 ≤ j at h1
        change j < 24 at h2
        interval_cases j
        exacts [CFSG.KD.YMS233F.g19, CFSG.KD.YMS233F.g20, CFSG.KD.YMS233F.g21, CFSG.KD.YMS233F.g22, CFSG.KD.YMS233F.g23]
      · intro j h1 h2
        change 24 ≤ j at h1
        change j < 29 at h2
        interval_cases j
        exacts [CFSG.KD.YMS233F.g24, CFSG.KD.YMS233F.g25, CFSG.KD.YMS233F.g26, CFSG.KD.YMS233F.g27, CFSG.KD.YMS233F.g28]
      · intro j h1 h2
        change 29 ≤ j at h1
        change j < 33 at h2
        interval_cases j
        exacts [CFSG.KD.YMS233F.g29, CFSG.KD.YMS233F.g30, CFSG.KD.YMS233F.g31, CFSG.KD.YMS233F.g32]
      · intro j h1 h2
        change 33 ≤ j at h1
        change j < 36 at h2
        interval_cases j
        exacts [CFSG.KD.YMS233F.g33, CFSG.KD.YMS233F.g34, CFSG.KD.YMS233F.g35]
      )
    (by intro i hi; interval_cases i <;> decide)
    (by
      intro i hi
      interval_cases i
      exacts [⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS233F.b0, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS233F.b1, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS233F.b2, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS233F.b3, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS233F.b4, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS233F.b5, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS233F.b6, by decide⟩])
    (by intro i hi; interval_cases i; exacts [CFSG.KD.YMS233F.p0, CFSG.KD.YMS233F.p1, CFSG.KD.YMS233F.p2, CFSG.KD.YMS233F.p3, CFSG.KD.YMS233F.p4, CFSG.KD.YMS233F.p5, CFSG.KD.YMS233F.p6])
    (by
      intro i hi
      interval_cases i
      · intro a ha
        change a < 3510 at ha
        rcases Nat.lt_or_ge a 64 with h | h
        · exact transOK_point (a0 := 0) (cnt := 64) CFSG.KD.YMS233F.t0_0 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 128 with h | h
        · exact transOK_point (a0 := 64) (cnt := 64) CFSG.KD.YMS233F.t0_1 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 192 with h | h
        · exact transOK_point (a0 := 128) (cnt := 64) CFSG.KD.YMS233F.t0_2 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 256 with h | h
        · exact transOK_point (a0 := 192) (cnt := 64) CFSG.KD.YMS233F.t0_3 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 320 with h | h
        · exact transOK_point (a0 := 256) (cnt := 64) CFSG.KD.YMS233F.t0_4 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 384 with h | h
        · exact transOK_point (a0 := 320) (cnt := 64) CFSG.KD.YMS233F.t0_5 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 448 with h | h
        · exact transOK_point (a0 := 384) (cnt := 64) CFSG.KD.YMS233F.t0_6 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 512 with h | h
        · exact transOK_point (a0 := 448) (cnt := 64) CFSG.KD.YMS233F.t0_7 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 576 with h | h
        · exact transOK_point (a0 := 512) (cnt := 64) CFSG.KD.YMS233F.t0_8 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 640 with h | h
        · exact transOK_point (a0 := 576) (cnt := 64) CFSG.KD.YMS233F.t0_9 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 704 with h | h
        · exact transOK_point (a0 := 640) (cnt := 64) CFSG.KD.YMS233F.t0_10 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 768 with h | h
        · exact transOK_point (a0 := 704) (cnt := 64) CFSG.KD.YMS233F.t0_11 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 832 with h | h
        · exact transOK_point (a0 := 768) (cnt := 64) CFSG.KD.YMS233F.t0_12 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 896 with h | h
        · exact transOK_point (a0 := 832) (cnt := 64) CFSG.KD.YMS233F.t0_13 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 960 with h | h
        · exact transOK_point (a0 := 896) (cnt := 64) CFSG.KD.YMS233F.t0_14 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1024 with h | h
        · exact transOK_point (a0 := 960) (cnt := 64) CFSG.KD.YMS233F.t0_15 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1088 with h | h
        · exact transOK_point (a0 := 1024) (cnt := 64) CFSG.KD.YMS233F.t0_16 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1152 with h | h
        · exact transOK_point (a0 := 1088) (cnt := 64) CFSG.KD.YMS233F.t0_17 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1216 with h | h
        · exact transOK_point (a0 := 1152) (cnt := 64) CFSG.KD.YMS233F.t0_18 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1280 with h | h
        · exact transOK_point (a0 := 1216) (cnt := 64) CFSG.KD.YMS233F.t0_19 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1344 with h | h
        · exact transOK_point (a0 := 1280) (cnt := 64) CFSG.KD.YMS233F.t0_20 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1408 with h | h
        · exact transOK_point (a0 := 1344) (cnt := 64) CFSG.KD.YMS233F.t0_21 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1472 with h | h
        · exact transOK_point (a0 := 1408) (cnt := 64) CFSG.KD.YMS233F.t0_22 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1536 with h | h
        · exact transOK_point (a0 := 1472) (cnt := 64) CFSG.KD.YMS233F.t0_23 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1600 with h | h
        · exact transOK_point (a0 := 1536) (cnt := 64) CFSG.KD.YMS233F.t0_24 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1664 with h | h
        · exact transOK_point (a0 := 1600) (cnt := 64) CFSG.KD.YMS233F.t0_25 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1728 with h | h
        · exact transOK_point (a0 := 1664) (cnt := 64) CFSG.KD.YMS233F.t0_26 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1792 with h | h
        · exact transOK_point (a0 := 1728) (cnt := 64) CFSG.KD.YMS233F.t0_27 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1856 with h | h
        · exact transOK_point (a0 := 1792) (cnt := 64) CFSG.KD.YMS233F.t0_28 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1920 with h | h
        · exact transOK_point (a0 := 1856) (cnt := 64) CFSG.KD.YMS233F.t0_29 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1984 with h | h
        · exact transOK_point (a0 := 1920) (cnt := 64) CFSG.KD.YMS233F.t0_30 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2048 with h | h
        · exact transOK_point (a0 := 1984) (cnt := 64) CFSG.KD.YMS233F.t0_31 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2112 with h | h
        · exact transOK_point (a0 := 2048) (cnt := 64) CFSG.KD.YMS233F.t0_32 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2176 with h | h
        · exact transOK_point (a0 := 2112) (cnt := 64) CFSG.KD.YMS233F.t0_33 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2240 with h | h
        · exact transOK_point (a0 := 2176) (cnt := 64) CFSG.KD.YMS233F.t0_34 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2304 with h | h
        · exact transOK_point (a0 := 2240) (cnt := 64) CFSG.KD.YMS233F.t0_35 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2368 with h | h
        · exact transOK_point (a0 := 2304) (cnt := 64) CFSG.KD.YMS233F.t0_36 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2432 with h | h
        · exact transOK_point (a0 := 2368) (cnt := 64) CFSG.KD.YMS233F.t0_37 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2496 with h | h
        · exact transOK_point (a0 := 2432) (cnt := 64) CFSG.KD.YMS233F.t0_38 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2560 with h | h
        · exact transOK_point (a0 := 2496) (cnt := 64) CFSG.KD.YMS233F.t0_39 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2624 with h | h
        · exact transOK_point (a0 := 2560) (cnt := 64) CFSG.KD.YMS233F.t0_40 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2688 with h | h
        · exact transOK_point (a0 := 2624) (cnt := 64) CFSG.KD.YMS233F.t0_41 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2752 with h | h
        · exact transOK_point (a0 := 2688) (cnt := 64) CFSG.KD.YMS233F.t0_42 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2816 with h | h
        · exact transOK_point (a0 := 2752) (cnt := 64) CFSG.KD.YMS233F.t0_43 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2880 with h | h
        · exact transOK_point (a0 := 2816) (cnt := 64) CFSG.KD.YMS233F.t0_44 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2944 with h | h
        · exact transOK_point (a0 := 2880) (cnt := 64) CFSG.KD.YMS233F.t0_45 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 3008 with h | h
        · exact transOK_point (a0 := 2944) (cnt := 64) CFSG.KD.YMS233F.t0_46 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 3072 with h | h
        · exact transOK_point (a0 := 3008) (cnt := 64) CFSG.KD.YMS233F.t0_47 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 3136 with h | h
        · exact transOK_point (a0 := 3072) (cnt := 64) CFSG.KD.YMS233F.t0_48 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 3200 with h | h
        · exact transOK_point (a0 := 3136) (cnt := 64) CFSG.KD.YMS233F.t0_49 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 3264 with h | h
        · exact transOK_point (a0 := 3200) (cnt := 64) CFSG.KD.YMS233F.t0_50 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 3328 with h | h
        · exact transOK_point (a0 := 3264) (cnt := 64) CFSG.KD.YMS233F.t0_51 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 3392 with h | h
        · exact transOK_point (a0 := 3328) (cnt := 64) CFSG.KD.YMS233F.t0_52 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 3456 with h | h
        · exact transOK_point (a0 := 3392) (cnt := 64) CFSG.KD.YMS233F.t0_53 a (by omega) (by omega)
        exact transOK_point (a0 := 3456) (cnt := 54) CFSG.KD.YMS233F.t0_54 a (by omega) (by omega)
      · intro a ha
        change a < 2816 at ha
        rcases Nat.lt_or_ge a 64 with h | h
        · exact transOK_point (a0 := 0) (cnt := 64) CFSG.KD.YMS233F.t1_0 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 128 with h | h
        · exact transOK_point (a0 := 64) (cnt := 64) CFSG.KD.YMS233F.t1_1 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 192 with h | h
        · exact transOK_point (a0 := 128) (cnt := 64) CFSG.KD.YMS233F.t1_2 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 256 with h | h
        · exact transOK_point (a0 := 192) (cnt := 64) CFSG.KD.YMS233F.t1_3 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 320 with h | h
        · exact transOK_point (a0 := 256) (cnt := 64) CFSG.KD.YMS233F.t1_4 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 384 with h | h
        · exact transOK_point (a0 := 320) (cnt := 64) CFSG.KD.YMS233F.t1_5 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 448 with h | h
        · exact transOK_point (a0 := 384) (cnt := 64) CFSG.KD.YMS233F.t1_6 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 512 with h | h
        · exact transOK_point (a0 := 448) (cnt := 64) CFSG.KD.YMS233F.t1_7 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 576 with h | h
        · exact transOK_point (a0 := 512) (cnt := 64) CFSG.KD.YMS233F.t1_8 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 640 with h | h
        · exact transOK_point (a0 := 576) (cnt := 64) CFSG.KD.YMS233F.t1_9 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 704 with h | h
        · exact transOK_point (a0 := 640) (cnt := 64) CFSG.KD.YMS233F.t1_10 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 768 with h | h
        · exact transOK_point (a0 := 704) (cnt := 64) CFSG.KD.YMS233F.t1_11 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 832 with h | h
        · exact transOK_point (a0 := 768) (cnt := 64) CFSG.KD.YMS233F.t1_12 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 896 with h | h
        · exact transOK_point (a0 := 832) (cnt := 64) CFSG.KD.YMS233F.t1_13 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 960 with h | h
        · exact transOK_point (a0 := 896) (cnt := 64) CFSG.KD.YMS233F.t1_14 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1024 with h | h
        · exact transOK_point (a0 := 960) (cnt := 64) CFSG.KD.YMS233F.t1_15 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1088 with h | h
        · exact transOK_point (a0 := 1024) (cnt := 64) CFSG.KD.YMS233F.t1_16 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1152 with h | h
        · exact transOK_point (a0 := 1088) (cnt := 64) CFSG.KD.YMS233F.t1_17 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1216 with h | h
        · exact transOK_point (a0 := 1152) (cnt := 64) CFSG.KD.YMS233F.t1_18 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1280 with h | h
        · exact transOK_point (a0 := 1216) (cnt := 64) CFSG.KD.YMS233F.t1_19 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1344 with h | h
        · exact transOK_point (a0 := 1280) (cnt := 64) CFSG.KD.YMS233F.t1_20 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1408 with h | h
        · exact transOK_point (a0 := 1344) (cnt := 64) CFSG.KD.YMS233F.t1_21 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1472 with h | h
        · exact transOK_point (a0 := 1408) (cnt := 64) CFSG.KD.YMS233F.t1_22 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1536 with h | h
        · exact transOK_point (a0 := 1472) (cnt := 64) CFSG.KD.YMS233F.t1_23 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1600 with h | h
        · exact transOK_point (a0 := 1536) (cnt := 64) CFSG.KD.YMS233F.t1_24 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1664 with h | h
        · exact transOK_point (a0 := 1600) (cnt := 64) CFSG.KD.YMS233F.t1_25 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1728 with h | h
        · exact transOK_point (a0 := 1664) (cnt := 64) CFSG.KD.YMS233F.t1_26 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1792 with h | h
        · exact transOK_point (a0 := 1728) (cnt := 64) CFSG.KD.YMS233F.t1_27 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1856 with h | h
        · exact transOK_point (a0 := 1792) (cnt := 64) CFSG.KD.YMS233F.t1_28 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1920 with h | h
        · exact transOK_point (a0 := 1856) (cnt := 64) CFSG.KD.YMS233F.t1_29 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 1984 with h | h
        · exact transOK_point (a0 := 1920) (cnt := 64) CFSG.KD.YMS233F.t1_30 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2048 with h | h
        · exact transOK_point (a0 := 1984) (cnt := 64) CFSG.KD.YMS233F.t1_31 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2112 with h | h
        · exact transOK_point (a0 := 2048) (cnt := 64) CFSG.KD.YMS233F.t1_32 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2176 with h | h
        · exact transOK_point (a0 := 2112) (cnt := 64) CFSG.KD.YMS233F.t1_33 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2240 with h | h
        · exact transOK_point (a0 := 2176) (cnt := 64) CFSG.KD.YMS233F.t1_34 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2304 with h | h
        · exact transOK_point (a0 := 2240) (cnt := 64) CFSG.KD.YMS233F.t1_35 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2368 with h | h
        · exact transOK_point (a0 := 2304) (cnt := 64) CFSG.KD.YMS233F.t1_36 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2432 with h | h
        · exact transOK_point (a0 := 2368) (cnt := 64) CFSG.KD.YMS233F.t1_37 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2496 with h | h
        · exact transOK_point (a0 := 2432) (cnt := 64) CFSG.KD.YMS233F.t1_38 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2560 with h | h
        · exact transOK_point (a0 := 2496) (cnt := 64) CFSG.KD.YMS233F.t1_39 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2624 with h | h
        · exact transOK_point (a0 := 2560) (cnt := 64) CFSG.KD.YMS233F.t1_40 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2688 with h | h
        · exact transOK_point (a0 := 2624) (cnt := 64) CFSG.KD.YMS233F.t1_41 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 2752 with h | h
        · exact transOK_point (a0 := 2688) (cnt := 64) CFSG.KD.YMS233F.t1_42 a (by omega) (by omega)
        exact transOK_point (a0 := 2752) (cnt := 64) CFSG.KD.YMS233F.t1_43 a (by omega) (by omega)
      · intro a ha
        change a < 567 at ha
        rcases Nat.lt_or_ge a 64 with h | h
        · exact transOK_point (a0 := 0) (cnt := 64) CFSG.KD.YMS233F.t2_0 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 128 with h | h
        · exact transOK_point (a0 := 64) (cnt := 64) CFSG.KD.YMS233F.t2_1 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 192 with h | h
        · exact transOK_point (a0 := 128) (cnt := 64) CFSG.KD.YMS233F.t2_2 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 256 with h | h
        · exact transOK_point (a0 := 192) (cnt := 64) CFSG.KD.YMS233F.t2_3 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 320 with h | h
        · exact transOK_point (a0 := 256) (cnt := 64) CFSG.KD.YMS233F.t2_4 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 384 with h | h
        · exact transOK_point (a0 := 320) (cnt := 64) CFSG.KD.YMS233F.t2_5 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 448 with h | h
        · exact transOK_point (a0 := 384) (cnt := 64) CFSG.KD.YMS233F.t2_6 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 512 with h | h
        · exact transOK_point (a0 := 448) (cnt := 64) CFSG.KD.YMS233F.t2_7 a (by omega) (by omega)
        exact transOK_point (a0 := 512) (cnt := 55) CFSG.KD.YMS233F.t2_8 a (by omega) (by omega)
      · intro a ha
        change a < 120 at ha
        rcases Nat.lt_or_ge a 64 with h | h
        · exact transOK_point (a0 := 0) (cnt := 64) CFSG.KD.YMS233F.t3_0 a (by omega) (by omega)
        exact transOK_point (a0 := 64) (cnt := 56) CFSG.KD.YMS233F.t3_1 a (by omega) (by omega)
      · intro a ha
        change a < 24 at ha
        exact transOK_point (a0 := 0) (cnt := 24) CFSG.KD.YMS233F.t4_0 a (by omega) (by omega)
      · intro a ha
        change a < 2 at ha
        exact transOK_point (a0 := 0) (cnt := 2) CFSG.KD.YMS233F.t5_0 a (by omega) (by omega)
      · intro a ha
        change a < 2 at ha
        exact transOK_point (a0 := 0) (cnt := 2) CFSG.KD.YMS233F.t6_0 a (by omega) (by omega)
      )
    (by
      intro i hi
      interval_cases i
      · intro a ha j hj1 hj2
        change a < 3510 at ha
        change 9 ≤ j at hj1
        change j < 12 at hj2
        rcases Nat.lt_or_ge a 20 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 40 with h | h
        · exact schOK_rec (a0 := 20) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_1 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 60 with h | h
        · exact schOK_rec (a0 := 40) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_2 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 80 with h | h
        · exact schOK_rec (a0 := 60) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_3 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 100 with h | h
        · exact schOK_rec (a0 := 80) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_4 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 120 with h | h
        · exact schOK_rec (a0 := 100) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_5 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 140 with h | h
        · exact schOK_rec (a0 := 120) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_6 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 160 with h | h
        · exact schOK_rec (a0 := 140) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_7 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 180 with h | h
        · exact schOK_rec (a0 := 160) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_8 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 200 with h | h
        · exact schOK_rec (a0 := 180) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_9 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 220 with h | h
        · exact schOK_rec (a0 := 200) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_10 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 240 with h | h
        · exact schOK_rec (a0 := 220) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_11 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 260 with h | h
        · exact schOK_rec (a0 := 240) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_12 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 280 with h | h
        · exact schOK_rec (a0 := 260) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_13 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 300 with h | h
        · exact schOK_rec (a0 := 280) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_14 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 320 with h | h
        · exact schOK_rec (a0 := 300) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_15 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 340 with h | h
        · exact schOK_rec (a0 := 320) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_16 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 360 with h | h
        · exact schOK_rec (a0 := 340) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_17 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 380 with h | h
        · exact schOK_rec (a0 := 360) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_18 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 400 with h | h
        · exact schOK_rec (a0 := 380) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_19 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 420 with h | h
        · exact schOK_rec (a0 := 400) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_20 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 440 with h | h
        · exact schOK_rec (a0 := 420) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_21 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 460 with h | h
        · exact schOK_rec (a0 := 440) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_22 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 480 with h | h
        · exact schOK_rec (a0 := 460) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_23 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 500 with h | h
        · exact schOK_rec (a0 := 480) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_24 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 520 with h | h
        · exact schOK_rec (a0 := 500) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_25 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 540 with h | h
        · exact schOK_rec (a0 := 520) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_26 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 560 with h | h
        · exact schOK_rec (a0 := 540) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_27 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 580 with h | h
        · exact schOK_rec (a0 := 560) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_28 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 600 with h | h
        · exact schOK_rec (a0 := 580) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_29 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 620 with h | h
        · exact schOK_rec (a0 := 600) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_30 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 640 with h | h
        · exact schOK_rec (a0 := 620) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_31 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 660 with h | h
        · exact schOK_rec (a0 := 640) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_32 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 680 with h | h
        · exact schOK_rec (a0 := 660) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_33 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 700 with h | h
        · exact schOK_rec (a0 := 680) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_34 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 720 with h | h
        · exact schOK_rec (a0 := 700) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_35 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 740 with h | h
        · exact schOK_rec (a0 := 720) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_36 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 760 with h | h
        · exact schOK_rec (a0 := 740) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_37 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 780 with h | h
        · exact schOK_rec (a0 := 760) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_38 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 800 with h | h
        · exact schOK_rec (a0 := 780) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_39 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 820 with h | h
        · exact schOK_rec (a0 := 800) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_40 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 840 with h | h
        · exact schOK_rec (a0 := 820) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_41 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 860 with h | h
        · exact schOK_rec (a0 := 840) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_42 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 880 with h | h
        · exact schOK_rec (a0 := 860) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_43 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 900 with h | h
        · exact schOK_rec (a0 := 880) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_44 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 920 with h | h
        · exact schOK_rec (a0 := 900) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_45 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 940 with h | h
        · exact schOK_rec (a0 := 920) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_46 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 960 with h | h
        · exact schOK_rec (a0 := 940) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_47 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 980 with h | h
        · exact schOK_rec (a0 := 960) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_48 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1000 with h | h
        · exact schOK_rec (a0 := 980) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_49 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1020 with h | h
        · exact schOK_rec (a0 := 1000) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_50 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1040 with h | h
        · exact schOK_rec (a0 := 1020) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_51 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1060 with h | h
        · exact schOK_rec (a0 := 1040) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_52 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1080 with h | h
        · exact schOK_rec (a0 := 1060) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_53 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1100 with h | h
        · exact schOK_rec (a0 := 1080) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_54 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1120 with h | h
        · exact schOK_rec (a0 := 1100) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_55 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1140 with h | h
        · exact schOK_rec (a0 := 1120) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_56 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1160 with h | h
        · exact schOK_rec (a0 := 1140) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_57 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1180 with h | h
        · exact schOK_rec (a0 := 1160) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_58 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1200 with h | h
        · exact schOK_rec (a0 := 1180) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_59 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1220 with h | h
        · exact schOK_rec (a0 := 1200) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_60 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1240 with h | h
        · exact schOK_rec (a0 := 1220) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_61 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1260 with h | h
        · exact schOK_rec (a0 := 1240) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_62 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1280 with h | h
        · exact schOK_rec (a0 := 1260) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_63 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1300 with h | h
        · exact schOK_rec (a0 := 1280) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_64 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1320 with h | h
        · exact schOK_rec (a0 := 1300) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_65 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1340 with h | h
        · exact schOK_rec (a0 := 1320) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_66 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1360 with h | h
        · exact schOK_rec (a0 := 1340) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_67 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1380 with h | h
        · exact schOK_rec (a0 := 1360) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_68 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1400 with h | h
        · exact schOK_rec (a0 := 1380) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_69 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1420 with h | h
        · exact schOK_rec (a0 := 1400) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_70 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1440 with h | h
        · exact schOK_rec (a0 := 1420) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_71 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1460 with h | h
        · exact schOK_rec (a0 := 1440) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_72 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1480 with h | h
        · exact schOK_rec (a0 := 1460) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_73 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1500 with h | h
        · exact schOK_rec (a0 := 1480) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_74 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1520 with h | h
        · exact schOK_rec (a0 := 1500) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_75 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1540 with h | h
        · exact schOK_rec (a0 := 1520) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_76 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1560 with h | h
        · exact schOK_rec (a0 := 1540) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_77 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1580 with h | h
        · exact schOK_rec (a0 := 1560) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_78 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1600 with h | h
        · exact schOK_rec (a0 := 1580) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_79 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1620 with h | h
        · exact schOK_rec (a0 := 1600) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_80 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1640 with h | h
        · exact schOK_rec (a0 := 1620) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_81 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1660 with h | h
        · exact schOK_rec (a0 := 1640) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_82 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1680 with h | h
        · exact schOK_rec (a0 := 1660) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_83 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1700 with h | h
        · exact schOK_rec (a0 := 1680) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_84 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1720 with h | h
        · exact schOK_rec (a0 := 1700) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_85 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1740 with h | h
        · exact schOK_rec (a0 := 1720) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_86 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1760 with h | h
        · exact schOK_rec (a0 := 1740) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_87 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1780 with h | h
        · exact schOK_rec (a0 := 1760) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_88 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1800 with h | h
        · exact schOK_rec (a0 := 1780) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_89 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1820 with h | h
        · exact schOK_rec (a0 := 1800) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_90 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1840 with h | h
        · exact schOK_rec (a0 := 1820) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_91 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1860 with h | h
        · exact schOK_rec (a0 := 1840) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_92 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1880 with h | h
        · exact schOK_rec (a0 := 1860) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_93 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1900 with h | h
        · exact schOK_rec (a0 := 1880) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_94 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1920 with h | h
        · exact schOK_rec (a0 := 1900) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_95 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1940 with h | h
        · exact schOK_rec (a0 := 1920) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_96 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1960 with h | h
        · exact schOK_rec (a0 := 1940) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_97 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1980 with h | h
        · exact schOK_rec (a0 := 1960) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_98 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2000 with h | h
        · exact schOK_rec (a0 := 1980) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_99 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2020 with h | h
        · exact schOK_rec (a0 := 2000) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_100 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2040 with h | h
        · exact schOK_rec (a0 := 2020) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_101 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2060 with h | h
        · exact schOK_rec (a0 := 2040) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_102 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2080 with h | h
        · exact schOK_rec (a0 := 2060) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_103 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2100 with h | h
        · exact schOK_rec (a0 := 2080) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_104 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2120 with h | h
        · exact schOK_rec (a0 := 2100) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_105 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2140 with h | h
        · exact schOK_rec (a0 := 2120) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_106 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2160 with h | h
        · exact schOK_rec (a0 := 2140) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_107 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2180 with h | h
        · exact schOK_rec (a0 := 2160) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_108 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2200 with h | h
        · exact schOK_rec (a0 := 2180) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_109 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2220 with h | h
        · exact schOK_rec (a0 := 2200) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_110 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2240 with h | h
        · exact schOK_rec (a0 := 2220) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_111 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2260 with h | h
        · exact schOK_rec (a0 := 2240) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_112 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2280 with h | h
        · exact schOK_rec (a0 := 2260) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_113 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2300 with h | h
        · exact schOK_rec (a0 := 2280) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_114 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2320 with h | h
        · exact schOK_rec (a0 := 2300) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_115 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2340 with h | h
        · exact schOK_rec (a0 := 2320) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_116 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2360 with h | h
        · exact schOK_rec (a0 := 2340) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_117 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2380 with h | h
        · exact schOK_rec (a0 := 2360) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_118 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2400 with h | h
        · exact schOK_rec (a0 := 2380) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_119 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2420 with h | h
        · exact schOK_rec (a0 := 2400) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_120 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2440 with h | h
        · exact schOK_rec (a0 := 2420) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_121 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2460 with h | h
        · exact schOK_rec (a0 := 2440) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_122 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2480 with h | h
        · exact schOK_rec (a0 := 2460) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_123 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2500 with h | h
        · exact schOK_rec (a0 := 2480) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_124 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2520 with h | h
        · exact schOK_rec (a0 := 2500) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_125 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2540 with h | h
        · exact schOK_rec (a0 := 2520) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_126 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2560 with h | h
        · exact schOK_rec (a0 := 2540) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_127 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2580 with h | h
        · exact schOK_rec (a0 := 2560) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_128 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2600 with h | h
        · exact schOK_rec (a0 := 2580) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_129 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2620 with h | h
        · exact schOK_rec (a0 := 2600) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_130 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2640 with h | h
        · exact schOK_rec (a0 := 2620) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_131 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2660 with h | h
        · exact schOK_rec (a0 := 2640) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_132 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2680 with h | h
        · exact schOK_rec (a0 := 2660) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_133 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2700 with h | h
        · exact schOK_rec (a0 := 2680) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_134 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2720 with h | h
        · exact schOK_rec (a0 := 2700) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_135 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2740 with h | h
        · exact schOK_rec (a0 := 2720) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_136 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2760 with h | h
        · exact schOK_rec (a0 := 2740) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_137 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2780 with h | h
        · exact schOK_rec (a0 := 2760) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_138 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2800 with h | h
        · exact schOK_rec (a0 := 2780) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_139 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2820 with h | h
        · exact schOK_rec (a0 := 2800) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_140 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2840 with h | h
        · exact schOK_rec (a0 := 2820) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_141 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2860 with h | h
        · exact schOK_rec (a0 := 2840) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_142 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2880 with h | h
        · exact schOK_rec (a0 := 2860) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_143 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2900 with h | h
        · exact schOK_rec (a0 := 2880) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_144 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2920 with h | h
        · exact schOK_rec (a0 := 2900) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_145 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2940 with h | h
        · exact schOK_rec (a0 := 2920) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_146 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2960 with h | h
        · exact schOK_rec (a0 := 2940) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_147 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2980 with h | h
        · exact schOK_rec (a0 := 2960) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_148 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3000 with h | h
        · exact schOK_rec (a0 := 2980) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_149 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3020 with h | h
        · exact schOK_rec (a0 := 3000) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_150 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3040 with h | h
        · exact schOK_rec (a0 := 3020) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_151 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3060 with h | h
        · exact schOK_rec (a0 := 3040) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_152 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3080 with h | h
        · exact schOK_rec (a0 := 3060) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_153 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3100 with h | h
        · exact schOK_rec (a0 := 3080) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_154 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3120 with h | h
        · exact schOK_rec (a0 := 3100) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_155 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3140 with h | h
        · exact schOK_rec (a0 := 3120) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_156 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3160 with h | h
        · exact schOK_rec (a0 := 3140) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_157 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3180 with h | h
        · exact schOK_rec (a0 := 3160) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_158 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3200 with h | h
        · exact schOK_rec (a0 := 3180) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_159 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3220 with h | h
        · exact schOK_rec (a0 := 3200) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_160 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3240 with h | h
        · exact schOK_rec (a0 := 3220) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_161 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3260 with h | h
        · exact schOK_rec (a0 := 3240) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_162 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3280 with h | h
        · exact schOK_rec (a0 := 3260) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_163 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3300 with h | h
        · exact schOK_rec (a0 := 3280) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_164 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3320 with h | h
        · exact schOK_rec (a0 := 3300) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_165 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3340 with h | h
        · exact schOK_rec (a0 := 3320) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_166 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3360 with h | h
        · exact schOK_rec (a0 := 3340) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_167 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3380 with h | h
        · exact schOK_rec (a0 := 3360) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_168 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3400 with h | h
        · exact schOK_rec (a0 := 3380) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_169 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3420 with h | h
        · exact schOK_rec (a0 := 3400) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_170 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3440 with h | h
        · exact schOK_rec (a0 := 3420) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_171 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3460 with h | h
        · exact schOK_rec (a0 := 3440) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_172 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3480 with h | h
        · exact schOK_rec (a0 := 3460) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_173 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3500 with h | h
        · exact schOK_rec (a0 := 3480) (cnt := 20) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_174 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 3500) (cnt := 10) (lo := 9) (hi := 12) CFSG.KD.YMS233F.s0_175 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 2816 at ha
        change 12 ≤ j at hj1
        change j < 15 at hj2
        rcases Nat.lt_or_ge a 20 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 40 with h | h
        · exact schOK_rec (a0 := 20) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_1 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 60 with h | h
        · exact schOK_rec (a0 := 40) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_2 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 80 with h | h
        · exact schOK_rec (a0 := 60) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_3 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 100 with h | h
        · exact schOK_rec (a0 := 80) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_4 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 120 with h | h
        · exact schOK_rec (a0 := 100) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_5 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 140 with h | h
        · exact schOK_rec (a0 := 120) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_6 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 160 with h | h
        · exact schOK_rec (a0 := 140) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_7 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 180 with h | h
        · exact schOK_rec (a0 := 160) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_8 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 200 with h | h
        · exact schOK_rec (a0 := 180) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_9 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 220 with h | h
        · exact schOK_rec (a0 := 200) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_10 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 240 with h | h
        · exact schOK_rec (a0 := 220) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_11 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 260 with h | h
        · exact schOK_rec (a0 := 240) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_12 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 280 with h | h
        · exact schOK_rec (a0 := 260) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_13 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 300 with h | h
        · exact schOK_rec (a0 := 280) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_14 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 320 with h | h
        · exact schOK_rec (a0 := 300) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_15 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 340 with h | h
        · exact schOK_rec (a0 := 320) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_16 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 360 with h | h
        · exact schOK_rec (a0 := 340) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_17 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 380 with h | h
        · exact schOK_rec (a0 := 360) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_18 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 400 with h | h
        · exact schOK_rec (a0 := 380) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_19 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 420 with h | h
        · exact schOK_rec (a0 := 400) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_20 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 440 with h | h
        · exact schOK_rec (a0 := 420) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_21 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 460 with h | h
        · exact schOK_rec (a0 := 440) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_22 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 480 with h | h
        · exact schOK_rec (a0 := 460) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_23 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 500 with h | h
        · exact schOK_rec (a0 := 480) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_24 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 520 with h | h
        · exact schOK_rec (a0 := 500) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_25 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 540 with h | h
        · exact schOK_rec (a0 := 520) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_26 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 560 with h | h
        · exact schOK_rec (a0 := 540) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_27 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 580 with h | h
        · exact schOK_rec (a0 := 560) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_28 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 600 with h | h
        · exact schOK_rec (a0 := 580) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_29 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 620 with h | h
        · exact schOK_rec (a0 := 600) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_30 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 640 with h | h
        · exact schOK_rec (a0 := 620) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_31 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 660 with h | h
        · exact schOK_rec (a0 := 640) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_32 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 680 with h | h
        · exact schOK_rec (a0 := 660) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_33 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 700 with h | h
        · exact schOK_rec (a0 := 680) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_34 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 720 with h | h
        · exact schOK_rec (a0 := 700) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_35 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 740 with h | h
        · exact schOK_rec (a0 := 720) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_36 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 760 with h | h
        · exact schOK_rec (a0 := 740) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_37 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 780 with h | h
        · exact schOK_rec (a0 := 760) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_38 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 800 with h | h
        · exact schOK_rec (a0 := 780) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_39 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 820 with h | h
        · exact schOK_rec (a0 := 800) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_40 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 840 with h | h
        · exact schOK_rec (a0 := 820) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_41 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 860 with h | h
        · exact schOK_rec (a0 := 840) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_42 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 880 with h | h
        · exact schOK_rec (a0 := 860) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_43 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 900 with h | h
        · exact schOK_rec (a0 := 880) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_44 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 920 with h | h
        · exact schOK_rec (a0 := 900) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_45 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 940 with h | h
        · exact schOK_rec (a0 := 920) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_46 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 960 with h | h
        · exact schOK_rec (a0 := 940) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_47 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 980 with h | h
        · exact schOK_rec (a0 := 960) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_48 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1000 with h | h
        · exact schOK_rec (a0 := 980) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_49 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1020 with h | h
        · exact schOK_rec (a0 := 1000) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_50 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1040 with h | h
        · exact schOK_rec (a0 := 1020) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_51 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1060 with h | h
        · exact schOK_rec (a0 := 1040) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_52 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1080 with h | h
        · exact schOK_rec (a0 := 1060) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_53 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1100 with h | h
        · exact schOK_rec (a0 := 1080) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_54 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1120 with h | h
        · exact schOK_rec (a0 := 1100) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_55 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1140 with h | h
        · exact schOK_rec (a0 := 1120) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_56 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1160 with h | h
        · exact schOK_rec (a0 := 1140) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_57 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1180 with h | h
        · exact schOK_rec (a0 := 1160) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_58 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1200 with h | h
        · exact schOK_rec (a0 := 1180) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_59 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1220 with h | h
        · exact schOK_rec (a0 := 1200) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_60 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1240 with h | h
        · exact schOK_rec (a0 := 1220) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_61 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1260 with h | h
        · exact schOK_rec (a0 := 1240) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_62 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1280 with h | h
        · exact schOK_rec (a0 := 1260) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_63 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1300 with h | h
        · exact schOK_rec (a0 := 1280) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_64 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1320 with h | h
        · exact schOK_rec (a0 := 1300) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_65 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1340 with h | h
        · exact schOK_rec (a0 := 1320) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_66 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1360 with h | h
        · exact schOK_rec (a0 := 1340) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_67 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1380 with h | h
        · exact schOK_rec (a0 := 1360) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_68 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1400 with h | h
        · exact schOK_rec (a0 := 1380) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_69 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1420 with h | h
        · exact schOK_rec (a0 := 1400) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_70 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1440 with h | h
        · exact schOK_rec (a0 := 1420) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_71 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1460 with h | h
        · exact schOK_rec (a0 := 1440) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_72 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1480 with h | h
        · exact schOK_rec (a0 := 1460) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_73 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1500 with h | h
        · exact schOK_rec (a0 := 1480) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_74 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1520 with h | h
        · exact schOK_rec (a0 := 1500) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_75 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1540 with h | h
        · exact schOK_rec (a0 := 1520) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_76 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1560 with h | h
        · exact schOK_rec (a0 := 1540) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_77 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1580 with h | h
        · exact schOK_rec (a0 := 1560) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_78 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1600 with h | h
        · exact schOK_rec (a0 := 1580) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_79 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1620 with h | h
        · exact schOK_rec (a0 := 1600) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_80 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1640 with h | h
        · exact schOK_rec (a0 := 1620) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_81 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1660 with h | h
        · exact schOK_rec (a0 := 1640) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_82 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1680 with h | h
        · exact schOK_rec (a0 := 1660) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_83 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1700 with h | h
        · exact schOK_rec (a0 := 1680) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_84 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1720 with h | h
        · exact schOK_rec (a0 := 1700) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_85 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1740 with h | h
        · exact schOK_rec (a0 := 1720) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_86 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1760 with h | h
        · exact schOK_rec (a0 := 1740) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_87 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1780 with h | h
        · exact schOK_rec (a0 := 1760) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_88 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1800 with h | h
        · exact schOK_rec (a0 := 1780) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_89 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1820 with h | h
        · exact schOK_rec (a0 := 1800) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_90 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1840 with h | h
        · exact schOK_rec (a0 := 1820) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_91 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1860 with h | h
        · exact schOK_rec (a0 := 1840) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_92 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1880 with h | h
        · exact schOK_rec (a0 := 1860) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_93 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1900 with h | h
        · exact schOK_rec (a0 := 1880) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_94 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1920 with h | h
        · exact schOK_rec (a0 := 1900) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_95 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1940 with h | h
        · exact schOK_rec (a0 := 1920) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_96 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1960 with h | h
        · exact schOK_rec (a0 := 1940) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_97 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 1980 with h | h
        · exact schOK_rec (a0 := 1960) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_98 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2000 with h | h
        · exact schOK_rec (a0 := 1980) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_99 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2020 with h | h
        · exact schOK_rec (a0 := 2000) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_100 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2040 with h | h
        · exact schOK_rec (a0 := 2020) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_101 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2060 with h | h
        · exact schOK_rec (a0 := 2040) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_102 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2080 with h | h
        · exact schOK_rec (a0 := 2060) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_103 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2100 with h | h
        · exact schOK_rec (a0 := 2080) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_104 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2120 with h | h
        · exact schOK_rec (a0 := 2100) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_105 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2140 with h | h
        · exact schOK_rec (a0 := 2120) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_106 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2160 with h | h
        · exact schOK_rec (a0 := 2140) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_107 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2180 with h | h
        · exact schOK_rec (a0 := 2160) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_108 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2200 with h | h
        · exact schOK_rec (a0 := 2180) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_109 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2220 with h | h
        · exact schOK_rec (a0 := 2200) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_110 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2240 with h | h
        · exact schOK_rec (a0 := 2220) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_111 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2260 with h | h
        · exact schOK_rec (a0 := 2240) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_112 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2280 with h | h
        · exact schOK_rec (a0 := 2260) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_113 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2300 with h | h
        · exact schOK_rec (a0 := 2280) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_114 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2320 with h | h
        · exact schOK_rec (a0 := 2300) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_115 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2340 with h | h
        · exact schOK_rec (a0 := 2320) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_116 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2360 with h | h
        · exact schOK_rec (a0 := 2340) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_117 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2380 with h | h
        · exact schOK_rec (a0 := 2360) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_118 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2400 with h | h
        · exact schOK_rec (a0 := 2380) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_119 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2420 with h | h
        · exact schOK_rec (a0 := 2400) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_120 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2440 with h | h
        · exact schOK_rec (a0 := 2420) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_121 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2460 with h | h
        · exact schOK_rec (a0 := 2440) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_122 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2480 with h | h
        · exact schOK_rec (a0 := 2460) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_123 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2500 with h | h
        · exact schOK_rec (a0 := 2480) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_124 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2520 with h | h
        · exact schOK_rec (a0 := 2500) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_125 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2540 with h | h
        · exact schOK_rec (a0 := 2520) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_126 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2560 with h | h
        · exact schOK_rec (a0 := 2540) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_127 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2580 with h | h
        · exact schOK_rec (a0 := 2560) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_128 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2600 with h | h
        · exact schOK_rec (a0 := 2580) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_129 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2620 with h | h
        · exact schOK_rec (a0 := 2600) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_130 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2640 with h | h
        · exact schOK_rec (a0 := 2620) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_131 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2660 with h | h
        · exact schOK_rec (a0 := 2640) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_132 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2680 with h | h
        · exact schOK_rec (a0 := 2660) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_133 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2700 with h | h
        · exact schOK_rec (a0 := 2680) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_134 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2720 with h | h
        · exact schOK_rec (a0 := 2700) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_135 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2740 with h | h
        · exact schOK_rec (a0 := 2720) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_136 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2760 with h | h
        · exact schOK_rec (a0 := 2740) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_137 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2780 with h | h
        · exact schOK_rec (a0 := 2760) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_138 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2800 with h | h
        · exact schOK_rec (a0 := 2780) (cnt := 20) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_139 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 2800) (cnt := 16) (lo := 12) (hi := 15) CFSG.KD.YMS233F.s1_140 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 567 at ha
        change 15 ≤ j at hj1
        change j < 19 at hj2
        rcases Nat.lt_or_ge a 15 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 30 with h | h
        · exact schOK_rec (a0 := 15) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_1 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 45 with h | h
        · exact schOK_rec (a0 := 30) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_2 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 60 with h | h
        · exact schOK_rec (a0 := 45) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_3 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 75 with h | h
        · exact schOK_rec (a0 := 60) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_4 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 90 with h | h
        · exact schOK_rec (a0 := 75) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_5 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 105 with h | h
        · exact schOK_rec (a0 := 90) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_6 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 120 with h | h
        · exact schOK_rec (a0 := 105) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_7 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 135 with h | h
        · exact schOK_rec (a0 := 120) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_8 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 150 with h | h
        · exact schOK_rec (a0 := 135) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_9 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 165 with h | h
        · exact schOK_rec (a0 := 150) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_10 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 180 with h | h
        · exact schOK_rec (a0 := 165) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_11 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 195 with h | h
        · exact schOK_rec (a0 := 180) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_12 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 210 with h | h
        · exact schOK_rec (a0 := 195) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_13 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 225 with h | h
        · exact schOK_rec (a0 := 210) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_14 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 240 with h | h
        · exact schOK_rec (a0 := 225) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_15 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 255 with h | h
        · exact schOK_rec (a0 := 240) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_16 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 270 with h | h
        · exact schOK_rec (a0 := 255) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_17 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 285 with h | h
        · exact schOK_rec (a0 := 270) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_18 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 300 with h | h
        · exact schOK_rec (a0 := 285) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_19 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 315 with h | h
        · exact schOK_rec (a0 := 300) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_20 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 330 with h | h
        · exact schOK_rec (a0 := 315) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_21 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 345 with h | h
        · exact schOK_rec (a0 := 330) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_22 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 360 with h | h
        · exact schOK_rec (a0 := 345) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_23 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 375 with h | h
        · exact schOK_rec (a0 := 360) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_24 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 390 with h | h
        · exact schOK_rec (a0 := 375) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_25 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 405 with h | h
        · exact schOK_rec (a0 := 390) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_26 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 420 with h | h
        · exact schOK_rec (a0 := 405) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_27 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 435 with h | h
        · exact schOK_rec (a0 := 420) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_28 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 450 with h | h
        · exact schOK_rec (a0 := 435) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_29 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 465 with h | h
        · exact schOK_rec (a0 := 450) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_30 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 480 with h | h
        · exact schOK_rec (a0 := 465) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_31 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 495 with h | h
        · exact schOK_rec (a0 := 480) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_32 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 510 with h | h
        · exact schOK_rec (a0 := 495) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_33 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 525 with h | h
        · exact schOK_rec (a0 := 510) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_34 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 540 with h | h
        · exact schOK_rec (a0 := 525) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_35 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 555 with h | h
        · exact schOK_rec (a0 := 540) (cnt := 15) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_36 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 555) (cnt := 12) (lo := 15) (hi := 19) CFSG.KD.YMS233F.s2_37 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 120 at ha
        change 19 ≤ j at hj1
        change j < 24 at hj2
        rcases Nat.lt_or_ge a 12 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 12) (lo := 19) (hi := 24) CFSG.KD.YMS233F.s3_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 24 with h | h
        · exact schOK_rec (a0 := 12) (cnt := 12) (lo := 19) (hi := 24) CFSG.KD.YMS233F.s3_1 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 36 with h | h
        · exact schOK_rec (a0 := 24) (cnt := 12) (lo := 19) (hi := 24) CFSG.KD.YMS233F.s3_2 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 48 with h | h
        · exact schOK_rec (a0 := 36) (cnt := 12) (lo := 19) (hi := 24) CFSG.KD.YMS233F.s3_3 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 60 with h | h
        · exact schOK_rec (a0 := 48) (cnt := 12) (lo := 19) (hi := 24) CFSG.KD.YMS233F.s3_4 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 72 with h | h
        · exact schOK_rec (a0 := 60) (cnt := 12) (lo := 19) (hi := 24) CFSG.KD.YMS233F.s3_5 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 84 with h | h
        · exact schOK_rec (a0 := 72) (cnt := 12) (lo := 19) (hi := 24) CFSG.KD.YMS233F.s3_6 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 96 with h | h
        · exact schOK_rec (a0 := 84) (cnt := 12) (lo := 19) (hi := 24) CFSG.KD.YMS233F.s3_7 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 108 with h | h
        · exact schOK_rec (a0 := 96) (cnt := 12) (lo := 19) (hi := 24) CFSG.KD.YMS233F.s3_8 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 108) (cnt := 12) (lo := 19) (hi := 24) CFSG.KD.YMS233F.s3_9 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 24 at ha
        change 24 ≤ j at hj1
        change j < 29 at hj2
        rcases Nat.lt_or_ge a 12 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 12) (lo := 24) (hi := 29) CFSG.KD.YMS233F.s4_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 12) (cnt := 12) (lo := 24) (hi := 29) CFSG.KD.YMS233F.s4_1 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 2 at ha
        change 29 ≤ j at hj1
        change j < 33 at hj2
        exact schOK_rec (a0 := 0) (cnt := 2) (lo := 29) (hi := 33) CFSG.KD.YMS233F.s5_0 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 2 at ha
        change 33 ≤ j at hj1
        change j < 36 at hj2
        exact schOK_rec (a0 := 0) (cnt := 2) (lo := 33) (hi := 36) CFSG.KD.YMS233F.s6_0 (by decide) a
          (by omega) (by omega) j hj1 hj2
      )
    (by
      intro c hc
      interval_cases c
      exacts [⟨CFSG.KD.YMS233F.lw0, CFSG.KD.YMS233F.lc0⟩, ⟨CFSG.KD.YMS233F.lw1, CFSG.KD.YMS233F.lc1⟩, ⟨CFSG.KD.YMS233F.lw2, CFSG.KD.YMS233F.lc2⟩, ⟨CFSG.KD.YMS233F.lw3, CFSG.KD.YMS233F.lc3⟩, ⟨CFSG.KD.YMS233F.lw4, CFSG.KD.YMS233F.lc4⟩, ⟨CFSG.KD.YMS233F.lw5, CFSG.KD.YMS233F.lc5⟩, ⟨CFSG.KD.YMS233F.lw6, CFSG.KD.YMS233F.lc6⟩, ⟨CFSG.KD.YMS233F.lw7, CFSG.KD.YMS233F.lc7⟩, ⟨CFSG.KD.YMS233F.lw8, CFSG.KD.YMS233F.lc8⟩])
  rw [h]
  decide

end CertificateChecks.KernelYModel

end
