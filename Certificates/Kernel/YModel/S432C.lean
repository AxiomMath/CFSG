module

public import Certificates.Kernel.YModel.Basic
public import CFSG.Certificates.Kernel.YModel.S432C.Data
import CFSG.Certificates.Kernel.YModel.S432C.CheckL
import CFSG.Certificates.Kernel.YModel.S432C.CheckG
import CFSG.Certificates.Kernel.YModel.S432C.CheckP
import CFSG.Certificates.Kernel.YModel.S432C.CheckT
import CFSG.Certificates.Kernel.YModel.S432C.CheckS0
import CFSG.Certificates.Kernel.YModel.S432C.CheckS1
import CFSG.Certificates.Kernel.YModel.S432C.CheckS2
import CFSG.Certificates.Kernel.YModel.S432C.CheckS3

public section

namespace CertificateChecks.KernelYModel

open CFSG.KC.YModel

set_option maxRecDepth 100000

theorem s432C_card : Nat.card (CFSG.YGroups.arrClosure 31671 (linesA (fun _ => 31671) 32 CFSG.KD.YMS432C.LF 9)) =
    47377612800 := by
  have h := card_arrClosure_of_sch (k := 15) (n := 31671) (m := 9) (w := 8) (t := 9)
    (F := CFSG.KD.YMS432C.LF) (Nf := CFSG.KD.YMS432C.Nf) (U := CFSG.KD.YMS432C.U) (WP := CFSG.KD.YMS432C.GP) (WL := CFSG.KD.YMS432C.GL) (TT := CFSG.KD.YMS432C.TT)
    (off := CFSG.KC.YModel.lget [9, 11, 14, 19, 28, 40, 48, 53, 57, 60]) (bp := CFSG.KC.YModel.lget [0, 52, 166, 722, 1, 3, 10, 5, 8]) (Z := CFSG.KC.YModel.lget [255, 126, 60, 24, 16, 8, 2, 2, 2])
    (LP := CFSG.KC.YModel.lget [145601891183903003663148578, 26206, 482181789740, 1885101632, 37249867514123851592276255252, 28774, 2684135841985000416426788091952225694741174300, 120, 30832]) (LL := CFSG.KC.YModel.lget [11, 2, 5, 4, 12, 2, 19, 1, 2])
    (by intro c hc; interval_cases c; exacts [CFSG.KD.YMS432C.l0, CFSG.KD.YMS432C.l1, CFSG.KD.YMS432C.l2, CFSG.KD.YMS432C.l3, CFSG.KD.YMS432C.l4, CFSG.KD.YMS432C.l5, CFSG.KD.YMS432C.l6, CFSG.KD.YMS432C.l7, CFSG.KD.YMS432C.l8])
    (by intro c hc; interval_cases c <;> rfl)
    rfl (by decide)
    (by
      intro j h1 h2
      change 9 ≤ j at h1
      change j < 11 at h2
      interval_cases j
      exacts [CFSG.KD.YMS432C.g9, CFSG.KD.YMS432C.g10])
    (by
      intro i hi1 hi2
      interval_cases i
      · intro j h1 h2
        change 11 ≤ j at h1
        change j < 14 at h2
        interval_cases j
        exacts [CFSG.KD.YMS432C.g11, CFSG.KD.YMS432C.g12, CFSG.KD.YMS432C.g13]
      · intro j h1 h2
        change 14 ≤ j at h1
        change j < 19 at h2
        interval_cases j
        exacts [CFSG.KD.YMS432C.g14, CFSG.KD.YMS432C.g15, CFSG.KD.YMS432C.g16, CFSG.KD.YMS432C.g17, CFSG.KD.YMS432C.g18]
      · intro j h1 h2
        change 19 ≤ j at h1
        change j < 28 at h2
        interval_cases j
        exacts [CFSG.KD.YMS432C.g19, CFSG.KD.YMS432C.g20, CFSG.KD.YMS432C.g21, CFSG.KD.YMS432C.g22, CFSG.KD.YMS432C.g23, CFSG.KD.YMS432C.g24, CFSG.KD.YMS432C.g25, CFSG.KD.YMS432C.g26, CFSG.KD.YMS432C.g27]
      · intro j h1 h2
        change 28 ≤ j at h1
        change j < 40 at h2
        interval_cases j
        exacts [CFSG.KD.YMS432C.g28, CFSG.KD.YMS432C.g29, CFSG.KD.YMS432C.g30, CFSG.KD.YMS432C.g31, CFSG.KD.YMS432C.g32, CFSG.KD.YMS432C.g33, CFSG.KD.YMS432C.g34, CFSG.KD.YMS432C.g35, CFSG.KD.YMS432C.g36, CFSG.KD.YMS432C.g37, CFSG.KD.YMS432C.g38, CFSG.KD.YMS432C.g39]
      · intro j h1 h2
        change 40 ≤ j at h1
        change j < 48 at h2
        interval_cases j
        exacts [CFSG.KD.YMS432C.g40, CFSG.KD.YMS432C.g41, CFSG.KD.YMS432C.g42, CFSG.KD.YMS432C.g43, CFSG.KD.YMS432C.g44, CFSG.KD.YMS432C.g45, CFSG.KD.YMS432C.g46, CFSG.KD.YMS432C.g47]
      · intro j h1 h2
        change 48 ≤ j at h1
        change j < 53 at h2
        interval_cases j
        exacts [CFSG.KD.YMS432C.g48, CFSG.KD.YMS432C.g49, CFSG.KD.YMS432C.g50, CFSG.KD.YMS432C.g51, CFSG.KD.YMS432C.g52]
      · intro j h1 h2
        change 53 ≤ j at h1
        change j < 57 at h2
        interval_cases j
        exacts [CFSG.KD.YMS432C.g53, CFSG.KD.YMS432C.g54, CFSG.KD.YMS432C.g55, CFSG.KD.YMS432C.g56]
      · intro j h1 h2
        change 57 ≤ j at h1
        change j < 60 at h2
        interval_cases j
        exacts [CFSG.KD.YMS432C.g57, CFSG.KD.YMS432C.g58, CFSG.KD.YMS432C.g59]
      )
    (by intro i hi; interval_cases i <;> decide)
    (by
      intro i hi
      interval_cases i
      exacts [⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS432C.b0, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS432C.b1, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS432C.b2, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS432C.b3, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS432C.b4, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS432C.b5, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS432C.b6, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS432C.b7, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS432C.b8, by decide⟩])
    (by intro i hi; interval_cases i; exacts [CFSG.KD.YMS432C.p0, CFSG.KD.YMS432C.p1, CFSG.KD.YMS432C.p2, CFSG.KD.YMS432C.p3, CFSG.KD.YMS432C.p4, CFSG.KD.YMS432C.p5, CFSG.KD.YMS432C.p6, CFSG.KD.YMS432C.p7, CFSG.KD.YMS432C.p8])
    (by
      intro i hi
      interval_cases i
      · intro a ha
        change a < 255 at ha
        rcases Nat.lt_or_ge a 12 with h | h
        · exact transOK_point (a0 := 0) (cnt := 12) CFSG.KD.YMS432C.t0_0 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 24 with h | h
        · exact transOK_point (a0 := 12) (cnt := 12) CFSG.KD.YMS432C.t0_1 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 36 with h | h
        · exact transOK_point (a0 := 24) (cnt := 12) CFSG.KD.YMS432C.t0_2 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 48 with h | h
        · exact transOK_point (a0 := 36) (cnt := 12) CFSG.KD.YMS432C.t0_3 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 60 with h | h
        · exact transOK_point (a0 := 48) (cnt := 12) CFSG.KD.YMS432C.t0_4 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 72 with h | h
        · exact transOK_point (a0 := 60) (cnt := 12) CFSG.KD.YMS432C.t0_5 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 84 with h | h
        · exact transOK_point (a0 := 72) (cnt := 12) CFSG.KD.YMS432C.t0_6 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 96 with h | h
        · exact transOK_point (a0 := 84) (cnt := 12) CFSG.KD.YMS432C.t0_7 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 108 with h | h
        · exact transOK_point (a0 := 96) (cnt := 12) CFSG.KD.YMS432C.t0_8 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 120 with h | h
        · exact transOK_point (a0 := 108) (cnt := 12) CFSG.KD.YMS432C.t0_9 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 132 with h | h
        · exact transOK_point (a0 := 120) (cnt := 12) CFSG.KD.YMS432C.t0_10 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 144 with h | h
        · exact transOK_point (a0 := 132) (cnt := 12) CFSG.KD.YMS432C.t0_11 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 156 with h | h
        · exact transOK_point (a0 := 144) (cnt := 12) CFSG.KD.YMS432C.t0_12 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 168 with h | h
        · exact transOK_point (a0 := 156) (cnt := 12) CFSG.KD.YMS432C.t0_13 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 180 with h | h
        · exact transOK_point (a0 := 168) (cnt := 12) CFSG.KD.YMS432C.t0_14 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 192 with h | h
        · exact transOK_point (a0 := 180) (cnt := 12) CFSG.KD.YMS432C.t0_15 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 204 with h | h
        · exact transOK_point (a0 := 192) (cnt := 12) CFSG.KD.YMS432C.t0_16 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 216 with h | h
        · exact transOK_point (a0 := 204) (cnt := 12) CFSG.KD.YMS432C.t0_17 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 228 with h | h
        · exact transOK_point (a0 := 216) (cnt := 12) CFSG.KD.YMS432C.t0_18 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 240 with h | h
        · exact transOK_point (a0 := 228) (cnt := 12) CFSG.KD.YMS432C.t0_19 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 252 with h | h
        · exact transOK_point (a0 := 240) (cnt := 12) CFSG.KD.YMS432C.t0_20 a (by omega) (by omega)
        exact transOK_point (a0 := 252) (cnt := 3) CFSG.KD.YMS432C.t0_21 a (by omega) (by omega)
      · intro a ha
        change a < 126 at ha
        rcases Nat.lt_or_ge a 12 with h | h
        · exact transOK_point (a0 := 0) (cnt := 12) CFSG.KD.YMS432C.t1_0 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 24 with h | h
        · exact transOK_point (a0 := 12) (cnt := 12) CFSG.KD.YMS432C.t1_1 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 36 with h | h
        · exact transOK_point (a0 := 24) (cnt := 12) CFSG.KD.YMS432C.t1_2 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 48 with h | h
        · exact transOK_point (a0 := 36) (cnt := 12) CFSG.KD.YMS432C.t1_3 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 60 with h | h
        · exact transOK_point (a0 := 48) (cnt := 12) CFSG.KD.YMS432C.t1_4 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 72 with h | h
        · exact transOK_point (a0 := 60) (cnt := 12) CFSG.KD.YMS432C.t1_5 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 84 with h | h
        · exact transOK_point (a0 := 72) (cnt := 12) CFSG.KD.YMS432C.t1_6 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 96 with h | h
        · exact transOK_point (a0 := 84) (cnt := 12) CFSG.KD.YMS432C.t1_7 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 108 with h | h
        · exact transOK_point (a0 := 96) (cnt := 12) CFSG.KD.YMS432C.t1_8 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 120 with h | h
        · exact transOK_point (a0 := 108) (cnt := 12) CFSG.KD.YMS432C.t1_9 a (by omega) (by omega)
        exact transOK_point (a0 := 120) (cnt := 6) CFSG.KD.YMS432C.t1_10 a (by omega) (by omega)
      · intro a ha
        change a < 60 at ha
        rcases Nat.lt_or_ge a 12 with h | h
        · exact transOK_point (a0 := 0) (cnt := 12) CFSG.KD.YMS432C.t2_0 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 24 with h | h
        · exact transOK_point (a0 := 12) (cnt := 12) CFSG.KD.YMS432C.t2_1 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 36 with h | h
        · exact transOK_point (a0 := 24) (cnt := 12) CFSG.KD.YMS432C.t2_2 a (by omega) (by omega)
        rcases Nat.lt_or_ge a 48 with h | h
        · exact transOK_point (a0 := 36) (cnt := 12) CFSG.KD.YMS432C.t2_3 a (by omega) (by omega)
        exact transOK_point (a0 := 48) (cnt := 12) CFSG.KD.YMS432C.t2_4 a (by omega) (by omega)
      · intro a ha
        change a < 24 at ha
        rcases Nat.lt_or_ge a 12 with h | h
        · exact transOK_point (a0 := 0) (cnt := 12) CFSG.KD.YMS432C.t3_0 a (by omega) (by omega)
        exact transOK_point (a0 := 12) (cnt := 12) CFSG.KD.YMS432C.t3_1 a (by omega) (by omega)
      · intro a ha
        change a < 16 at ha
        rcases Nat.lt_or_ge a 12 with h | h
        · exact transOK_point (a0 := 0) (cnt := 12) CFSG.KD.YMS432C.t4_0 a (by omega) (by omega)
        exact transOK_point (a0 := 12) (cnt := 4) CFSG.KD.YMS432C.t4_1 a (by omega) (by omega)
      · intro a ha
        change a < 8 at ha
        exact transOK_point (a0 := 0) (cnt := 8) CFSG.KD.YMS432C.t5_0 a (by omega) (by omega)
      · intro a ha
        change a < 2 at ha
        exact transOK_point (a0 := 0) (cnt := 2) CFSG.KD.YMS432C.t6_0 a (by omega) (by omega)
      · intro a ha
        change a < 2 at ha
        exact transOK_point (a0 := 0) (cnt := 2) CFSG.KD.YMS432C.t7_0 a (by omega) (by omega)
      · intro a ha
        change a < 2 at ha
        exact transOK_point (a0 := 0) (cnt := 2) CFSG.KD.YMS432C.t8_0 a (by omega) (by omega)
      )
    (by
      intro i hi
      interval_cases i
      · intro a ha j hj1 hj2
        change a < 255 at ha
        change 9 ≤ j at hj1
        change j < 11 at hj2
        rcases Nat.lt_or_ge a 5 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 10 with h | h
        · exact schOK_rec (a0 := 5) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_1 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 15 with h | h
        · exact schOK_rec (a0 := 10) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_2 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 20 with h | h
        · exact schOK_rec (a0 := 15) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_3 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 25 with h | h
        · exact schOK_rec (a0 := 20) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_4 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 30 with h | h
        · exact schOK_rec (a0 := 25) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_5 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 35 with h | h
        · exact schOK_rec (a0 := 30) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_6 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 40 with h | h
        · exact schOK_rec (a0 := 35) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_7 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 45 with h | h
        · exact schOK_rec (a0 := 40) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_8 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 50 with h | h
        · exact schOK_rec (a0 := 45) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_9 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 55 with h | h
        · exact schOK_rec (a0 := 50) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_10 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 60 with h | h
        · exact schOK_rec (a0 := 55) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_11 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 65 with h | h
        · exact schOK_rec (a0 := 60) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_12 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 70 with h | h
        · exact schOK_rec (a0 := 65) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_13 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 75 with h | h
        · exact schOK_rec (a0 := 70) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_14 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 80 with h | h
        · exact schOK_rec (a0 := 75) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_15 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 85 with h | h
        · exact schOK_rec (a0 := 80) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_16 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 90 with h | h
        · exact schOK_rec (a0 := 85) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_17 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 95 with h | h
        · exact schOK_rec (a0 := 90) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_18 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 100 with h | h
        · exact schOK_rec (a0 := 95) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_19 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 105 with h | h
        · exact schOK_rec (a0 := 100) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_20 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 110 with h | h
        · exact schOK_rec (a0 := 105) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_21 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 115 with h | h
        · exact schOK_rec (a0 := 110) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_22 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 120 with h | h
        · exact schOK_rec (a0 := 115) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_23 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 125 with h | h
        · exact schOK_rec (a0 := 120) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_24 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 130 with h | h
        · exact schOK_rec (a0 := 125) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_25 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 135 with h | h
        · exact schOK_rec (a0 := 130) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_26 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 140 with h | h
        · exact schOK_rec (a0 := 135) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_27 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 145 with h | h
        · exact schOK_rec (a0 := 140) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_28 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 150 with h | h
        · exact schOK_rec (a0 := 145) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_29 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 155 with h | h
        · exact schOK_rec (a0 := 150) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_30 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 160 with h | h
        · exact schOK_rec (a0 := 155) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_31 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 165 with h | h
        · exact schOK_rec (a0 := 160) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_32 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 170 with h | h
        · exact schOK_rec (a0 := 165) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_33 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 175 with h | h
        · exact schOK_rec (a0 := 170) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_34 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 180 with h | h
        · exact schOK_rec (a0 := 175) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_35 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 185 with h | h
        · exact schOK_rec (a0 := 180) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_36 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 190 with h | h
        · exact schOK_rec (a0 := 185) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_37 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 195 with h | h
        · exact schOK_rec (a0 := 190) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_38 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 200 with h | h
        · exact schOK_rec (a0 := 195) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_39 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 205 with h | h
        · exact schOK_rec (a0 := 200) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_40 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 210 with h | h
        · exact schOK_rec (a0 := 205) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_41 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 215 with h | h
        · exact schOK_rec (a0 := 210) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_42 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 220 with h | h
        · exact schOK_rec (a0 := 215) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_43 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 225 with h | h
        · exact schOK_rec (a0 := 220) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_44 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 230 with h | h
        · exact schOK_rec (a0 := 225) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_45 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 235 with h | h
        · exact schOK_rec (a0 := 230) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_46 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 240 with h | h
        · exact schOK_rec (a0 := 235) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_47 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 245 with h | h
        · exact schOK_rec (a0 := 240) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_48 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 250 with h | h
        · exact schOK_rec (a0 := 245) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_49 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 250) (cnt := 5) (lo := 9) (hi := 11) CFSG.KD.YMS432C.s0_50 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 126 at ha
        change 11 ≤ j at hj1
        change j < 14 at hj2
        rcases Nat.lt_or_ge a 3 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 6 with h | h
        · exact schOK_rec (a0 := 3) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_1 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 9 with h | h
        · exact schOK_rec (a0 := 6) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_2 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 12 with h | h
        · exact schOK_rec (a0 := 9) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_3 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 15 with h | h
        · exact schOK_rec (a0 := 12) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_4 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 18 with h | h
        · exact schOK_rec (a0 := 15) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_5 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 21 with h | h
        · exact schOK_rec (a0 := 18) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_6 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 24 with h | h
        · exact schOK_rec (a0 := 21) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_7 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 27 with h | h
        · exact schOK_rec (a0 := 24) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_8 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 30 with h | h
        · exact schOK_rec (a0 := 27) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_9 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 33 with h | h
        · exact schOK_rec (a0 := 30) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_10 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 36 with h | h
        · exact schOK_rec (a0 := 33) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_11 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 39 with h | h
        · exact schOK_rec (a0 := 36) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_12 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 42 with h | h
        · exact schOK_rec (a0 := 39) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_13 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 45 with h | h
        · exact schOK_rec (a0 := 42) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_14 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 48 with h | h
        · exact schOK_rec (a0 := 45) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_15 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 51 with h | h
        · exact schOK_rec (a0 := 48) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_16 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 54 with h | h
        · exact schOK_rec (a0 := 51) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_17 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 57 with h | h
        · exact schOK_rec (a0 := 54) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_18 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 60 with h | h
        · exact schOK_rec (a0 := 57) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_19 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 63 with h | h
        · exact schOK_rec (a0 := 60) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_20 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 66 with h | h
        · exact schOK_rec (a0 := 63) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_21 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 69 with h | h
        · exact schOK_rec (a0 := 66) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_22 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 72 with h | h
        · exact schOK_rec (a0 := 69) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_23 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 75 with h | h
        · exact schOK_rec (a0 := 72) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_24 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 78 with h | h
        · exact schOK_rec (a0 := 75) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_25 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 81 with h | h
        · exact schOK_rec (a0 := 78) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_26 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 84 with h | h
        · exact schOK_rec (a0 := 81) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_27 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 87 with h | h
        · exact schOK_rec (a0 := 84) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_28 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 90 with h | h
        · exact schOK_rec (a0 := 87) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_29 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 93 with h | h
        · exact schOK_rec (a0 := 90) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_30 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 96 with h | h
        · exact schOK_rec (a0 := 93) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_31 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 99 with h | h
        · exact schOK_rec (a0 := 96) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_32 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 102 with h | h
        · exact schOK_rec (a0 := 99) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_33 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 105 with h | h
        · exact schOK_rec (a0 := 102) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_34 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 108 with h | h
        · exact schOK_rec (a0 := 105) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_35 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 111 with h | h
        · exact schOK_rec (a0 := 108) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_36 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 114 with h | h
        · exact schOK_rec (a0 := 111) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_37 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 117 with h | h
        · exact schOK_rec (a0 := 114) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_38 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 120 with h | h
        · exact schOK_rec (a0 := 117) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_39 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 123 with h | h
        · exact schOK_rec (a0 := 120) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_40 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 123) (cnt := 3) (lo := 11) (hi := 14) CFSG.KD.YMS432C.s1_41 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 60 at ha
        change 14 ≤ j at hj1
        change j < 19 at hj2
        rcases Nat.lt_or_ge a 2 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 4 with h | h
        · exact schOK_rec (a0 := 2) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_1 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 6 with h | h
        · exact schOK_rec (a0 := 4) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_2 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 8 with h | h
        · exact schOK_rec (a0 := 6) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_3 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 10 with h | h
        · exact schOK_rec (a0 := 8) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_4 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 12 with h | h
        · exact schOK_rec (a0 := 10) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_5 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 14 with h | h
        · exact schOK_rec (a0 := 12) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_6 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 16 with h | h
        · exact schOK_rec (a0 := 14) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_7 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 18 with h | h
        · exact schOK_rec (a0 := 16) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_8 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 20 with h | h
        · exact schOK_rec (a0 := 18) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_9 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 22 with h | h
        · exact schOK_rec (a0 := 20) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_10 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 24 with h | h
        · exact schOK_rec (a0 := 22) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_11 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 26 with h | h
        · exact schOK_rec (a0 := 24) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_12 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 28 with h | h
        · exact schOK_rec (a0 := 26) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_13 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 30 with h | h
        · exact schOK_rec (a0 := 28) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_14 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 32 with h | h
        · exact schOK_rec (a0 := 30) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_15 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 34 with h | h
        · exact schOK_rec (a0 := 32) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_16 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 36 with h | h
        · exact schOK_rec (a0 := 34) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_17 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 38 with h | h
        · exact schOK_rec (a0 := 36) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_18 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 40 with h | h
        · exact schOK_rec (a0 := 38) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_19 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 42 with h | h
        · exact schOK_rec (a0 := 40) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_20 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 44 with h | h
        · exact schOK_rec (a0 := 42) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_21 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 46 with h | h
        · exact schOK_rec (a0 := 44) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_22 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 48 with h | h
        · exact schOK_rec (a0 := 46) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_23 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 50 with h | h
        · exact schOK_rec (a0 := 48) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_24 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 52 with h | h
        · exact schOK_rec (a0 := 50) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_25 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 54 with h | h
        · exact schOK_rec (a0 := 52) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_26 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 56 with h | h
        · exact schOK_rec (a0 := 54) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_27 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 58 with h | h
        · exact schOK_rec (a0 := 56) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_28 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 58) (cnt := 2) (lo := 14) (hi := 19) CFSG.KD.YMS432C.s2_29 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 24 at ha
        change 19 ≤ j at hj1
        change j < 28 at hj2
        rcases Nat.lt_or_ge a 1 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2 with h | h
        · exact schOK_rec (a0 := 1) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_1 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3 with h | h
        · exact schOK_rec (a0 := 2) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_2 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 4 with h | h
        · exact schOK_rec (a0 := 3) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_3 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 5 with h | h
        · exact schOK_rec (a0 := 4) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_4 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 6 with h | h
        · exact schOK_rec (a0 := 5) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_5 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 7 with h | h
        · exact schOK_rec (a0 := 6) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_6 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 8 with h | h
        · exact schOK_rec (a0 := 7) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_7 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 9 with h | h
        · exact schOK_rec (a0 := 8) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_8 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 10 with h | h
        · exact schOK_rec (a0 := 9) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_9 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 11 with h | h
        · exact schOK_rec (a0 := 10) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_10 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 12 with h | h
        · exact schOK_rec (a0 := 11) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_11 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 13 with h | h
        · exact schOK_rec (a0 := 12) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_12 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 14 with h | h
        · exact schOK_rec (a0 := 13) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_13 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 15 with h | h
        · exact schOK_rec (a0 := 14) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_14 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 16 with h | h
        · exact schOK_rec (a0 := 15) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_15 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 17 with h | h
        · exact schOK_rec (a0 := 16) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_16 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 18 with h | h
        · exact schOK_rec (a0 := 17) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_17 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 19 with h | h
        · exact schOK_rec (a0 := 18) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_18 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 20 with h | h
        · exact schOK_rec (a0 := 19) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_19 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 21 with h | h
        · exact schOK_rec (a0 := 20) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_20 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 22 with h | h
        · exact schOK_rec (a0 := 21) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_21 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 23 with h | h
        · exact schOK_rec (a0 := 22) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_22 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 23) (cnt := 1) (lo := 19) (hi := 28) CFSG.KD.YMS432C.s3_23 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 16 at ha
        change 28 ≤ j at hj1
        change j < 40 at hj2
        rcases Nat.lt_or_ge a 1 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2 with h | h
        · exact schOK_rec (a0 := 1) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_1 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3 with h | h
        · exact schOK_rec (a0 := 2) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_2 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 4 with h | h
        · exact schOK_rec (a0 := 3) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_3 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 5 with h | h
        · exact schOK_rec (a0 := 4) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_4 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 6 with h | h
        · exact schOK_rec (a0 := 5) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_5 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 7 with h | h
        · exact schOK_rec (a0 := 6) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_6 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 8 with h | h
        · exact schOK_rec (a0 := 7) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_7 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 9 with h | h
        · exact schOK_rec (a0 := 8) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_8 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 10 with h | h
        · exact schOK_rec (a0 := 9) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_9 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 11 with h | h
        · exact schOK_rec (a0 := 10) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_10 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 12 with h | h
        · exact schOK_rec (a0 := 11) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_11 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 13 with h | h
        · exact schOK_rec (a0 := 12) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_12 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 14 with h | h
        · exact schOK_rec (a0 := 13) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_13 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 15 with h | h
        · exact schOK_rec (a0 := 14) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_14 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 15) (cnt := 1) (lo := 28) (hi := 40) CFSG.KD.YMS432C.s4_15 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 8 at ha
        change 40 ≤ j at hj1
        change j < 48 at hj2
        rcases Nat.lt_or_ge a 1 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 1) (lo := 40) (hi := 48) CFSG.KD.YMS432C.s5_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 2 with h | h
        · exact schOK_rec (a0 := 1) (cnt := 1) (lo := 40) (hi := 48) CFSG.KD.YMS432C.s5_1 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 3 with h | h
        · exact schOK_rec (a0 := 2) (cnt := 1) (lo := 40) (hi := 48) CFSG.KD.YMS432C.s5_2 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 4 with h | h
        · exact schOK_rec (a0 := 3) (cnt := 1) (lo := 40) (hi := 48) CFSG.KD.YMS432C.s5_3 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 5 with h | h
        · exact schOK_rec (a0 := 4) (cnt := 1) (lo := 40) (hi := 48) CFSG.KD.YMS432C.s5_4 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 6 with h | h
        · exact schOK_rec (a0 := 5) (cnt := 1) (lo := 40) (hi := 48) CFSG.KD.YMS432C.s5_5 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 7 with h | h
        · exact schOK_rec (a0 := 6) (cnt := 1) (lo := 40) (hi := 48) CFSG.KD.YMS432C.s5_6 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 7) (cnt := 1) (lo := 40) (hi := 48) CFSG.KD.YMS432C.s5_7 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 2 at ha
        change 48 ≤ j at hj1
        change j < 53 at hj2
        exact schOK_rec (a0 := 0) (cnt := 2) (lo := 48) (hi := 53) CFSG.KD.YMS432C.s6_0 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 2 at ha
        change 53 ≤ j at hj1
        change j < 57 at hj2
        exact schOK_rec (a0 := 0) (cnt := 2) (lo := 53) (hi := 57) CFSG.KD.YMS432C.s7_0 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 2 at ha
        change 57 ≤ j at hj1
        change j < 60 at hj2
        exact schOK_rec (a0 := 0) (cnt := 2) (lo := 57) (hi := 60) CFSG.KD.YMS432C.s8_0 (by decide) a
          (by omega) (by omega) j hj1 hj2
      )
    (by
      intro c hc
      interval_cases c
      exacts [⟨CFSG.KD.YMS432C.lw0, CFSG.KD.YMS432C.lc0⟩, ⟨CFSG.KD.YMS432C.lw1, CFSG.KD.YMS432C.lc1⟩, ⟨CFSG.KD.YMS432C.lw2, CFSG.KD.YMS432C.lc2⟩, ⟨CFSG.KD.YMS432C.lw3, CFSG.KD.YMS432C.lc3⟩, ⟨CFSG.KD.YMS432C.lw4, CFSG.KD.YMS432C.lc4⟩, ⟨CFSG.KD.YMS432C.lw5, CFSG.KD.YMS432C.lc5⟩, ⟨CFSG.KD.YMS432C.lw6, CFSG.KD.YMS432C.lc6⟩, ⟨CFSG.KD.YMS432C.lw7, CFSG.KD.YMS432C.lc7⟩, ⟨CFSG.KD.YMS432C.lw8, CFSG.KD.YMS432C.lc8⟩])
  rw [h]
  decide

end CertificateChecks.KernelYModel

end
