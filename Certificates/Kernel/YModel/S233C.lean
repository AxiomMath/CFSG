module

public import Certificates.Kernel.YModel.Basic
public import CFSG.Certificates.Kernel.YModel.S233C.Data
import CFSG.Certificates.Kernel.YModel.S233C.CheckL
import CFSG.Certificates.Kernel.YModel.S233C.CheckG
import CFSG.Certificates.Kernel.YModel.S233C.CheckP
import CFSG.Certificates.Kernel.YModel.S233C.CheckT
import CFSG.Certificates.Kernel.YModel.S233C.CheckS0

public section

namespace CertificateChecks.KernelYModel

open CFSG.KC.YModel

set_option maxRecDepth 100000

theorem s233C_card : Nat.card (CFSG.YGroups.arrClosure 3510 (linesA (fun _ => 3510) 32 CFSG.KD.YMS233C.LF 8)) =
    92897280 := by
  have h := card_arrClosure_of_sch (k := 12) (n := 3510) (m := 8) (w := 8) (t := 7)
    (F := CFSG.KD.YMS233C.LF) (Nf := CFSG.KD.YMS233C.Nf) (U := CFSG.KD.YMS233C.U) (WP := CFSG.KD.YMS233C.GP) (WL := CFSG.KD.YMS233C.GL) (TT := CFSG.KD.YMS233C.TT)
    (off := CFSG.KC.YModel.lget [8, 13, 19, 26, 33, 40, 44, 47]) (bp := CFSG.KC.YModel.lget [0, 1, 2, 3, 5, 9, 12]) (Z := CFSG.KC.YModel.lget [126, 64, 30, 12, 8, 2, 2])
    (LP := CFSG.KC.YModel.lget [5654558, 79285634339350, 24288401374319636, 1447569448, 86, 369839054354, 64, 94]) (LL := CFSG.KC.YModel.lget [3, 6, 7, 4, 1, 5, 1, 1])
    (by intro c hc; interval_cases c; exacts [CFSG.KD.YMS233C.l0, CFSG.KD.YMS233C.l1, CFSG.KD.YMS233C.l2, CFSG.KD.YMS233C.l3, CFSG.KD.YMS233C.l4, CFSG.KD.YMS233C.l5, CFSG.KD.YMS233C.l6, CFSG.KD.YMS233C.l7])
    (by intro c hc; interval_cases c <;> rfl)
    rfl (by decide)
    (by
      intro j h1 h2
      change 8 ≤ j at h1
      change j < 13 at h2
      interval_cases j
      exacts [CFSG.KD.YMS233C.g8, CFSG.KD.YMS233C.g9, CFSG.KD.YMS233C.g10, CFSG.KD.YMS233C.g11, CFSG.KD.YMS233C.g12])
    (by
      intro i hi1 hi2
      interval_cases i
      · intro j h1 h2
        change 13 ≤ j at h1
        change j < 19 at h2
        interval_cases j
        exacts [CFSG.KD.YMS233C.g13, CFSG.KD.YMS233C.g14, CFSG.KD.YMS233C.g15, CFSG.KD.YMS233C.g16, CFSG.KD.YMS233C.g17, CFSG.KD.YMS233C.g18]
      · intro j h1 h2
        change 19 ≤ j at h1
        change j < 26 at h2
        interval_cases j
        exacts [CFSG.KD.YMS233C.g19, CFSG.KD.YMS233C.g20, CFSG.KD.YMS233C.g21, CFSG.KD.YMS233C.g22, CFSG.KD.YMS233C.g23, CFSG.KD.YMS233C.g24, CFSG.KD.YMS233C.g25]
      · intro j h1 h2
        change 26 ≤ j at h1
        change j < 33 at h2
        interval_cases j
        exacts [CFSG.KD.YMS233C.g26, CFSG.KD.YMS233C.g27, CFSG.KD.YMS233C.g28, CFSG.KD.YMS233C.g29, CFSG.KD.YMS233C.g30, CFSG.KD.YMS233C.g31, CFSG.KD.YMS233C.g32]
      · intro j h1 h2
        change 33 ≤ j at h1
        change j < 40 at h2
        interval_cases j
        exacts [CFSG.KD.YMS233C.g33, CFSG.KD.YMS233C.g34, CFSG.KD.YMS233C.g35, CFSG.KD.YMS233C.g36, CFSG.KD.YMS233C.g37, CFSG.KD.YMS233C.g38, CFSG.KD.YMS233C.g39]
      · intro j h1 h2
        change 40 ≤ j at h1
        change j < 44 at h2
        interval_cases j
        exacts [CFSG.KD.YMS233C.g40, CFSG.KD.YMS233C.g41, CFSG.KD.YMS233C.g42, CFSG.KD.YMS233C.g43]
      · intro j h1 h2
        change 44 ≤ j at h1
        change j < 47 at h2
        interval_cases j
        exacts [CFSG.KD.YMS233C.g44, CFSG.KD.YMS233C.g45, CFSG.KD.YMS233C.g46]
      )
    (by intro i hi; interval_cases i <;> decide)
    (by
      intro i hi
      interval_cases i
      exacts [⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS233C.b0, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS233C.b1, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS233C.b2, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS233C.b3, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS233C.b4, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS233C.b5, by decide⟩, ⟨Nat.eq_of_beq_eq_true CFSG.KD.YMS233C.b6, by decide⟩])
    (by intro i hi; interval_cases i; exacts [CFSG.KD.YMS233C.p0, CFSG.KD.YMS233C.p1, CFSG.KD.YMS233C.p2, CFSG.KD.YMS233C.p3, CFSG.KD.YMS233C.p4, CFSG.KD.YMS233C.p5, CFSG.KD.YMS233C.p6])
    (by
      intro i hi
      interval_cases i
      · intro a ha
        change a < 126 at ha
        rcases Nat.lt_or_ge a 64 with h | h
        · exact transOK_point (a0 := 0) (cnt := 64) CFSG.KD.YMS233C.t0_0 a (by omega) (by omega)
        exact transOK_point (a0 := 64) (cnt := 62) CFSG.KD.YMS233C.t0_1 a (by omega) (by omega)
      · intro a ha
        change a < 64 at ha
        exact transOK_point (a0 := 0) (cnt := 64) CFSG.KD.YMS233C.t1_0 a (by omega) (by omega)
      · intro a ha
        change a < 30 at ha
        exact transOK_point (a0 := 0) (cnt := 30) CFSG.KD.YMS233C.t2_0 a (by omega) (by omega)
      · intro a ha
        change a < 12 at ha
        exact transOK_point (a0 := 0) (cnt := 12) CFSG.KD.YMS233C.t3_0 a (by omega) (by omega)
      · intro a ha
        change a < 8 at ha
        exact transOK_point (a0 := 0) (cnt := 8) CFSG.KD.YMS233C.t4_0 a (by omega) (by omega)
      · intro a ha
        change a < 2 at ha
        exact transOK_point (a0 := 0) (cnt := 2) CFSG.KD.YMS233C.t5_0 a (by omega) (by omega)
      · intro a ha
        change a < 2 at ha
        exact transOK_point (a0 := 0) (cnt := 2) CFSG.KD.YMS233C.t6_0 a (by omega) (by omega)
      )
    (by
      intro i hi
      interval_cases i
      · intro a ha j hj1 hj2
        change a < 126 at ha
        change 8 ≤ j at hj1
        change j < 13 at hj2
        rcases Nat.lt_or_ge a 12 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 12) (lo := 8) (hi := 13) CFSG.KD.YMS233C.s0_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 24 with h | h
        · exact schOK_rec (a0 := 12) (cnt := 12) (lo := 8) (hi := 13) CFSG.KD.YMS233C.s0_1 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 36 with h | h
        · exact schOK_rec (a0 := 24) (cnt := 12) (lo := 8) (hi := 13) CFSG.KD.YMS233C.s0_2 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 48 with h | h
        · exact schOK_rec (a0 := 36) (cnt := 12) (lo := 8) (hi := 13) CFSG.KD.YMS233C.s0_3 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 60 with h | h
        · exact schOK_rec (a0 := 48) (cnt := 12) (lo := 8) (hi := 13) CFSG.KD.YMS233C.s0_4 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 72 with h | h
        · exact schOK_rec (a0 := 60) (cnt := 12) (lo := 8) (hi := 13) CFSG.KD.YMS233C.s0_5 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 84 with h | h
        · exact schOK_rec (a0 := 72) (cnt := 12) (lo := 8) (hi := 13) CFSG.KD.YMS233C.s0_6 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 96 with h | h
        · exact schOK_rec (a0 := 84) (cnt := 12) (lo := 8) (hi := 13) CFSG.KD.YMS233C.s0_7 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 108 with h | h
        · exact schOK_rec (a0 := 96) (cnt := 12) (lo := 8) (hi := 13) CFSG.KD.YMS233C.s0_8 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 120 with h | h
        · exact schOK_rec (a0 := 108) (cnt := 12) (lo := 8) (hi := 13) CFSG.KD.YMS233C.s0_9 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 120) (cnt := 6) (lo := 8) (hi := 13) CFSG.KD.YMS233C.s0_10 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 64 at ha
        change 13 ≤ j at hj1
        change j < 19 at hj2
        rcases Nat.lt_or_ge a 10 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 10) (lo := 13) (hi := 19) CFSG.KD.YMS233C.s1_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 20 with h | h
        · exact schOK_rec (a0 := 10) (cnt := 10) (lo := 13) (hi := 19) CFSG.KD.YMS233C.s1_1 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 30 with h | h
        · exact schOK_rec (a0 := 20) (cnt := 10) (lo := 13) (hi := 19) CFSG.KD.YMS233C.s1_2 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 40 with h | h
        · exact schOK_rec (a0 := 30) (cnt := 10) (lo := 13) (hi := 19) CFSG.KD.YMS233C.s1_3 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 50 with h | h
        · exact schOK_rec (a0 := 40) (cnt := 10) (lo := 13) (hi := 19) CFSG.KD.YMS233C.s1_4 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 60 with h | h
        · exact schOK_rec (a0 := 50) (cnt := 10) (lo := 13) (hi := 19) CFSG.KD.YMS233C.s1_5 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 60) (cnt := 4) (lo := 13) (hi := 19) CFSG.KD.YMS233C.s1_6 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 30 at ha
        change 19 ≤ j at hj1
        change j < 26 at hj2
        rcases Nat.lt_or_ge a 8 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 8) (lo := 19) (hi := 26) CFSG.KD.YMS233C.s2_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 16 with h | h
        · exact schOK_rec (a0 := 8) (cnt := 8) (lo := 19) (hi := 26) CFSG.KD.YMS233C.s2_1 (by decide) a
            (by omega) (by omega) j hj1 hj2
        rcases Nat.lt_or_ge a 24 with h | h
        · exact schOK_rec (a0 := 16) (cnt := 8) (lo := 19) (hi := 26) CFSG.KD.YMS233C.s2_2 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 24) (cnt := 6) (lo := 19) (hi := 26) CFSG.KD.YMS233C.s2_3 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 12 at ha
        change 26 ≤ j at hj1
        change j < 33 at hj2
        rcases Nat.lt_or_ge a 8 with h | h
        · exact schOK_rec (a0 := 0) (cnt := 8) (lo := 26) (hi := 33) CFSG.KD.YMS233C.s3_0 (by decide) a
            (by omega) (by omega) j hj1 hj2
        exact schOK_rec (a0 := 8) (cnt := 4) (lo := 26) (hi := 33) CFSG.KD.YMS233C.s3_1 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 8 at ha
        change 33 ≤ j at hj1
        change j < 40 at hj2
        exact schOK_rec (a0 := 0) (cnt := 8) (lo := 33) (hi := 40) CFSG.KD.YMS233C.s4_0 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 2 at ha
        change 40 ≤ j at hj1
        change j < 44 at hj2
        exact schOK_rec (a0 := 0) (cnt := 2) (lo := 40) (hi := 44) CFSG.KD.YMS233C.s5_0 (by decide) a
          (by omega) (by omega) j hj1 hj2
      · intro a ha j hj1 hj2
        change a < 2 at ha
        change 44 ≤ j at hj1
        change j < 47 at hj2
        exact schOK_rec (a0 := 0) (cnt := 2) (lo := 44) (hi := 47) CFSG.KD.YMS233C.s6_0 (by decide) a
          (by omega) (by omega) j hj1 hj2
      )
    (by
      intro c hc
      interval_cases c
      exacts [⟨CFSG.KD.YMS233C.lw0, CFSG.KD.YMS233C.lc0⟩, ⟨CFSG.KD.YMS233C.lw1, CFSG.KD.YMS233C.lc1⟩, ⟨CFSG.KD.YMS233C.lw2, CFSG.KD.YMS233C.lc2⟩, ⟨CFSG.KD.YMS233C.lw3, CFSG.KD.YMS233C.lc3⟩, ⟨CFSG.KD.YMS233C.lw4, CFSG.KD.YMS233C.lc4⟩, ⟨CFSG.KD.YMS233C.lw5, CFSG.KD.YMS233C.lc5⟩, ⟨CFSG.KD.YMS233C.lw6, CFSG.KD.YMS233C.lc6⟩, ⟨CFSG.KD.YMS233C.lw7, CFSG.KD.YMS233C.lc7⟩])
  rw [h]
  decide

end CertificateChecks.KernelYModel

end
