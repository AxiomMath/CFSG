module

public import Certificates.Kernel.Sporadic.Fi24Pc.Data
import Certificates.Kernel.Sporadic.Fi24Net.PTabSound
import Certificates.Kernel.Sporadic.Fi24Pc.PTabSound
import CFSG.Certificates.Kernel.Common.Harness

namespace CFSG.KD.Fi24Pc.Ck

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24Pc CFSG.KC.Fi24NetPt CFSG.KD.Fi24Pc

theorem xone_of {l v0 v1 v2 v3 v4 v5 : Nat} (hg : Nat.blt (nth J.tgt l) 5 = true)
    (hn : nwOK (f32 J.RP l) = true)
    (a0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt l))
      (apP CFSG.KD.Fi24Net.letPT (nthL J.trans l) 0) = v0)
    (b0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans l)
      (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP l)) 0) = v0)
    (a1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt l))
      (apP CFSG.KD.Fi24Net.letPT (nthL J.trans l) 305530) = v1)
    (b1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans l)
      (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP l)) 305530) = v1)
    (a2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt l))
      (apP CFSG.KD.Fi24Net.letPT (nthL J.trans l) 5604) = v2)
    (b2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans l)
      (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP l)) 5604) = v2)
    (a3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt l))
      (apP CFSG.KD.Fi24Net.letPT (nthL J.trans l) 221549) = v3)
    (b3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans l)
      (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP l)) 221549) = v3)
    (a4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt l))
      (apP CFSG.KD.Fi24Net.letPT (nthL J.trans l) 266275) = v4)
    (b4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans l)
      (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP l)) 266275) = v4)
    (a5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt l))
      (apP CFSG.KD.Fi24Net.letPT (nthL J.trans l) 186844) = v5)
    (b5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans l)
      (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP l)) 186844) = v5) :
    xone l = true := by
  unfold xone transOK cb
  rw [hg, hn, ← CFSG.KD.Fi24Net.letPT_eq, ← CFSG.KD.Fi24Pc.letPX_eq]
  dsimp only
  rw [a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5]
  simp only [Nat.beq_refl]
  rfl

theorem xck_of {g : Nat}
    (h0 : xone (Nat.add (Nat.mul 8 g) 0) = true)
    (c0 : Nat.blt (Nat.add (Nat.mul 8 g) 0) 824 = true)
    (h1 : xone (Nat.add (Nat.mul 8 g) 1) = true)
    (c1 : Nat.blt (Nat.add (Nat.mul 8 g) 1) 824 = true)
    (h2 : xone (Nat.add (Nat.mul 8 g) 2) = true)
    (c2 : Nat.blt (Nat.add (Nat.mul 8 g) 2) 824 = true)
    (h3 : xone (Nat.add (Nat.mul 8 g) 3) = true)
    (c3 : Nat.blt (Nat.add (Nat.mul 8 g) 3) 824 = true)
    (h4 : xone (Nat.add (Nat.mul 8 g) 4) = true)
    (c4 : Nat.blt (Nat.add (Nat.mul 8 g) 4) 824 = true)
    (h5 : xone (Nat.add (Nat.mul 8 g) 5) = true)
    (c5 : Nat.blt (Nat.add (Nat.mul 8 g) 5) 824 = true)
    (h6 : xone (Nat.add (Nat.mul 8 g) 6) = true)
    (c6 : Nat.blt (Nat.add (Nat.mul 8 g) 6) 824 = true)
    (h7 : xone (Nat.add (Nat.mul 8 g) 7) = true)
    (c7 : Nat.blt (Nat.add (Nat.mul 8 g) 7) 824 = true) :
    xck g = true := by
  unfold xck
  change bAnd(bIf(Nat.blt (Nat.add (Nat.mul 8 g) 7) 824, xone (Nat.add (Nat.mul 8 g) 7), true),
    bAnd(bIf(Nat.blt (Nat.add (Nat.mul 8 g) 6) 824, xone (Nat.add (Nat.mul 8 g) 6), true),
    bAnd(bIf(Nat.blt (Nat.add (Nat.mul 8 g) 5) 824, xone (Nat.add (Nat.mul 8 g) 5), true),
    bAnd(bIf(Nat.blt (Nat.add (Nat.mul 8 g) 4) 824, xone (Nat.add (Nat.mul 8 g) 4), true),
    bAnd(bIf(Nat.blt (Nat.add (Nat.mul 8 g) 3) 824, xone (Nat.add (Nat.mul 8 g) 3), true),
    bAnd(bIf(Nat.blt (Nat.add (Nat.mul 8 g) 2) 824, xone (Nat.add (Nat.mul 8 g) 2), true),
    bAnd(bIf(Nat.blt (Nat.add (Nat.mul 8 g) 1) 824, xone (Nat.add (Nat.mul 8 g) 1), true),
    bAnd(bIf(Nat.blt (Nat.add (Nat.mul 8 g) 0) 824, xone (Nat.add (Nat.mul 8 g) 0), true),
    true)))))))) = true
  rw [c0, h0, c1, h1, c2, h2, c3, h3, c4, h4, c5, h5, c6, h6, c7, h7]

theorem a0_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 0))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 0) 0) = 134591 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b0_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 0)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 0)) 0) = 134591 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a0_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 0))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 0) 305530) = 269346 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b0_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 0)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 0)) 305530) = 269346 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a0_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 0))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 0) 5604) = 11054 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b0_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 0)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 0)) 5604) = 11054 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a0_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 0))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 0) 221549) = 50339 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b0_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 0)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 0)) 221549) = 50339 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a0_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 0))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 0) 266275) = 12397 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b0_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 0)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 0)) 266275) = 12397 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a0_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 0))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 0) 186844) = 256448 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b0_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 0)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 0)) 186844) = 256448 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o0 : xone 0 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a0_0 b0_0 a0_1 b0_1 a0_2 b0_2
    a0_3 b0_3 a0_4 b0_4 a0_5 b0_5

theorem a1_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 1))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 1) 0) = 216660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b1_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 1)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 1)) 0) = 216660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a1_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 1))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 1) 305530) = 106319 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b1_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 1)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 1)) 305530) = 106319 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a1_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 1))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 1) 5604) = 70175 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b1_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 1)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 1)) 5604) = 70175 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a1_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 1))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 1) 221549) = 78807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b1_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 1)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 1)) 221549) = 78807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a1_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 1))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 1) 266275) = 169487 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b1_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 1)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 1)) 266275) = 169487 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a1_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 1))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 1) 186844) = 128219 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b1_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 1)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 1)) 186844) = 128219 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o1 : xone 1 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a1_0 b1_0 a1_1 b1_1 a1_2 b1_2
    a1_3 b1_3 a1_4 b1_4 a1_5 b1_5

theorem a2_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 2))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 2) 0) = 141083 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b2_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 2)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 2)) 0) = 141083 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a2_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 2))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 2) 305530) = 89226 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b2_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 2)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 2)) 305530) = 89226 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a2_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 2))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 2) 5604) = 22874 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b2_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 2)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 2)) 5604) = 22874 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a2_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 2))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 2) 221549) = 44283 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b2_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 2)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 2)) 221549) = 44283 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a2_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 2))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 2) 266275) = 57211 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b2_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 2)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 2)) 266275) = 57211 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a2_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 2))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 2) 186844) = 73850 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b2_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 2)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 2)) 186844) = 73850 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o2 : xone 2 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a2_0 b2_0 a2_1 b2_1 a2_2 b2_2
    a2_3 b2_3 a2_4 b2_4 a2_5 b2_5

theorem a3_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 3))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 3) 0) = 67096 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b3_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 3)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 3)) 0) = 67096 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a3_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 3))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 3) 305530) = 59705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b3_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 3)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 3)) 305530) = 59705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a3_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 3))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 3) 5604) = 183488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b3_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 3)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 3)) 5604) = 183488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a3_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 3))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 3) 221549) = 273462 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b3_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 3)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 3)) 221549) = 273462 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a3_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 3))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 3) 266275) = 124148 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b3_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 3)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 3)) 266275) = 124148 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a3_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 3))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 3) 186844) = 283311 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b3_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 3)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 3)) 186844) = 283311 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o3 : xone 3 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a3_0 b3_0 a3_1 b3_1 a3_2 b3_2
    a3_3 b3_3 a3_4 b3_4 a3_5 b3_5

theorem a4_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 4))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 4) 0) = 258139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b4_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 4)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 4)) 0) = 258139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a4_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 4))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 4) 305530) = 85742 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b4_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 4)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 4)) 305530) = 85742 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a4_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 4))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 4) 5604) = 32676 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b4_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 4)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 4)) 5604) = 32676 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a4_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 4))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 4) 221549) = 43109 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b4_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 4)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 4)) 221549) = 43109 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a4_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 4))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 4) 266275) = 101048 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b4_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 4)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 4)) 266275) = 101048 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a4_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 4))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 4) 186844) = 113297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b4_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 4)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 4)) 186844) = 113297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o4 : xone 4 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a4_0 b4_0 a4_1 b4_1 a4_2 b4_2
    a4_3 b4_3 a4_4 b4_4 a4_5 b4_5

theorem a5_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 5))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 5) 0) = 76722 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b5_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 5)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 5)) 0) = 76722 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a5_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 5))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 5) 305530) = 58448 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b5_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 5)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 5)) 305530) = 58448 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a5_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 5))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 5) 5604) = 146978 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b5_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 5)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 5)) 5604) = 146978 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a5_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 5))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 5) 221549) = 187075 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b5_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 5)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 5)) 221549) = 187075 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a5_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 5))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 5) 266275) = 173504 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b5_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 5)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 5)) 266275) = 173504 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a5_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 5))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 5) 186844) = 94679 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b5_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 5)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 5)) 186844) = 94679 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o5 : xone 5 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a5_0 b5_0 a5_1 b5_1 a5_2 b5_2
    a5_3 b5_3 a5_4 b5_4 a5_5 b5_5

theorem a6_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 6))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 6) 0) = 290050 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b6_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 6)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 6)) 0) = 290050 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a6_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 6))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 6) 305530) = 98977 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b6_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 6)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 6)) 305530) = 98977 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a6_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 6))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 6) 5604) = 13929 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b6_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 6)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 6)) 5604) = 13929 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a6_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 6))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 6) 221549) = 265565 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b6_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 6)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 6)) 221549) = 265565 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a6_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 6))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 6) 266275) = 73173 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b6_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 6)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 6)) 266275) = 73173 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a6_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 6))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 6) 186844) = 132965 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b6_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 6)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 6)) 186844) = 132965 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o6 : xone 6 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a6_0 b6_0 a6_1 b6_1 a6_2 b6_2
    a6_3 b6_3 a6_4 b6_4 a6_5 b6_5

theorem a7_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 7))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 7) 0) = 273421 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b7_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 7)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 7)) 0) = 273421 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a7_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 7))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 7) 305530) = 201985 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b7_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 7)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 7)) 305530) = 201985 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a7_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 7))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 7) 5604) = 250366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b7_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 7)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 7)) 5604) = 250366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a7_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 7))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 7) 221549) = 176886 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b7_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 7)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 7)) 221549) = 176886 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a7_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 7))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 7) 266275) = 170270 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b7_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 7)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 7)) 266275) = 170270 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a7_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 7))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 7) 186844) = 170680 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b7_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 7)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 7)) 186844) = 170680 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o7 : xone 7 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a7_0 b7_0 a7_1 b7_1 a7_2 b7_2
    a7_3 b7_3 a7_4 b7_4 a7_5 b7_5

theorem a8_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 8))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 8) 0) = 159116 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b8_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 8)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 8)) 0) = 159116 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a8_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 8))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 8) 305530) = 110012 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b8_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 8)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 8)) 305530) = 110012 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a8_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 8))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 8) 5604) = 37668 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b8_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 8)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 8)) 5604) = 37668 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a8_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 8))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 8) 221549) = 150461 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b8_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 8)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 8)) 221549) = 150461 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a8_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 8))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 8) 266275) = 119235 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b8_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 8)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 8)) 266275) = 119235 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a8_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 8))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 8) 186844) = 293512 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b8_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 8)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 8)) 186844) = 293512 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o8 : xone 8 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a8_0 b8_0 a8_1 b8_1 a8_2 b8_2
    a8_3 b8_3 a8_4 b8_4 a8_5 b8_5

theorem a9_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 9))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 9) 0) = 128020 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b9_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 9)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 9)) 0) = 128020 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a9_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 9))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 9) 305530) = 78716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b9_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 9)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 9)) 305530) = 78716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a9_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 9))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 9) 5604) = 210812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b9_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 9)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 9)) 5604) = 210812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a9_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 9))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 9) 221549) = 10751 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b9_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 9)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 9)) 221549) = 10751 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a9_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 9))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 9) 266275) = 244372 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b9_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 9)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 9)) 266275) = 244372 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a9_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 9))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 9) 186844) = 107791 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b9_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 9)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 9)) 186844) = 107791 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o9 : xone 9 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a9_0 b9_0 a9_1 b9_1 a9_2 b9_2
    a9_3 b9_3 a9_4 b9_4 a9_5 b9_5

theorem a10_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 10))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 10) 0) = 208093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b10_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 10)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 10)) 0) = 208093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a10_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 10))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 10) 305530) = 51177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b10_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 10)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 10)) 305530) = 51177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a10_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 10))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 10) 5604) = 213631 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b10_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 10)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 10)) 5604) = 213631 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a10_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 10))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 10) 221549) = 97936 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b10_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 10)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 10)) 221549) = 97936 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a10_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 10))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 10) 266275) = 116797 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b10_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 10)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 10)) 266275) = 116797 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a10_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 10))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 10) 186844) = 297858 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b10_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 10)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 10)) 186844) = 297858 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o10 : xone 10 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a10_0 b10_0 a10_1 b10_1 a10_2 b10_2
    a10_3 b10_3 a10_4 b10_4 a10_5 b10_5

theorem a11_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 11))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 11) 0) = 23391 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b11_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 11)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 11)) 0) = 23391 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a11_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 11))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 11) 305530) = 37881 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b11_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 11)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 11)) 305530) = 37881 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a11_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 11))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 11) 5604) = 277998 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b11_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 11)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 11)) 5604) = 277998 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a11_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 11))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 11) 221549) = 194789 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b11_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 11)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 11)) 221549) = 194789 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a11_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 11))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 11) 266275) = 292608 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b11_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 11)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 11)) 266275) = 292608 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a11_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 11))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 11) 186844) = 164315 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b11_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 11)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 11)) 186844) = 164315 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o11 : xone 11 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a11_0 b11_0 a11_1 b11_1 a11_2 b11_2
    a11_3 b11_3 a11_4 b11_4 a11_5 b11_5

theorem a12_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 12))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 12) 0) = 284732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b12_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 12)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 12)) 0) = 284732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a12_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 12))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 12) 305530) = 160906 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b12_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 12)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 12)) 305530) = 160906 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a12_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 12))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 12) 5604) = 21429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b12_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 12)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 12)) 5604) = 21429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a12_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 12))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 12) 221549) = 301530 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b12_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 12)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 12)) 221549) = 301530 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a12_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 12))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 12) 266275) = 64181 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b12_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 12)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 12)) 266275) = 64181 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a12_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 12))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 12) 186844) = 191453 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b12_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 12)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 12)) 186844) = 191453 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o12 : xone 12 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a12_0 b12_0 a12_1 b12_1 a12_2 b12_2
    a12_3 b12_3 a12_4 b12_4 a12_5 b12_5

theorem a13_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 13))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 13) 0) = 256242 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b13_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 13)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 13)) 0) = 256242 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a13_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 13))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 13) 305530) = 172121 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b13_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 13)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 13)) 305530) = 172121 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a13_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 13))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 13) 5604) = 272953 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b13_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 13)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 13)) 5604) = 272953 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a13_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 13))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 13) 221549) = 121631 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b13_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 13)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 13)) 221549) = 121631 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a13_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 13))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 13) 266275) = 96937 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b13_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 13)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 13)) 266275) = 96937 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a13_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 13))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 13) 186844) = 131092 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b13_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 13)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 13)) 186844) = 131092 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o13 : xone 13 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a13_0 b13_0 a13_1 b13_1 a13_2 b13_2
    a13_3 b13_3 a13_4 b13_4 a13_5 b13_5

theorem a14_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 14))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 14) 0) = 305061 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b14_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 14)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 14)) 0) = 305061 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a14_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 14))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 14) 305530) = 249170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b14_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 14)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 14)) 305530) = 249170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a14_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 14))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 14) 5604) = 119309 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b14_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 14)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 14)) 5604) = 119309 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a14_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 14))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 14) 221549) = 155402 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b14_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 14)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 14)) 221549) = 155402 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a14_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 14))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 14) 266275) = 218574 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b14_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 14)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 14)) 266275) = 218574 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a14_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 14))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 14) 186844) = 41430 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b14_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 14)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 14)) 186844) = 41430 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o14 : xone 14 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a14_0 b14_0 a14_1 b14_1 a14_2 b14_2
    a14_3 b14_3 a14_4 b14_4 a14_5 b14_5

theorem a15_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 15))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 15) 0) = 173198 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b15_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 15)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 15)) 0) = 173198 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a15_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 15))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 15) 305530) = 86485 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b15_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 15)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 15)) 305530) = 86485 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a15_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 15))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 15) 5604) = 31628 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b15_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 15)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 15)) 5604) = 31628 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a15_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 15))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 15) 221549) = 218086 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b15_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 15)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 15)) 221549) = 218086 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a15_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 15))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 15) 266275) = 148428 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b15_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 15)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 15)) 266275) = 148428 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a15_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 15))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 15) 186844) = 225700 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b15_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 15)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 15)) 186844) = 225700 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o15 : xone 15 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a15_0 b15_0 a15_1 b15_1 a15_2 b15_2
    a15_3 b15_3 a15_4 b15_4 a15_5 b15_5

theorem a16_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 16))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 16) 0) = 91534 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b16_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 16)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 16)) 0) = 91534 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a16_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 16))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 16) 305530) = 58048 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b16_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 16)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 16)) 305530) = 58048 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a16_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 16))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 16) 5604) = 159299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b16_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 16)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 16)) 5604) = 159299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a16_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 16))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 16) 221549) = 8652 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b16_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 16)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 16)) 221549) = 8652 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a16_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 16))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 16) 266275) = 98837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b16_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 16)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 16)) 266275) = 98837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a16_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 16))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 16) 186844) = 159877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b16_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 16)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 16)) 186844) = 159877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o16 : xone 16 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a16_0 b16_0 a16_1 b16_1 a16_2 b16_2
    a16_3 b16_3 a16_4 b16_4 a16_5 b16_5

theorem a17_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 17))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 17) 0) = 131499 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b17_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 17)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 17)) 0) = 131499 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a17_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 17))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 17) 305530) = 70024 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b17_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 17)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 17)) 305530) = 70024 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a17_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 17))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 17) 5604) = 49766 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b17_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 17)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 17)) 5604) = 49766 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a17_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 17))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 17) 221549) = 167421 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b17_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 17)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 17)) 221549) = 167421 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a17_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 17))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 17) 266275) = 215832 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b17_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 17)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 17)) 266275) = 215832 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a17_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 17))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 17) 186844) = 147294 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b17_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 17)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 17)) 186844) = 147294 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o17 : xone 17 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a17_0 b17_0 a17_1 b17_1 a17_2 b17_2
    a17_3 b17_3 a17_4 b17_4 a17_5 b17_5

theorem a18_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 18))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 18) 0) = 134127 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b18_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 18)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 18)) 0) = 134127 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a18_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 18))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 18) 305530) = 113084 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b18_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 18)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 18)) 305530) = 113084 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a18_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 18))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 18) 5604) = 195579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b18_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 18)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 18)) 5604) = 195579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a18_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 18))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 18) 221549) = 172731 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b18_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 18)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 18)) 221549) = 172731 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a18_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 18))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 18) 266275) = 75409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b18_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 18)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 18)) 266275) = 75409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a18_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 18))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 18) 186844) = 1518 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b18_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 18)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 18)) 186844) = 1518 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o18 : xone 18 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a18_0 b18_0 a18_1 b18_1 a18_2 b18_2
    a18_3 b18_3 a18_4 b18_4 a18_5 b18_5

theorem a19_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 19))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 19) 0) = 79924 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b19_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 19)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 19)) 0) = 79924 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a19_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 19))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 19) 305530) = 226842 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b19_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 19)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 19)) 305530) = 226842 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a19_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 19))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 19) 5604) = 113537 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b19_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 19)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 19)) 5604) = 113537 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a19_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 19))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 19) 221549) = 84540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b19_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 19)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 19)) 221549) = 84540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a19_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 19))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 19) 266275) = 254348 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b19_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 19)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 19)) 266275) = 254348 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a19_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 19))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 19) 186844) = 245655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b19_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 19)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 19)) 186844) = 245655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o19 : xone 19 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a19_0 b19_0 a19_1 b19_1 a19_2 b19_2
    a19_3 b19_3 a19_4 b19_4 a19_5 b19_5

theorem a20_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 20))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 20) 0) = 238116 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b20_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 20)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 20)) 0) = 238116 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a20_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 20))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 20) 305530) = 82368 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b20_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 20)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 20)) 305530) = 82368 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a20_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 20))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 20) 5604) = 170002 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b20_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 20)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 20)) 5604) = 170002 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a20_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 20))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 20) 221549) = 208262 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b20_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 20)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 20)) 221549) = 208262 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a20_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 20))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 20) 266275) = 37041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b20_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 20)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 20)) 266275) = 37041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a20_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 20))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 20) 186844) = 225305 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b20_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 20)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 20)) 186844) = 225305 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o20 : xone 20 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a20_0 b20_0 a20_1 b20_1 a20_2 b20_2
    a20_3 b20_3 a20_4 b20_4 a20_5 b20_5

theorem a21_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 21))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 21) 0) = 12822 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b21_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 21)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 21)) 0) = 12822 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a21_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 21))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 21) 305530) = 25084 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b21_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 21)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 21)) 305530) = 25084 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a21_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 21))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 21) 5604) = 123630 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b21_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 21)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 21)) 5604) = 123630 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a21_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 21))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 21) 221549) = 173935 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b21_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 21)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 21)) 221549) = 173935 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a21_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 21))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 21) 266275) = 208066 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b21_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 21)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 21)) 266275) = 208066 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a21_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 21))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 21) 186844) = 92150 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b21_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 21)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 21)) 186844) = 92150 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o21 : xone 21 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a21_0 b21_0 a21_1 b21_1 a21_2 b21_2
    a21_3 b21_3 a21_4 b21_4 a21_5 b21_5

theorem a22_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 22))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 22) 0) = 93801 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b22_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 22)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 22)) 0) = 93801 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a22_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 22))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 22) 305530) = 41281 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b22_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 22)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 22)) 305530) = 41281 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a22_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 22))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 22) 5604) = 216373 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b22_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 22)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 22)) 5604) = 216373 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a22_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 22))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 22) 221549) = 65896 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b22_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 22)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 22)) 221549) = 65896 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a22_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 22))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 22) 266275) = 94443 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b22_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 22)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 22)) 266275) = 94443 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a22_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 22))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 22) 186844) = 74793 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b22_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 22)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 22)) 186844) = 74793 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o22 : xone 22 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a22_0 b22_0 a22_1 b22_1 a22_2 b22_2
    a22_3 b22_3 a22_4 b22_4 a22_5 b22_5

theorem a23_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 23))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 23) 0) = 213003 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b23_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 23)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 23)) 0) = 213003 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a23_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 23))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 23) 305530) = 121877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b23_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 23)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 23)) 305530) = 121877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a23_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 23))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 23) 5604) = 287543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b23_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 23)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 23)) 5604) = 287543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a23_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 23))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 23) 221549) = 248748 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b23_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 23)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 23)) 221549) = 248748 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a23_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 23))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 23) 266275) = 163085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b23_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 23)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 23)) 266275) = 163085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a23_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 23))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 23) 186844) = 267879 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b23_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 23)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 23)) 186844) = 267879 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o23 : xone 23 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a23_0 b23_0 a23_1 b23_1 a23_2 b23_2
    a23_3 b23_3 a23_4 b23_4 a23_5 b23_5

theorem a24_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 24))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 24) 0) = 208531 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b24_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 24)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 24)) 0) = 208531 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a24_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 24))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 24) 305530) = 248180 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b24_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 24)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 24)) 305530) = 248180 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a24_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 24))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 24) 5604) = 19795 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b24_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 24)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 24)) 5604) = 19795 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a24_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 24))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 24) 221549) = 112742 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b24_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 24)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 24)) 221549) = 112742 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a24_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 24))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 24) 266275) = 180433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b24_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 24)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 24)) 266275) = 180433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a24_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 24))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 24) 186844) = 64324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b24_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 24)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 24)) 186844) = 64324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o24 : xone 24 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a24_0 b24_0 a24_1 b24_1 a24_2 b24_2
    a24_3 b24_3 a24_4 b24_4 a24_5 b24_5

theorem a25_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 25))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 25) 0) = 96314 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b25_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 25)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 25)) 0) = 96314 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a25_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 25))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 25) 305530) = 84072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b25_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 25)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 25)) 305530) = 84072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a25_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 25))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 25) 5604) = 14484 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b25_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 25)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 25)) 5604) = 14484 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a25_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 25))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 25) 221549) = 236358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b25_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 25)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 25)) 221549) = 236358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a25_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 25))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 25) 266275) = 232958 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b25_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 25)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 25)) 266275) = 232958 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a25_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 25))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 25) 186844) = 155323 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b25_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 25)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 25)) 186844) = 155323 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o25 : xone 25 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a25_0 b25_0 a25_1 b25_1 a25_2 b25_2
    a25_3 b25_3 a25_4 b25_4 a25_5 b25_5

theorem a26_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 26))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 26) 0) = 43289 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b26_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 26)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 26)) 0) = 43289 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a26_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 26))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 26) 305530) = 180062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b26_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 26)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 26)) 305530) = 180062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a26_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 26))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 26) 5604) = 123438 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b26_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 26)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 26)) 5604) = 123438 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a26_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 26))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 26) 221549) = 154038 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b26_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 26)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 26)) 221549) = 154038 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a26_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 26))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 26) 266275) = 143364 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b26_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 26)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 26)) 266275) = 143364 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a26_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 26))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 26) 186844) = 166371 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b26_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 26)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 26)) 186844) = 166371 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o26 : xone 26 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a26_0 b26_0 a26_1 b26_1 a26_2 b26_2
    a26_3 b26_3 a26_4 b26_4 a26_5 b26_5

theorem a27_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 27))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 27) 0) = 254693 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b27_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 27)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 27)) 0) = 254693 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a27_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 27))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 27) 305530) = 236428 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b27_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 27)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 27)) 305530) = 236428 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a27_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 27))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 27) 5604) = 97507 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b27_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 27)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 27)) 5604) = 97507 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a27_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 27))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 27) 221549) = 33366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b27_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 27)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 27)) 221549) = 33366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a27_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 27))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 27) 266275) = 11596 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b27_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 27)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 27)) 266275) = 11596 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a27_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 27))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 27) 186844) = 27845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b27_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 27)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 27)) 186844) = 27845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o27 : xone 27 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a27_0 b27_0 a27_1 b27_1 a27_2 b27_2
    a27_3 b27_3 a27_4 b27_4 a27_5 b27_5

theorem a28_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 28))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 28) 0) = 13085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b28_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 28)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 28)) 0) = 13085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a28_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 28))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 28) 305530) = 262309 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b28_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 28)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 28)) 305530) = 262309 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a28_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 28))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 28) 5604) = 187540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b28_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 28)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 28)) 5604) = 187540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a28_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 28))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 28) 221549) = 279392 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b28_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 28)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 28)) 221549) = 279392 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a28_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 28))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 28) 266275) = 7985 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b28_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 28)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 28)) 266275) = 7985 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a28_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 28))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 28) 186844) = 221868 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b28_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 28)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 28)) 186844) = 221868 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o28 : xone 28 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a28_0 b28_0 a28_1 b28_1 a28_2 b28_2
    a28_3 b28_3 a28_4 b28_4 a28_5 b28_5

theorem a29_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 29))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 29) 0) = 186390 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b29_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 29)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 29)) 0) = 186390 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a29_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 29))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 29) 305530) = 154562 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b29_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 29)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 29)) 305530) = 154562 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a29_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 29))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 29) 5604) = 68424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b29_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 29)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 29)) 5604) = 68424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a29_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 29))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 29) 221549) = 192695 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b29_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 29)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 29)) 221549) = 192695 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a29_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 29))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 29) 266275) = 89708 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b29_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 29)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 29)) 266275) = 89708 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a29_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 29))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 29) 186844) = 172492 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b29_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 29)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 29)) 186844) = 172492 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o29 : xone 29 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a29_0 b29_0 a29_1 b29_1 a29_2 b29_2
    a29_3 b29_3 a29_4 b29_4 a29_5 b29_5

theorem a30_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 30))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 30) 0) = 296312 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b30_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 30)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 30)) 0) = 296312 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a30_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 30))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 30) 305530) = 298967 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b30_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 30)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 30)) 305530) = 298967 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a30_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 30))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 30) 5604) = 111489 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b30_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 30)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 30)) 5604) = 111489 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a30_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 30))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 30) 221549) = 152339 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b30_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 30)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 30)) 221549) = 152339 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a30_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 30))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 30) 266275) = 121193 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b30_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 30)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 30)) 266275) = 121193 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a30_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 30))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 30) 186844) = 125040 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b30_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 30)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 30)) 186844) = 125040 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o30 : xone 30 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a30_0 b30_0 a30_1 b30_1 a30_2 b30_2
    a30_3 b30_3 a30_4 b30_4 a30_5 b30_5

theorem a31_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 31))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 31) 0) = 7941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b31_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 31)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 31)) 0) = 7941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a31_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 31))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 31) 305530) = 80677 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b31_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 31)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 31)) 305530) = 80677 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a31_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 31))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 31) 5604) = 92399 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b31_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 31)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 31)) 5604) = 92399 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a31_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 31))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 31) 221549) = 189647 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b31_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 31)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 31)) 221549) = 189647 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a31_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 31))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 31) 266275) = 25610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b31_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 31)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 31)) 266275) = 25610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a31_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 31))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 31) 186844) = 2845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b31_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 31)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 31)) 186844) = 2845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o31 : xone 31 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a31_0 b31_0 a31_1 b31_1 a31_2 b31_2
    a31_3 b31_3 a31_4 b31_4 a31_5 b31_5

theorem a32_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 32))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 32) 0) = 202358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b32_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 32)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 32)) 0) = 202358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a32_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 32))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 32) 305530) = 88074 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b32_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 32)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 32)) 305530) = 88074 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a32_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 32))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 32) 5604) = 16640 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b32_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 32)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 32)) 5604) = 16640 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a32_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 32))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 32) 221549) = 297376 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b32_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 32)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 32)) 221549) = 297376 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a32_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 32))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 32) 266275) = 75442 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b32_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 32)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 32)) 266275) = 75442 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a32_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 32))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 32) 186844) = 90891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b32_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 32)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 32)) 186844) = 90891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o32 : xone 32 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a32_0 b32_0 a32_1 b32_1 a32_2 b32_2
    a32_3 b32_3 a32_4 b32_4 a32_5 b32_5

theorem a33_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 33))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 33) 0) = 30169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b33_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 33)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 33)) 0) = 30169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a33_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 33))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 33) 305530) = 16759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b33_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 33)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 33)) 305530) = 16759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a33_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 33))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 33) 5604) = 246927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b33_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 33)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 33)) 5604) = 246927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a33_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 33))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 33) 221549) = 70526 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b33_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 33)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 33)) 221549) = 70526 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a33_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 33))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 33) 266275) = 65856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b33_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 33)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 33)) 266275) = 65856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a33_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 33))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 33) 186844) = 54834 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b33_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 33)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 33)) 186844) = 54834 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o33 : xone 33 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a33_0 b33_0 a33_1 b33_1 a33_2 b33_2
    a33_3 b33_3 a33_4 b33_4 a33_5 b33_5

theorem a34_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 34))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 34) 0) = 157236 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b34_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 34)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 34)) 0) = 157236 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a34_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 34))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 34) 305530) = 40056 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b34_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 34)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 34)) 305530) = 40056 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a34_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 34))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 34) 5604) = 98937 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b34_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 34)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 34)) 5604) = 98937 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a34_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 34))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 34) 221549) = 180755 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b34_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 34)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 34)) 221549) = 180755 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a34_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 34))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 34) 266275) = 128559 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b34_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 34)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 34)) 266275) = 128559 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a34_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 34))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 34) 186844) = 95445 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b34_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 34)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 34)) 186844) = 95445 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o34 : xone 34 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a34_0 b34_0 a34_1 b34_1 a34_2 b34_2
    a34_3 b34_3 a34_4 b34_4 a34_5 b34_5

theorem a35_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 35))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 35) 0) = 22392 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b35_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 35)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 35)) 0) = 22392 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a35_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 35))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 35) 305530) = 278062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b35_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 35)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 35)) 305530) = 278062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a35_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 35))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 35) 5604) = 130821 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b35_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 35)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 35)) 5604) = 130821 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a35_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 35))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 35) 221549) = 36775 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b35_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 35)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 35)) 221549) = 36775 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a35_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 35))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 35) 266275) = 167677 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b35_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 35)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 35)) 266275) = 167677 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a35_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 35))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 35) 186844) = 93605 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b35_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 35)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 35)) 186844) = 93605 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o35 : xone 35 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a35_0 b35_0 a35_1 b35_1 a35_2 b35_2
    a35_3 b35_3 a35_4 b35_4 a35_5 b35_5

theorem a36_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 36))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 36) 0) = 64283 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b36_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 36)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 36)) 0) = 64283 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a36_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 36))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 36) 305530) = 261341 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b36_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 36)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 36)) 305530) = 261341 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a36_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 36))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 36) 5604) = 184594 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b36_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 36)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 36)) 5604) = 184594 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a36_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 36))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 36) 221549) = 267653 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b36_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 36)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 36)) 221549) = 267653 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a36_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 36))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 36) 266275) = 222991 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b36_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 36)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 36)) 266275) = 222991 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a36_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 36))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 36) 186844) = 169230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b36_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 36)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 36)) 186844) = 169230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o36 : xone 36 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a36_0 b36_0 a36_1 b36_1 a36_2 b36_2
    a36_3 b36_3 a36_4 b36_4 a36_5 b36_5

theorem a37_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 37))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 37) 0) = 107747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b37_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 37)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 37)) 0) = 107747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a37_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 37))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 37) 305530) = 115565 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b37_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 37)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 37)) 305530) = 115565 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a37_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 37))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 37) 5604) = 282685 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b37_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 37)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 37)) 5604) = 282685 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a37_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 37))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 37) 221549) = 9491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b37_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 37)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 37)) 221549) = 9491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a37_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 37))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 37) 266275) = 207550 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b37_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 37)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 37)) 266275) = 207550 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a37_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 37))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 37) 186844) = 163993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b37_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 37)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 37)) 186844) = 163993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o37 : xone 37 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a37_0 b37_0 a37_1 b37_1 a37_2 b37_2
    a37_3 b37_3 a37_4 b37_4 a37_5 b37_5

theorem a38_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 38))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 38) 0) = 18333 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b38_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 38)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 38)) 0) = 18333 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a38_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 38))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 38) 305530) = 81429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b38_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 38)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 38)) 305530) = 81429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a38_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 38))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 38) 5604) = 98453 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b38_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 38)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 38)) 5604) = 98453 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a38_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 38))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 38) 221549) = 48563 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b38_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 38)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 38)) 221549) = 48563 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a38_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 38))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 38) 266275) = 225751 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b38_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 38)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 38)) 266275) = 225751 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a38_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 38))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 38) 186844) = 126571 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b38_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 38)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 38)) 186844) = 126571 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o38 : xone 38 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a38_0 b38_0 a38_1 b38_1 a38_2 b38_2
    a38_3 b38_3 a38_4 b38_4 a38_5 b38_5

theorem a39_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 39))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 39) 0) = 91318 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b39_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 39)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 39)) 0) = 91318 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a39_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 39))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 39) 305530) = 131765 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b39_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 39)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 39)) 305530) = 131765 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a39_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 39))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 39) 5604) = 154791 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b39_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 39)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 39)) 5604) = 154791 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a39_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 39))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 39) 221549) = 235289 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b39_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 39)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 39)) 221549) = 235289 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a39_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 39))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 39) 266275) = 107358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b39_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 39)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 39)) 266275) = 107358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a39_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 39))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 39) 186844) = 305716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b39_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 39)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 39)) 186844) = 305716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o39 : xone 39 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a39_0 b39_0 a39_1 b39_1 a39_2 b39_2
    a39_3 b39_3 a39_4 b39_4 a39_5 b39_5

theorem a40_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 40))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 40) 0) = 48618 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b40_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 40)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 40)) 0) = 48618 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a40_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 40))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 40) 305530) = 256286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b40_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 40)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 40)) 305530) = 256286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a40_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 40))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 40) 5604) = 265254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b40_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 40)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 40)) 5604) = 265254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a40_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 40))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 40) 221549) = 194166 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b40_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 40)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 40)) 221549) = 194166 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a40_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 40))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 40) 266275) = 17934 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b40_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 40)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 40)) 266275) = 17934 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a40_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 40))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 40) 186844) = 48722 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b40_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 40)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 40)) 186844) = 48722 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o40 : xone 40 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a40_0 b40_0 a40_1 b40_1 a40_2 b40_2
    a40_3 b40_3 a40_4 b40_4 a40_5 b40_5

theorem a41_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 41))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 41) 0) = 90928 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b41_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 41)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 41)) 0) = 90928 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a41_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 41))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 41) 305530) = 21541 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b41_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 41)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 41)) 305530) = 21541 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a41_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 41))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 41) 5604) = 275148 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b41_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 41)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 41)) 5604) = 275148 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a41_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 41))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 41) 221549) = 234426 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b41_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 41)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 41)) 221549) = 234426 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a41_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 41))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 41) 266275) = 267993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b41_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 41)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 41)) 266275) = 267993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a41_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 41))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 41) 186844) = 240904 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b41_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 41)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 41)) 186844) = 240904 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o41 : xone 41 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a41_0 b41_0 a41_1 b41_1 a41_2 b41_2
    a41_3 b41_3 a41_4 b41_4 a41_5 b41_5

theorem a42_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 42))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 42) 0) = 128368 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b42_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 42)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 42)) 0) = 128368 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a42_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 42))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 42) 305530) = 75719 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b42_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 42)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 42)) 305530) = 75719 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a42_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 42))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 42) 5604) = 115240 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b42_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 42)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 42)) 5604) = 115240 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a42_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 42))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 42) 221549) = 297350 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b42_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 42)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 42)) 221549) = 297350 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a42_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 42))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 42) 266275) = 194541 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b42_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 42)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 42)) 266275) = 194541 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a42_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 42))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 42) 186844) = 303630 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b42_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 42)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 42)) 186844) = 303630 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o42 : xone 42 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a42_0 b42_0 a42_1 b42_1 a42_2 b42_2
    a42_3 b42_3 a42_4 b42_4 a42_5 b42_5

theorem a43_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 43))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 43) 0) = 205659 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b43_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 43)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 43)) 0) = 205659 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a43_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 43))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 43) 305530) = 215352 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b43_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 43)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 43)) 305530) = 215352 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a43_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 43))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 43) 5604) = 250152 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b43_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 43)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 43)) 5604) = 250152 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a43_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 43))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 43) 221549) = 239360 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b43_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 43)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 43)) 221549) = 239360 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a43_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 43))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 43) 266275) = 276389 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b43_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 43)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 43)) 266275) = 276389 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a43_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 43))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 43) 186844) = 141985 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b43_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 43)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 43)) 186844) = 141985 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o43 : xone 43 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a43_0 b43_0 a43_1 b43_1 a43_2 b43_2
    a43_3 b43_3 a43_4 b43_4 a43_5 b43_5

theorem a44_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 44))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 44) 0) = 48935 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b44_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 44)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 44)) 0) = 48935 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a44_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 44))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 44) 305530) = 23030 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b44_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 44)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 44)) 305530) = 23030 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a44_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 44))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 44) 5604) = 244078 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b44_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 44)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 44)) 5604) = 244078 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a44_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 44))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 44) 221549) = 79042 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b44_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 44)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 44)) 221549) = 79042 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a44_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 44))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 44) 266275) = 64878 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b44_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 44)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 44)) 266275) = 64878 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a44_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 44))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 44) 186844) = 238405 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b44_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 44)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 44)) 186844) = 238405 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o44 : xone 44 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a44_0 b44_0 a44_1 b44_1 a44_2 b44_2
    a44_3 b44_3 a44_4 b44_4 a44_5 b44_5

theorem a45_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 45))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 45) 0) = 100880 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b45_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 45)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 45)) 0) = 100880 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a45_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 45))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 45) 305530) = 196825 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b45_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 45)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 45)) 305530) = 196825 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a45_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 45))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 45) 5604) = 249628 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b45_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 45)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 45)) 5604) = 249628 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a45_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 45))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 45) 221549) = 135717 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b45_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 45)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 45)) 221549) = 135717 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a45_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 45))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 45) 266275) = 290962 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b45_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 45)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 45)) 266275) = 290962 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a45_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 45))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 45) 186844) = 261767 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b45_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 45)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 45)) 186844) = 261767 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o45 : xone 45 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a45_0 b45_0 a45_1 b45_1 a45_2 b45_2
    a45_3 b45_3 a45_4 b45_4 a45_5 b45_5

theorem a46_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 46))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 46) 0) = 59702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b46_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 46)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 46)) 0) = 59702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a46_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 46))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 46) 305530) = 111740 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b46_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 46)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 46)) 305530) = 111740 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a46_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 46))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 46) 5604) = 110844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b46_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 46)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 46)) 5604) = 110844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a46_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 46))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 46) 221549) = 237559 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b46_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 46)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 46)) 221549) = 237559 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a46_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 46))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 46) 266275) = 52385 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b46_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 46)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 46)) 266275) = 52385 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a46_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 46))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 46) 186844) = 22938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b46_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 46)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 46)) 186844) = 22938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o46 : xone 46 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a46_0 b46_0 a46_1 b46_1 a46_2 b46_2
    a46_3 b46_3 a46_4 b46_4 a46_5 b46_5

theorem a47_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 47))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 47) 0) = 198450 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b47_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 47)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 47)) 0) = 198450 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a47_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 47))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 47) 305530) = 34586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b47_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 47)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 47)) 305530) = 34586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a47_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 47))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 47) 5604) = 20407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b47_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 47)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 47)) 5604) = 20407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a47_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 47))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 47) 221549) = 150516 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b47_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 47)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 47)) 221549) = 150516 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a47_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 47))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 47) 266275) = 3001 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b47_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 47)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 47)) 266275) = 3001 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a47_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 47))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 47) 186844) = 15886 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b47_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 47)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 47)) 186844) = 15886 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o47 : xone 47 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a47_0 b47_0 a47_1 b47_1 a47_2 b47_2
    a47_3 b47_3 a47_4 b47_4 a47_5 b47_5

theorem a48_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 48))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 48) 0) = 306233 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b48_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 48)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 48)) 0) = 306233 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a48_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 48))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 48) 305530) = 183735 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b48_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 48)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 48)) 305530) = 183735 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a48_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 48))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 48) 5604) = 235837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b48_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 48)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 48)) 5604) = 235837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a48_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 48))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 48) 221549) = 42848 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b48_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 48)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 48)) 221549) = 42848 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a48_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 48))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 48) 266275) = 160696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b48_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 48)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 48)) 266275) = 160696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a48_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 48))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 48) 186844) = 104707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b48_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 48)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 48)) 186844) = 104707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o48 : xone 48 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a48_0 b48_0 a48_1 b48_1 a48_2 b48_2
    a48_3 b48_3 a48_4 b48_4 a48_5 b48_5

theorem a49_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 49))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 49) 0) = 131499 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b49_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 49)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 49)) 0) = 131499 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a49_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 49))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 49) 305530) = 95766 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b49_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 49)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 49)) 305530) = 95766 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a49_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 49))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 49) 5604) = 270626 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b49_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 49)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 49)) 5604) = 270626 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a49_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 49))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 49) 221549) = 18808 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b49_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 49)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 49)) 221549) = 18808 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a49_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 49))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 49) 266275) = 225669 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b49_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 49)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 49)) 266275) = 225669 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a49_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 49))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 49) 186844) = 93297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b49_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 49)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 49)) 186844) = 93297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o49 : xone 49 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a49_0 b49_0 a49_1 b49_1 a49_2 b49_2
    a49_3 b49_3 a49_4 b49_4 a49_5 b49_5

theorem a50_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 50))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 50) 0) = 96347 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b50_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 50)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 50)) 0) = 96347 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a50_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 50))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 50) 305530) = 255934 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b50_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 50)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 50)) 305530) = 255934 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a50_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 50))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 50) 5604) = 31430 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b50_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 50)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 50)) 5604) = 31430 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a50_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 50))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 50) 221549) = 266791 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b50_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 50)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 50)) 221549) = 266791 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a50_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 50))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 50) 266275) = 167197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b50_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 50)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 50)) 266275) = 167197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a50_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 50))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 50) 186844) = 6283 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b50_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 50)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 50)) 186844) = 6283 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o50 : xone 50 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a50_0 b50_0 a50_1 b50_1 a50_2 b50_2
    a50_3 b50_3 a50_4 b50_4 a50_5 b50_5

theorem a51_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 51))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 51) 0) = 138611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b51_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 51)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 51)) 0) = 138611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a51_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 51))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 51) 305530) = 165983 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b51_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 51)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 51)) 305530) = 165983 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a51_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 51))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 51) 5604) = 171390 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b51_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 51)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 51)) 5604) = 171390 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a51_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 51))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 51) 221549) = 218981 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b51_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 51)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 51)) 221549) = 218981 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a51_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 51))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 51) 266275) = 265873 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b51_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 51)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 51)) 266275) = 265873 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a51_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 51))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 51) 186844) = 301384 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b51_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 51)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 51)) 186844) = 301384 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o51 : xone 51 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a51_0 b51_0 a51_1 b51_1 a51_2 b51_2
    a51_3 b51_3 a51_4 b51_4 a51_5 b51_5

theorem a52_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 52))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 52) 0) = 146073 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b52_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 52)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 52)) 0) = 146073 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a52_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 52))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 52) 305530) = 54584 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b52_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 52)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 52)) 305530) = 54584 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a52_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 52))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 52) 5604) = 252128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b52_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 52)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 52)) 5604) = 252128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a52_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 52))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 52) 221549) = 244525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b52_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 52)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 52)) 221549) = 244525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a52_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 52))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 52) 266275) = 124593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b52_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 52)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 52)) 266275) = 124593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a52_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 52))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 52) 186844) = 171435 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b52_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 52)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 52)) 186844) = 171435 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o52 : xone 52 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a52_0 b52_0 a52_1 b52_1 a52_2 b52_2
    a52_3 b52_3 a52_4 b52_4 a52_5 b52_5

theorem a53_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 53))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 53) 0) = 183064 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b53_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 53)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 53)) 0) = 183064 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a53_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 53))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 53) 305530) = 33284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b53_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 53)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 53)) 305530) = 33284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a53_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 53))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 53) 5604) = 245267 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b53_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 53)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 53)) 5604) = 245267 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a53_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 53))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 53) 221549) = 14154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b53_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 53)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 53)) 221549) = 14154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a53_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 53))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 53) 266275) = 202469 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b53_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 53)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 53)) 266275) = 202469 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a53_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 53))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 53) 186844) = 87509 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b53_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 53)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 53)) 186844) = 87509 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o53 : xone 53 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a53_0 b53_0 a53_1 b53_1 a53_2 b53_2
    a53_3 b53_3 a53_4 b53_4 a53_5 b53_5

theorem a54_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 54))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 54) 0) = 123127 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b54_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 54)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 54)) 0) = 123127 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a54_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 54))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 54) 305530) = 95763 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b54_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 54)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 54)) 305530) = 95763 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a54_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 54))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 54) 5604) = 2458 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b54_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 54)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 54)) 5604) = 2458 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a54_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 54))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 54) 221549) = 121417 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b54_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 54)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 54)) 221549) = 121417 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a54_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 54))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 54) 266275) = 253961 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b54_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 54)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 54)) 266275) = 253961 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a54_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 54))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 54) 186844) = 163534 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b54_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 54)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 54)) 186844) = 163534 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o54 : xone 54 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a54_0 b54_0 a54_1 b54_1 a54_2 b54_2
    a54_3 b54_3 a54_4 b54_4 a54_5 b54_5

theorem a55_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 55))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 55) 0) = 138167 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b55_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 55)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 55)) 0) = 138167 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a55_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 55))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 55) 305530) = 228067 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b55_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 55)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 55)) 305530) = 228067 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a55_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 55))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 55) 5604) = 162588 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b55_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 55)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 55)) 5604) = 162588 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a55_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 55))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 55) 221549) = 282109 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b55_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 55)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 55)) 221549) = 282109 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a55_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 55))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 55) 266275) = 184125 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b55_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 55)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 55)) 266275) = 184125 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a55_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 55))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 55) 186844) = 149792 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b55_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 55)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 55)) 186844) = 149792 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o55 : xone 55 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a55_0 b55_0 a55_1 b55_1 a55_2 b55_2
    a55_3 b55_3 a55_4 b55_4 a55_5 b55_5

theorem a56_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 56))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 56) 0) = 165085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b56_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 56)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 56)) 0) = 165085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a56_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 56))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 56) 305530) = 165908 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b56_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 56)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 56)) 305530) = 165908 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a56_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 56))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 56) 5604) = 14390 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b56_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 56)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 56)) 5604) = 14390 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a56_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 56))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 56) 221549) = 291041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b56_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 56)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 56)) 221549) = 291041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a56_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 56))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 56) 266275) = 19618 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b56_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 56)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 56)) 266275) = 19618 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a56_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 56))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 56) 186844) = 269436 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b56_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 56)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 56)) 186844) = 269436 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o56 : xone 56 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a56_0 b56_0 a56_1 b56_1 a56_2 b56_2
    a56_3 b56_3 a56_4 b56_4 a56_5 b56_5

theorem a57_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 57))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 57) 0) = 163338 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b57_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 57)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 57)) 0) = 163338 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a57_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 57))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 57) 305530) = 263628 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b57_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 57)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 57)) 305530) = 263628 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a57_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 57))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 57) 5604) = 18665 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b57_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 57)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 57)) 5604) = 18665 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a57_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 57))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 57) 221549) = 225677 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b57_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 57)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 57)) 221549) = 225677 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a57_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 57))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 57) 266275) = 297876 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b57_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 57)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 57)) 266275) = 297876 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a57_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 57))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 57) 186844) = 59894 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b57_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 57)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 57)) 186844) = 59894 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o57 : xone 57 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a57_0 b57_0 a57_1 b57_1 a57_2 b57_2
    a57_3 b57_3 a57_4 b57_4 a57_5 b57_5

theorem a58_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 58))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 58) 0) = 131562 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b58_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 58)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 58)) 0) = 131562 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a58_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 58))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 58) 305530) = 9548 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b58_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 58)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 58)) 305530) = 9548 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a58_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 58))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 58) 5604) = 61752 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b58_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 58)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 58)) 5604) = 61752 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a58_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 58))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 58) 221549) = 265712 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b58_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 58)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 58)) 221549) = 265712 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a58_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 58))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 58) 266275) = 246125 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b58_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 58)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 58)) 266275) = 246125 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a58_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 58))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 58) 186844) = 26663 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b58_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 58)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 58)) 186844) = 26663 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o58 : xone 58 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a58_0 b58_0 a58_1 b58_1 a58_2 b58_2
    a58_3 b58_3 a58_4 b58_4 a58_5 b58_5

theorem a59_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 59))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 59) 0) = 61201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b59_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 59)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 59)) 0) = 61201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a59_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 59))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 59) 305530) = 42271 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b59_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 59)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 59)) 305530) = 42271 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a59_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 59))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 59) 5604) = 60566 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b59_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 59)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 59)) 5604) = 60566 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a59_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 59))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 59) 221549) = 83348 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b59_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 59)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 59)) 221549) = 83348 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a59_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 59))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 59) 266275) = 8546 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b59_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 59)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 59)) 266275) = 8546 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a59_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 59))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 59) 186844) = 219788 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b59_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 59)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 59)) 186844) = 219788 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o59 : xone 59 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a59_0 b59_0 a59_1 b59_1 a59_2 b59_2
    a59_3 b59_3 a59_4 b59_4 a59_5 b59_5

theorem a60_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 60))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 60) 0) = 53707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b60_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 60)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 60)) 0) = 53707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a60_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 60))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 60) 305530) = 303402 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b60_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 60)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 60)) 305530) = 303402 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a60_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 60))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 60) 5604) = 99990 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b60_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 60)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 60)) 5604) = 99990 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a60_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 60))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 60) 221549) = 240088 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b60_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 60)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 60)) 221549) = 240088 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a60_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 60))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 60) 266275) = 227585 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b60_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 60)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 60)) 266275) = 227585 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a60_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 60))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 60) 186844) = 76389 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b60_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 60)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 60)) 186844) = 76389 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o60 : xone 60 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a60_0 b60_0 a60_1 b60_1 a60_2 b60_2
    a60_3 b60_3 a60_4 b60_4 a60_5 b60_5

theorem a61_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 61))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 61) 0) = 59005 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b61_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 61)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 61)) 0) = 59005 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a61_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 61))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 61) 305530) = 43127 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b61_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 61)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 61)) 305530) = 43127 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a61_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 61))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 61) 5604) = 255884 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b61_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 61)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 61)) 5604) = 255884 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a61_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 61))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 61) 221549) = 39708 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b61_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 61)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 61)) 221549) = 39708 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a61_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 61))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 61) 266275) = 69914 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b61_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 61)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 61)) 266275) = 69914 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a61_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 61))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 61) 186844) = 66094 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b61_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 61)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 61)) 186844) = 66094 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o61 : xone 61 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a61_0 b61_0 a61_1 b61_1 a61_2 b61_2
    a61_3 b61_3 a61_4 b61_4 a61_5 b61_5

theorem a62_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 62))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 62) 0) = 237070 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b62_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 62)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 62)) 0) = 237070 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a62_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 62))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 62) 305530) = 142768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b62_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 62)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 62)) 305530) = 142768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a62_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 62))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 62) 5604) = 144169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b62_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 62)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 62)) 5604) = 144169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a62_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 62))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 62) 221549) = 287765 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b62_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 62)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 62)) 221549) = 287765 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a62_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 62))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 62) 266275) = 95856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b62_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 62)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 62)) 266275) = 95856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a62_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 62))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 62) 186844) = 267383 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b62_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 62)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 62)) 186844) = 267383 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o62 : xone 62 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a62_0 b62_0 a62_1 b62_1 a62_2 b62_2
    a62_3 b62_3 a62_4 b62_4 a62_5 b62_5

theorem a63_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 63))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 63) 0) = 36523 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b63_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 63)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 63)) 0) = 36523 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a63_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 63))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 63) 305530) = 177783 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b63_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 63)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 63)) 305530) = 177783 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a63_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 63))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 63) 5604) = 167019 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b63_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 63)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 63)) 5604) = 167019 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a63_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 63))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 63) 221549) = 89724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b63_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 63)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 63)) 221549) = 89724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a63_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 63))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 63) 266275) = 298342 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b63_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 63)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 63)) 266275) = 298342 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a63_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 63))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 63) 186844) = 191844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b63_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 63)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 63)) 186844) = 191844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o63 : xone 63 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a63_0 b63_0 a63_1 b63_1 a63_2 b63_2
    a63_3 b63_3 a63_4 b63_4 a63_5 b63_5

theorem a64_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 64))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 64) 0) = 270686 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b64_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 64)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 64)) 0) = 270686 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a64_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 64))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 64) 305530) = 290200 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b64_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 64)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 64)) 305530) = 290200 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a64_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 64))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 64) 5604) = 241498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b64_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 64)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 64)) 5604) = 241498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a64_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 64))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 64) 221549) = 43126 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b64_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 64)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 64)) 221549) = 43126 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a64_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 64))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 64) 266275) = 63556 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b64_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 64)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 64)) 266275) = 63556 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a64_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 64))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 64) 186844) = 31385 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b64_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 64)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 64)) 186844) = 31385 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o64 : xone 64 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a64_0 b64_0 a64_1 b64_1 a64_2 b64_2
    a64_3 b64_3 a64_4 b64_4 a64_5 b64_5

theorem a65_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 65))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 65) 0) = 304037 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b65_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 65)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 65)) 0) = 304037 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a65_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 65))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 65) 305530) = 13487 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b65_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 65)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 65)) 305530) = 13487 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a65_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 65))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 65) 5604) = 69633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b65_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 65)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 65)) 5604) = 69633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a65_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 65))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 65) 221549) = 94461 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b65_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 65)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 65)) 221549) = 94461 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a65_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 65))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 65) 266275) = 173722 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b65_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 65)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 65)) 266275) = 173722 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a65_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 65))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 65) 186844) = 91773 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b65_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 65)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 65)) 186844) = 91773 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o65 : xone 65 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a65_0 b65_0 a65_1 b65_1 a65_2 b65_2
    a65_3 b65_3 a65_4 b65_4 a65_5 b65_5

theorem a66_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 66))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 66) 0) = 72260 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b66_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 66)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 66)) 0) = 72260 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a66_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 66))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 66) 305530) = 261404 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b66_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 66)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 66)) 305530) = 261404 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a66_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 66))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 66) 5604) = 12972 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b66_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 66)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 66)) 5604) = 12972 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a66_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 66))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 66) 221549) = 220766 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b66_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 66)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 66)) 221549) = 220766 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a66_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 66))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 66) 266275) = 220624 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b66_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 66)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 66)) 266275) = 220624 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a66_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 66))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 66) 186844) = 269507 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b66_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 66)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 66)) 186844) = 269507 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o66 : xone 66 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a66_0 b66_0 a66_1 b66_1 a66_2 b66_2
    a66_3 b66_3 a66_4 b66_4 a66_5 b66_5

theorem a67_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 67))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 67) 0) = 6601 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b67_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 67)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 67)) 0) = 6601 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a67_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 67))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 67) 305530) = 259422 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b67_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 67)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 67)) 305530) = 259422 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a67_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 67))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 67) 5604) = 215949 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b67_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 67)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 67)) 5604) = 215949 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a67_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 67))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 67) 221549) = 207469 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b67_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 67)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 67)) 221549) = 207469 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a67_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 67))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 67) 266275) = 277319 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b67_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 67)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 67)) 266275) = 277319 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a67_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 67))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 67) 186844) = 222705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b67_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 67)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 67)) 186844) = 222705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o67 : xone 67 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a67_0 b67_0 a67_1 b67_1 a67_2 b67_2
    a67_3 b67_3 a67_4 b67_4 a67_5 b67_5

theorem a68_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 68))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 68) 0) = 89619 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b68_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 68)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 68)) 0) = 89619 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a68_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 68))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 68) 305530) = 97402 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b68_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 68)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 68)) 305530) = 97402 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a68_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 68))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 68) 5604) = 249517 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b68_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 68)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 68)) 5604) = 249517 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a68_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 68))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 68) 221549) = 89138 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b68_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 68)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 68)) 221549) = 89138 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a68_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 68))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 68) 266275) = 257482 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b68_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 68)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 68)) 266275) = 257482 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a68_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 68))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 68) 186844) = 258490 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b68_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 68)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 68)) 186844) = 258490 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o68 : xone 68 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a68_0 b68_0 a68_1 b68_1 a68_2 b68_2
    a68_3 b68_3 a68_4 b68_4 a68_5 b68_5

theorem a69_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 69))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 69) 0) = 233313 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b69_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 69)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 69)) 0) = 233313 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a69_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 69))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 69) 305530) = 228446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b69_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 69)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 69)) 305530) = 228446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a69_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 69))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 69) 5604) = 115254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b69_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 69)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 69)) 5604) = 115254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a69_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 69))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 69) 221549) = 15139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b69_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 69)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 69)) 221549) = 15139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a69_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 69))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 69) 266275) = 281607 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b69_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 69)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 69)) 266275) = 281607 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a69_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 69))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 69) 186844) = 79369 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b69_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 69)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 69)) 186844) = 79369 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o69 : xone 69 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a69_0 b69_0 a69_1 b69_1 a69_2 b69_2
    a69_3 b69_3 a69_4 b69_4 a69_5 b69_5

theorem a70_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 70))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 70) 0) = 15625 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b70_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 70)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 70)) 0) = 15625 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a70_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 70))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 70) 305530) = 5276 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b70_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 70)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 70)) 305530) = 5276 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a70_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 70))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 70) 5604) = 31857 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b70_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 70)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 70)) 5604) = 31857 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a70_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 70))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 70) 221549) = 253608 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b70_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 70)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 70)) 221549) = 253608 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a70_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 70))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 70) 266275) = 287681 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b70_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 70)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 70)) 266275) = 287681 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a70_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 70))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 70) 186844) = 146169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b70_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 70)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 70)) 186844) = 146169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o70 : xone 70 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a70_0 b70_0 a70_1 b70_1 a70_2 b70_2
    a70_3 b70_3 a70_4 b70_4 a70_5 b70_5

theorem a71_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 71))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 71) 0) = 289298 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b71_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 71)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 71)) 0) = 289298 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a71_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 71))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 71) 305530) = 159557 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b71_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 71)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 71)) 305530) = 159557 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a71_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 71))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 71) 5604) = 131755 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b71_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 71)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 71)) 5604) = 131755 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a71_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 71))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 71) 221549) = 201700 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b71_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 71)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 71)) 221549) = 201700 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a71_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 71))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 71) 266275) = 62243 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b71_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 71)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 71)) 266275) = 62243 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a71_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 71))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 71) 186844) = 24283 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b71_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 71)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 71)) 186844) = 24283 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o71 : xone 71 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a71_0 b71_0 a71_1 b71_1 a71_2 b71_2
    a71_3 b71_3 a71_4 b71_4 a71_5 b71_5

theorem a72_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 72))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 72) 0) = 229942 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b72_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 72)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 72)) 0) = 229942 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a72_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 72))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 72) 305530) = 249218 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b72_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 72)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 72)) 305530) = 249218 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a72_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 72))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 72) 5604) = 144196 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b72_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 72)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 72)) 5604) = 144196 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a72_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 72))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 72) 221549) = 34630 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b72_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 72)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 72)) 221549) = 34630 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a72_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 72))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 72) 266275) = 141543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b72_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 72)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 72)) 266275) = 141543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a72_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 72))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 72) 186844) = 48349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b72_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 72)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 72)) 186844) = 48349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o72 : xone 72 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a72_0 b72_0 a72_1 b72_1 a72_2 b72_2
    a72_3 b72_3 a72_4 b72_4 a72_5 b72_5

theorem a73_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 73))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 73) 0) = 89619 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b73_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 73)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 73)) 0) = 89619 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a73_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 73))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 73) 305530) = 87816 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b73_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 73)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 73)) 305530) = 87816 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a73_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 73))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 73) 5604) = 248846 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b73_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 73)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 73)) 5604) = 248846 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a73_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 73))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 73) 221549) = 183133 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b73_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 73)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 73)) 221549) = 183133 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a73_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 73))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 73) 266275) = 3365 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b73_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 73)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 73)) 266275) = 3365 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a73_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 73))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 73) 186844) = 114654 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b73_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 73)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 73)) 186844) = 114654 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o73 : xone 73 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a73_0 b73_0 a73_1 b73_1 a73_2 b73_2
    a73_3 b73_3 a73_4 b73_4 a73_5 b73_5

theorem a74_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 74))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 74) 0) = 25701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b74_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 74)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 74)) 0) = 25701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a74_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 74))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 74) 305530) = 105254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b74_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 74)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 74)) 305530) = 105254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a74_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 74))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 74) 5604) = 123928 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b74_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 74)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 74)) 5604) = 123928 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a74_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 74))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 74) 221549) = 292168 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b74_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 74)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 74)) 221549) = 292168 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a74_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 74))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 74) 266275) = 231274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b74_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 74)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 74)) 266275) = 231274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a74_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 74))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 74) 186844) = 244914 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b74_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 74)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 74)) 186844) = 244914 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o74 : xone 74 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a74_0 b74_0 a74_1 b74_1 a74_2 b74_2
    a74_3 b74_3 a74_4 b74_4 a74_5 b74_5

theorem a75_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 75))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 75) 0) = 228685 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b75_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 75)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 75)) 0) = 228685 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a75_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 75))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 75) 305530) = 225041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b75_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 75)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 75)) 305530) = 225041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a75_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 75))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 75) 5604) = 270323 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b75_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 75)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 75)) 5604) = 270323 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a75_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 75))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 75) 221549) = 283670 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b75_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 75)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 75)) 221549) = 283670 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a75_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 75))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 75) 266275) = 241548 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b75_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 75)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 75)) 266275) = 241548 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a75_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 75))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 75) 186844) = 91673 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b75_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 75)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 75)) 186844) = 91673 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o75 : xone 75 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a75_0 b75_0 a75_1 b75_1 a75_2 b75_2
    a75_3 b75_3 a75_4 b75_4 a75_5 b75_5

theorem a76_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 76))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 76) 0) = 271893 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b76_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 76)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 76)) 0) = 271893 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a76_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 76))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 76) 305530) = 299576 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b76_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 76)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 76)) 305530) = 299576 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a76_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 76))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 76) 5604) = 32500 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b76_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 76)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 76)) 5604) = 32500 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a76_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 76))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 76) 221549) = 153621 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b76_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 76)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 76)) 221549) = 153621 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a76_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 76))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 76) 266275) = 208351 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b76_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 76)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 76)) 266275) = 208351 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a76_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 76))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 76) 186844) = 187380 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b76_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 76)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 76)) 186844) = 187380 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o76 : xone 76 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a76_0 b76_0 a76_1 b76_1 a76_2 b76_2
    a76_3 b76_3 a76_4 b76_4 a76_5 b76_5

theorem a77_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 77))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 77) 0) = 35201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b77_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 77)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 77)) 0) = 35201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a77_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 77))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 77) 305530) = 213068 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b77_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 77)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 77)) 305530) = 213068 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a77_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 77))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 77) 5604) = 245672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b77_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 77)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 77)) 5604) = 245672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a77_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 77))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 77) 221549) = 101105 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b77_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 77)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 77)) 221549) = 101105 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a77_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 77))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 77) 266275) = 12560 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b77_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 77)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 77)) 266275) = 12560 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a77_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 77))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 77) 186844) = 15221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b77_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 77)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 77)) 186844) = 15221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o77 : xone 77 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a77_0 b77_0 a77_1 b77_1 a77_2 b77_2
    a77_3 b77_3 a77_4 b77_4 a77_5 b77_5

theorem a78_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 78))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 78) 0) = 69741 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b78_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 78)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 78)) 0) = 69741 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a78_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 78))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 78) 305530) = 173232 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b78_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 78)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 78)) 305530) = 173232 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a78_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 78))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 78) 5604) = 245906 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b78_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 78)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 78)) 5604) = 245906 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a78_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 78))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 78) 221549) = 151167 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b78_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 78)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 78)) 221549) = 151167 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a78_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 78))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 78) 266275) = 125984 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b78_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 78)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 78)) 266275) = 125984 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a78_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 78))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 78) 186844) = 138618 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b78_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 78)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 78)) 186844) = 138618 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o78 : xone 78 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a78_0 b78_0 a78_1 b78_1 a78_2 b78_2
    a78_3 b78_3 a78_4 b78_4 a78_5 b78_5

theorem a79_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 79))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 79) 0) = 101578 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b79_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 79)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 79)) 0) = 101578 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a79_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 79))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 79) 305530) = 136212 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b79_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 79)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 79)) 305530) = 136212 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a79_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 79))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 79) 5604) = 186844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b79_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 79)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 79)) 5604) = 186844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a79_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 79))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 79) 221549) = 77170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b79_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 79)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 79)) 221549) = 77170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a79_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 79))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 79) 266275) = 105946 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b79_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 79)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 79)) 266275) = 105946 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a79_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 79))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 79) 186844) = 304598 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b79_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 79)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 79)) 186844) = 304598 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o79 : xone 79 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a79_0 b79_0 a79_1 b79_1 a79_2 b79_2
    a79_3 b79_3 a79_4 b79_4 a79_5 b79_5

theorem a80_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 80))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 80) 0) = 84429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b80_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 80)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 80)) 0) = 84429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a80_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 80))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 80) 305530) = 206849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b80_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 80)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 80)) 305530) = 206849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a80_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 80))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 80) 5604) = 15629 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b80_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 80)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 80)) 5604) = 15629 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a80_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 80))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 80) 221549) = 152356 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b80_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 80)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 80)) 221549) = 152356 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a80_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 80))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 80) 266275) = 264752 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b80_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 80)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 80)) 266275) = 264752 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a80_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 80))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 80) 186844) = 104339 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b80_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 80)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 80)) 186844) = 104339 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o80 : xone 80 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a80_0 b80_0 a80_1 b80_1 a80_2 b80_2
    a80_3 b80_3 a80_4 b80_4 a80_5 b80_5

theorem a81_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 81))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 81) 0) = 16503 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b81_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 81)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 81)) 0) = 16503 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a81_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 81))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 81) 305530) = 293100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b81_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 81)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 81)) 305530) = 293100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a81_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 81))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 81) 5604) = 192112 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b81_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 81)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 81)) 5604) = 192112 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a81_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 81))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 81) 221549) = 23632 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b81_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 81)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 81)) 221549) = 23632 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a81_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 81))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 81) 266275) = 10979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b81_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 81)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 81)) 266275) = 10979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a81_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 81))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 81) 186844) = 130094 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b81_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 81)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 81)) 186844) = 130094 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o81 : xone 81 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a81_0 b81_0 a81_1 b81_1 a81_2 b81_2
    a81_3 b81_3 a81_4 b81_4 a81_5 b81_5

theorem a82_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 82))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 82) 0) = 207085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b82_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 82)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 82)) 0) = 207085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a82_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 82))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 82) 305530) = 241978 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b82_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 82)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 82)) 305530) = 241978 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a82_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 82))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 82) 5604) = 16126 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b82_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 82)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 82)) 5604) = 16126 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a82_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 82))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 82) 221549) = 283416 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b82_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 82)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 82)) 221549) = 283416 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a82_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 82))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 82) 266275) = 297153 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b82_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 82)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 82)) 266275) = 297153 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a82_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 82))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 82) 186844) = 115620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b82_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 82)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 82)) 186844) = 115620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o82 : xone 82 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a82_0 b82_0 a82_1 b82_1 a82_2 b82_2
    a82_3 b82_3 a82_4 b82_4 a82_5 b82_5

theorem a83_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 83))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 83) 0) = 102262 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b83_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 83)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 83)) 0) = 102262 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a83_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 83))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 83) 305530) = 267004 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b83_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 83)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 83)) 305530) = 267004 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a83_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 83))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 83) 5604) = 138551 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b83_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 83)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 83)) 5604) = 138551 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a83_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 83))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 83) 221549) = 2812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b83_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 83)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 83)) 221549) = 2812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a83_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 83))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 83) 266275) = 287212 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b83_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 83)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 83)) 266275) = 287212 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a83_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 83))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 83) 186844) = 124805 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b83_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 83)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 83)) 186844) = 124805 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o83 : xone 83 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a83_0 b83_0 a83_1 b83_1 a83_2 b83_2
    a83_3 b83_3 a83_4 b83_4 a83_5 b83_5

theorem a84_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 84))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 84) 0) = 250019 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b84_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 84)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 84)) 0) = 250019 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a84_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 84))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 84) 305530) = 177547 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b84_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 84)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 84)) 305530) = 177547 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a84_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 84))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 84) 5604) = 70359 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b84_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 84)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 84)) 5604) = 70359 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a84_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 84))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 84) 221549) = 287254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b84_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 84)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 84)) 221549) = 287254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a84_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 84))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 84) 266275) = 21607 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b84_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 84)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 84)) 266275) = 21607 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a84_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 84))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 84) 186844) = 170697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b84_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 84)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 84)) 186844) = 170697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o84 : xone 84 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a84_0 b84_0 a84_1 b84_1 a84_2 b84_2
    a84_3 b84_3 a84_4 b84_4 a84_5 b84_5

theorem a85_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 85))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 85) 0) = 50018 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b85_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 85)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 85)) 0) = 50018 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a85_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 85))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 85) 305530) = 207264 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b85_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 85)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 85)) 305530) = 207264 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a85_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 85))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 85) 5604) = 169356 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b85_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 85)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 85)) 5604) = 169356 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a85_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 85))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 85) 221549) = 128635 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b85_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 85)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 85)) 221549) = 128635 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a85_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 85))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 85) 266275) = 97224 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b85_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 85)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 85)) 266275) = 97224 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a85_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 85))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 85) 186844) = 147708 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b85_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 85)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 85)) 186844) = 147708 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o85 : xone 85 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a85_0 b85_0 a85_1 b85_1 a85_2 b85_2
    a85_3 b85_3 a85_4 b85_4 a85_5 b85_5

theorem a86_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 86))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 86) 0) = 58706 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b86_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 86)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 86)) 0) = 58706 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a86_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 86))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 86) 305530) = 15023 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b86_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 86)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 86)) 305530) = 15023 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a86_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 86))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 86) 5604) = 135130 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b86_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 86)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 86)) 5604) = 135130 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a86_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 86))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 86) 221549) = 96468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b86_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 86)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 86)) 221549) = 96468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a86_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 86))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 86) 266275) = 155036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b86_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 86)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 86)) 266275) = 155036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a86_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 86))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 86) 186844) = 284076 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b86_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 86)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 86)) 186844) = 284076 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o86 : xone 86 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a86_0 b86_0 a86_1 b86_1 a86_2 b86_2
    a86_3 b86_3 a86_4 b86_4 a86_5 b86_5

theorem a87_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 87))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 87) 0) = 272084 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b87_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 87)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 87)) 0) = 272084 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a87_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 87))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 87) 305530) = 85659 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b87_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 87)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 87)) 305530) = 85659 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a87_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 87))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 87) 5604) = 193800 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b87_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 87)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 87)) 5604) = 193800 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a87_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 87))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 87) 221549) = 290637 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b87_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 87)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 87)) 221549) = 290637 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a87_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 87))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 87) 266275) = 270845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b87_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 87)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 87)) 266275) = 270845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a87_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 87))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 87) 186844) = 73609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b87_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 87)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 87)) 186844) = 73609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o87 : xone 87 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a87_0 b87_0 a87_1 b87_1 a87_2 b87_2
    a87_3 b87_3 a87_4 b87_4 a87_5 b87_5

theorem a88_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 88))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 88) 0) = 48964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b88_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 88)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 88)) 0) = 48964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a88_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 88))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 88) 305530) = 207956 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b88_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 88)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 88)) 305530) = 207956 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a88_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 88))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 88) 5604) = 8129 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b88_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 88)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 88)) 5604) = 8129 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a88_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 88))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 88) 221549) = 84051 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b88_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 88)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 88)) 221549) = 84051 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a88_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 88))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 88) 266275) = 229297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b88_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 88)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 88)) 266275) = 229297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a88_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 88))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 88) 186844) = 37585 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b88_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 88)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 88)) 186844) = 37585 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o88 : xone 88 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a88_0 b88_0 a88_1 b88_1 a88_2 b88_2
    a88_3 b88_3 a88_4 b88_4 a88_5 b88_5

theorem a89_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 89))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 89) 0) = 264963 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b89_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 89)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 89)) 0) = 264963 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a89_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 89))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 89) 305530) = 301357 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b89_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 89)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 89)) 305530) = 301357 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a89_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 89))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 89) 5604) = 243083 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b89_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 89)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 89)) 5604) = 243083 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a89_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 89))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 89) 221549) = 199809 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b89_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 89)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 89)) 221549) = 199809 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a89_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 89))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 89) 266275) = 281088 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b89_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 89)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 89)) 266275) = 281088 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a89_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 89))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 89) 186844) = 131343 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b89_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 89)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 89)) 186844) = 131343 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o89 : xone 89 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a89_0 b89_0 a89_1 b89_1 a89_2 b89_2
    a89_3 b89_3 a89_4 b89_4 a89_5 b89_5

theorem a90_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 90))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 90) 0) = 287423 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b90_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 90)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 90)) 0) = 287423 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a90_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 90))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 90) 305530) = 263647 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b90_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 90)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 90)) 305530) = 263647 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a90_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 90))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 90) 5604) = 216527 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b90_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 90)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 90)) 5604) = 216527 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a90_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 90))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 90) 221549) = 239157 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b90_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 90)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 90)) 221549) = 239157 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a90_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 90))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 90) 266275) = 75386 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b90_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 90)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 90)) 266275) = 75386 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a90_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 90))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 90) 186844) = 130733 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b90_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 90)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 90)) 186844) = 130733 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o90 : xone 90 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a90_0 b90_0 a90_1 b90_1 a90_2 b90_2
    a90_3 b90_3 a90_4 b90_4 a90_5 b90_5

theorem a91_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 91))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 91) 0) = 149938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b91_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 91)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 91)) 0) = 149938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a91_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 91))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 91) 305530) = 297394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b91_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 91)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 91)) 305530) = 297394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a91_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 91))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 91) 5604) = 131383 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b91_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 91)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 91)) 5604) = 131383 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a91_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 91))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 91) 221549) = 87014 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b91_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 91)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 91)) 221549) = 87014 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a91_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 91))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 91) 266275) = 219147 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b91_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 91)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 91)) 266275) = 219147 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a91_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 91))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 91) 186844) = 18882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b91_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 91)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 91)) 186844) = 18882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o91 : xone 91 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a91_0 b91_0 a91_1 b91_1 a91_2 b91_2
    a91_3 b91_3 a91_4 b91_4 a91_5 b91_5

theorem a92_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 92))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 92) 0) = 84048 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b92_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 92)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 92)) 0) = 84048 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a92_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 92))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 92) 305530) = 272678 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b92_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 92)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 92)) 305530) = 272678 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a92_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 92))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 92) 5604) = 47870 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b92_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 92)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 92)) 5604) = 47870 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a92_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 92))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 92) 221549) = 93284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b92_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 92)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 92)) 221549) = 93284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a92_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 92))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 92) 266275) = 214773 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b92_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 92)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 92)) 266275) = 214773 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a92_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 92))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 92) 186844) = 220450 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b92_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 92)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 92)) 186844) = 220450 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o92 : xone 92 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a92_0 b92_0 a92_1 b92_1 a92_2 b92_2
    a92_3 b92_3 a92_4 b92_4 a92_5 b92_5

theorem a93_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 93))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 93) 0) = 266717 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b93_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 93)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 93)) 0) = 266717 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a93_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 93))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 93) 305530) = 124535 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b93_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 93)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 93)) 305530) = 124535 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a93_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 93))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 93) 5604) = 215025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b93_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 93)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 93)) 5604) = 215025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a93_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 93))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 93) 221549) = 291154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b93_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 93)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 93)) 221549) = 291154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a93_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 93))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 93) 266275) = 112474 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b93_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 93)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 93)) 266275) = 112474 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a93_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 93))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 93) 186844) = 252884 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b93_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 93)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 93)) 186844) = 252884 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o93 : xone 93 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a93_0 b93_0 a93_1 b93_1 a93_2 b93_2
    a93_3 b93_3 a93_4 b93_4 a93_5 b93_5

theorem a94_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 94))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 94) 0) = 60470 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b94_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 94)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 94)) 0) = 60470 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a94_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 94))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 94) 305530) = 35321 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b94_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 94)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 94)) 305530) = 35321 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a94_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 94))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 94) 5604) = 50975 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b94_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 94)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 94)) 5604) = 50975 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a94_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 94))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 94) 221549) = 261260 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b94_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 94)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 94)) 221549) = 261260 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a94_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 94))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 94) 266275) = 275762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b94_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 94)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 94)) 266275) = 275762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a94_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 94))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 94) 186844) = 234553 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b94_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 94)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 94)) 186844) = 234553 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o94 : xone 94 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a94_0 b94_0 a94_1 b94_1 a94_2 b94_2
    a94_3 b94_3 a94_4 b94_4 a94_5 b94_5

theorem a95_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 95))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 95) 0) = 10925 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b95_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 95)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 95)) 0) = 10925 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a95_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 95))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 95) 305530) = 92826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b95_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 95)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 95)) 305530) = 92826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a95_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 95))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 95) 5604) = 289545 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b95_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 95)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 95)) 5604) = 289545 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a95_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 95))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 95) 221549) = 160392 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b95_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 95)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 95)) 221549) = 160392 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a95_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 95))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 95) 266275) = 76176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b95_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 95)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 95)) 266275) = 76176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a95_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 95))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 95) 186844) = 161472 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b95_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 95)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 95)) 186844) = 161472 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o95 : xone 95 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a95_0 b95_0 a95_1 b95_1 a95_2 b95_2
    a95_3 b95_3 a95_4 b95_4 a95_5 b95_5

theorem a96_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 96))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 96) 0) = 294452 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b96_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 96)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 96)) 0) = 294452 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a96_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 96))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 96) 305530) = 29934 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b96_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 96)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 96)) 305530) = 29934 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a96_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 96))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 96) 5604) = 287551 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b96_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 96)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 96)) 5604) = 287551 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a96_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 96))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 96) 221549) = 173187 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b96_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 96)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 96)) 221549) = 173187 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a96_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 96))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 96) 266275) = 162071 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b96_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 96)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 96)) 266275) = 162071 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a96_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 96))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 96) 186844) = 62285 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b96_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 96)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 96)) 186844) = 62285 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o96 : xone 96 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a96_0 b96_0 a96_1 b96_1 a96_2 b96_2
    a96_3 b96_3 a96_4 b96_4 a96_5 b96_5

theorem a97_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 97))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 97) 0) = 167153 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b97_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 97)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 97)) 0) = 167153 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a97_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 97))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 97) 305530) = 74386 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b97_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 97)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 97)) 305530) = 74386 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a97_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 97))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 97) 5604) = 112656 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b97_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 97)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 97)) 5604) = 112656 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a97_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 97))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 97) 221549) = 13526 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b97_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 97)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 97)) 221549) = 13526 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a97_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 97))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 97) 266275) = 110255 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b97_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 97)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 97)) 266275) = 110255 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a97_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 97))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 97) 186844) = 196008 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b97_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 97)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 97)) 186844) = 196008 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o97 : xone 97 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a97_0 b97_0 a97_1 b97_1 a97_2 b97_2
    a97_3 b97_3 a97_4 b97_4 a97_5 b97_5

theorem a98_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 98))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 98) 0) = 144885 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b98_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 98)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 98)) 0) = 144885 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a98_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 98))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 98) 305530) = 113636 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b98_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 98)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 98)) 305530) = 113636 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a98_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 98))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 98) 5604) = 181723 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b98_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 98)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 98)) 5604) = 181723 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a98_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 98))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 98) 221549) = 257682 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b98_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 98)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 98)) 221549) = 257682 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a98_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 98))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 98) 266275) = 193060 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b98_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 98)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 98)) 266275) = 193060 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a98_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 98))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 98) 186844) = 117401 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b98_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 98)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 98)) 186844) = 117401 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o98 : xone 98 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a98_0 b98_0 a98_1 b98_1 a98_2 b98_2
    a98_3 b98_3 a98_4 b98_4 a98_5 b98_5

theorem a99_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 99))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 99) 0) = 206738 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b99_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 99)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 99)) 0) = 206738 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a99_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 99))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 99) 305530) = 208337 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b99_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 99)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 99)) 305530) = 208337 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a99_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 99))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 99) 5604) = 173401 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b99_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 99)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 99)) 5604) = 173401 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a99_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 99))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 99) 221549) = 60817 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b99_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 99)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 99)) 221549) = 60817 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a99_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 99))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 99) 266275) = 55358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b99_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 99)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 99)) 266275) = 55358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a99_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 99))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 99) 186844) = 228391 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b99_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 99)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 99)) 186844) = 228391 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o99 : xone 99 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a99_0 b99_0 a99_1 b99_1 a99_2 b99_2
    a99_3 b99_3 a99_4 b99_4 a99_5 b99_5

theorem a100_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 100))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 100) 0) = 221639 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b100_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 100)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 100)) 0) = 221639 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a100_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 100))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 100) 305530) = 108784 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b100_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 100)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 100)) 305530) = 108784 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a100_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 100))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 100) 5604) = 194317 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b100_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 100)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 100)) 5604) = 194317 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a100_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 100))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 100) 221549) = 6623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b100_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 100)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 100)) 221549) = 6623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a100_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 100))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 100) 266275) = 84475 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b100_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 100)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 100)) 266275) = 84475 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a100_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 100))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 100) 186844) = 61986 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b100_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 100)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 100)) 186844) = 61986 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o100 : xone 100 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a100_0 b100_0 a100_1 b100_1 a100_2 b100_2
    a100_3 b100_3 a100_4 b100_4 a100_5 b100_5

theorem a101_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 101))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 101) 0) = 110286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b101_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 101)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 101)) 0) = 110286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a101_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 101))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 101) 305530) = 63072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b101_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 101)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 101)) 305530) = 63072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a101_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 101))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 101) 5604) = 8050 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b101_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 101)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 101)) 5604) = 8050 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a101_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 101))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 101) 221549) = 39502 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b101_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 101)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 101)) 221549) = 39502 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a101_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 101))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 101) 266275) = 214991 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b101_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 101)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 101)) 266275) = 214991 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a101_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 101))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 101) 186844) = 84044 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b101_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 101)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 101)) 186844) = 84044 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o101 : xone 101 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a101_0 b101_0 a101_1 b101_1 a101_2 b101_2
    a101_3 b101_3 a101_4 b101_4 a101_5 b101_5

theorem a102_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 102))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 102) 0) = 287764 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b102_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 102)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 102)) 0) = 287764 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a102_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 102))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 102) 305530) = 140377 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b102_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 102)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 102)) 305530) = 140377 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a102_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 102))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 102) 5604) = 243263 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b102_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 102)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 102)) 5604) = 243263 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a102_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 102))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 102) 221549) = 27851 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b102_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 102)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 102)) 221549) = 27851 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a102_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 102))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 102) 266275) = 30103 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b102_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 102)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 102)) 266275) = 30103 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a102_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 102))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 102) 186844) = 168786 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b102_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 102)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 102)) 186844) = 168786 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o102 : xone 102 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a102_0 b102_0 a102_1 b102_1 a102_2 b102_2
    a102_3 b102_3 a102_4 b102_4 a102_5 b102_5

theorem a103_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 103))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 103) 0) = 184280 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b103_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 103)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 103)) 0) = 184280 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a103_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 103))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 103) 305530) = 223545 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b103_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 103)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 103)) 305530) = 223545 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a103_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 103))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 103) 5604) = 38201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b103_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 103)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 103)) 5604) = 38201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a103_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 103))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 103) 221549) = 23357 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b103_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 103)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 103)) 221549) = 23357 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a103_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 103))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 103) 266275) = 39294 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b103_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 103)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 103)) 266275) = 39294 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a103_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 103))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 103) 186844) = 142915 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b103_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 103)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 103)) 186844) = 142915 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o103 : xone 103 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a103_0 b103_0 a103_1 b103_1 a103_2 b103_2
    a103_3 b103_3 a103_4 b103_4 a103_5 b103_5

theorem a104_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 104))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 104) 0) = 178385 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b104_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 104)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 104)) 0) = 178385 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a104_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 104))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 104) 305530) = 44677 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b104_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 104)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 104)) 305530) = 44677 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a104_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 104))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 104) 5604) = 6119 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b104_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 104)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 104)) 5604) = 6119 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a104_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 104))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 104) 221549) = 167271 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b104_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 104)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 104)) 221549) = 167271 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a104_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 104))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 104) 266275) = 161987 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b104_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 104)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 104)) 266275) = 161987 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a104_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 104))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 104) 186844) = 135431 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b104_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 104)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 104)) 186844) = 135431 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o104 : xone 104 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a104_0 b104_0 a104_1 b104_1 a104_2 b104_2
    a104_3 b104_3 a104_4 b104_4 a104_5 b104_5

theorem a105_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 105))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 105) 0) = 39972 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b105_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 105)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 105)) 0) = 39972 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a105_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 105))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 105) 305530) = 142802 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b105_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 105)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 105)) 305530) = 142802 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a105_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 105))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 105) 5604) = 78299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b105_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 105)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 105)) 5604) = 78299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a105_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 105))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 105) 221549) = 10617 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b105_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 105)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 105)) 221549) = 10617 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a105_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 105))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 105) 266275) = 205809 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b105_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 105)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 105)) 266275) = 205809 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a105_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 105))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 105) 186844) = 18993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b105_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 105)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 105)) 186844) = 18993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o105 : xone 105 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a105_0 b105_0 a105_1 b105_1 a105_2 b105_2
    a105_3 b105_3 a105_4 b105_4 a105_5 b105_5

theorem a106_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 106))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 106) 0) = 251128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b106_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 106)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 106)) 0) = 251128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a106_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 106))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 106) 305530) = 203184 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b106_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 106)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 106)) 305530) = 203184 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a106_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 106))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 106) 5604) = 73504 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b106_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 106)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 106)) 5604) = 73504 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a106_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 106))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 106) 221549) = 112310 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b106_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 106)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 106)) 221549) = 112310 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a106_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 106))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 106) 266275) = 27877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b106_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 106)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 106)) 266275) = 27877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a106_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 106))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 106) 186844) = 184468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b106_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 106)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 106)) 186844) = 184468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o106 : xone 106 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a106_0 b106_0 a106_1 b106_1 a106_2 b106_2
    a106_3 b106_3 a106_4 b106_4 a106_5 b106_5

theorem a107_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 107))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 107) 0) = 286449 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b107_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 107)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 107)) 0) = 286449 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a107_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 107))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 107) 305530) = 39525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b107_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 107)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 107)) 305530) = 39525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a107_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 107))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 107) 5604) = 110085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b107_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 107)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 107)) 5604) = 110085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a107_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 107))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 107) 221549) = 234470 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b107_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 107)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 107)) 221549) = 234470 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a107_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 107))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 107) 266275) = 218264 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b107_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 107)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 107)) 266275) = 218264 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a107_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 107))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 107) 186844) = 14728 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b107_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 107)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 107)) 186844) = 14728 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o107 : xone 107 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a107_0 b107_0 a107_1 b107_1 a107_2 b107_2
    a107_3 b107_3 a107_4 b107_4 a107_5 b107_5

theorem a108_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 108))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 108) 0) = 209569 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b108_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 108)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 108)) 0) = 209569 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a108_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 108))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 108) 305530) = 256191 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b108_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 108)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 108)) 305530) = 256191 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a108_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 108))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 108) 5604) = 129926 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b108_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 108)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 108)) 5604) = 129926 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a108_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 108))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 108) 221549) = 73642 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b108_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 108)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 108)) 221549) = 73642 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a108_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 108))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 108) 266275) = 107102 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b108_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 108)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 108)) 266275) = 107102 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a108_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 108))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 108) 186844) = 153049 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b108_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 108)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 108)) 186844) = 153049 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o108 : xone 108 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a108_0 b108_0 a108_1 b108_1 a108_2 b108_2
    a108_3 b108_3 a108_4 b108_4 a108_5 b108_5

theorem a109_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 109))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 109) 0) = 54051 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b109_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 109)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 109)) 0) = 54051 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a109_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 109))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 109) 305530) = 291161 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b109_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 109)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 109)) 305530) = 291161 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a109_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 109))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 109) 5604) = 181077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b109_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 109)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 109)) 5604) = 181077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a109_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 109))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 109) 221549) = 162898 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b109_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 109)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 109)) 221549) = 162898 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a109_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 109))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 109) 266275) = 42501 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b109_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 109)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 109)) 266275) = 42501 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a109_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 109))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 109) 186844) = 182848 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b109_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 109)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 109)) 186844) = 182848 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o109 : xone 109 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a109_0 b109_0 a109_1 b109_1 a109_2 b109_2
    a109_3 b109_3 a109_4 b109_4 a109_5 b109_5

theorem a110_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 110))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 110) 0) = 97707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b110_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 110)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 110)) 0) = 97707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a110_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 110))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 110) 305530) = 176260 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b110_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 110)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 110)) 305530) = 176260 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a110_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 110))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 110) 5604) = 255678 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b110_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 110)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 110)) 5604) = 255678 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a110_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 110))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 110) 221549) = 291709 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b110_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 110)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 110)) 221549) = 291709 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a110_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 110))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 110) 266275) = 233027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b110_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 110)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 110)) 266275) = 233027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a110_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 110))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 110) 186844) = 85192 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b110_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 110)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 110)) 186844) = 85192 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o110 : xone 110 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a110_0 b110_0 a110_1 b110_1 a110_2 b110_2
    a110_3 b110_3 a110_4 b110_4 a110_5 b110_5

theorem a111_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 111))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 111) 0) = 218028 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b111_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 111)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 111)) 0) = 218028 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a111_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 111))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 111) 305530) = 91012 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b111_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 111)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 111)) 305530) = 91012 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a111_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 111))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 111) 5604) = 255075 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b111_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 111)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 111)) 5604) = 255075 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a111_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 111))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 111) 221549) = 195713 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b111_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 111)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 111)) 221549) = 195713 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a111_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 111))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 111) 266275) = 301234 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b111_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 111)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 111)) 266275) = 301234 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a111_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 111))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 111) 186844) = 276855 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b111_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 111)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 111)) 186844) = 276855 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o111 : xone 111 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a111_0 b111_0 a111_1 b111_1 a111_2 b111_2
    a111_3 b111_3 a111_4 b111_4 a111_5 b111_5

theorem a112_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 112))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 112) 0) = 125251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b112_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 112)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 112)) 0) = 125251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a112_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 112))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 112) 305530) = 97290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b112_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 112)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 112)) 305530) = 97290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a112_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 112))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 112) 5604) = 291941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b112_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 112)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 112)) 5604) = 291941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a112_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 112))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 112) 221549) = 273859 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b112_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 112)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 112)) 221549) = 273859 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a112_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 112))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 112) 266275) = 84449 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b112_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 112)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 112)) 266275) = 84449 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a112_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 112))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 112) 186844) = 254284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b112_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 112)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 112)) 186844) = 254284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o112 : xone 112 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a112_0 b112_0 a112_1 b112_1 a112_2 b112_2
    a112_3 b112_3 a112_4 b112_4 a112_5 b112_5

theorem a113_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 113))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 113) 0) = 194471 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b113_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 113)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 113)) 0) = 194471 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a113_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 113))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 113) 305530) = 184362 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b113_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 113)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 113)) 305530) = 184362 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a113_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 113))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 113) 5604) = 193210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b113_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 113)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 113)) 5604) = 193210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a113_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 113))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 113) 221549) = 15606 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b113_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 113)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 113)) 221549) = 15606 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a113_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 113))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 113) 266275) = 174223 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b113_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 113)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 113)) 266275) = 174223 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a113_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 113))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 113) 186844) = 134955 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b113_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 113)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 113)) 186844) = 134955 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o113 : xone 113 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a113_0 b113_0 a113_1 b113_1 a113_2 b113_2
    a113_3 b113_3 a113_4 b113_4 a113_5 b113_5

theorem a114_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 114))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 114) 0) = 228563 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b114_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 114)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 114)) 0) = 228563 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a114_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 114))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 114) 305530) = 171291 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b114_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 114)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 114)) 305530) = 171291 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a114_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 114))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 114) 5604) = 49816 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b114_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 114)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 114)) 5604) = 49816 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a114_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 114))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 114) 221549) = 172770 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b114_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 114)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 114)) 221549) = 172770 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a114_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 114))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 114) 266275) = 146538 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b114_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 114)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 114)) 266275) = 146538 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a114_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 114))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 114) 186844) = 97388 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b114_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 114)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 114)) 186844) = 97388 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o114 : xone 114 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a114_0 b114_0 a114_1 b114_1 a114_2 b114_2
    a114_3 b114_3 a114_4 b114_4 a114_5 b114_5

theorem a115_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 115))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 115) 0) = 56732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b115_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 115)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 115)) 0) = 56732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a115_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 115))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 115) 305530) = 140474 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b115_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 115)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 115)) 305530) = 140474 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a115_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 115))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 115) 5604) = 181169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b115_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 115)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 115)) 5604) = 181169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a115_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 115))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 115) 221549) = 223420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b115_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 115)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 115)) 221549) = 223420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a115_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 115))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 115) 266275) = 78744 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b115_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 115)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 115)) 266275) = 78744 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a115_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 115))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 115) 186844) = 35413 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b115_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 115)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 115)) 186844) = 35413 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o115 : xone 115 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a115_0 b115_0 a115_1 b115_1 a115_2 b115_2
    a115_3 b115_3 a115_4 b115_4 a115_5 b115_5

theorem a116_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 116))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 116) 0) = 235533 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b116_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 116)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 116)) 0) = 235533 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a116_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 116))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 116) 305530) = 115923 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b116_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 116)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 116)) 305530) = 115923 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a116_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 116))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 116) 5604) = 189243 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b116_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 116)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 116)) 5604) = 189243 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a116_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 116))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 116) 221549) = 75583 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b116_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 116)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 116)) 221549) = 75583 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a116_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 116))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 116) 266275) = 171260 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b116_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 116)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 116)) 266275) = 171260 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a116_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 116))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 116) 186844) = 10251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b116_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 116)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 116)) 186844) = 10251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o116 : xone 116 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a116_0 b116_0 a116_1 b116_1 a116_2 b116_2
    a116_3 b116_3 a116_4 b116_4 a116_5 b116_5

theorem a117_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 117))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 117) 0) = 260859 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b117_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 117)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 117)) 0) = 260859 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a117_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 117))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 117) 305530) = 150230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b117_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 117)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 117)) 305530) = 150230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a117_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 117))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 117) 5604) = 244837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b117_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 117)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 117)) 5604) = 244837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a117_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 117))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 117) 221549) = 108487 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b117_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 117)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 117)) 221549) = 108487 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a117_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 117))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 117) 266275) = 44578 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b117_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 117)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 117)) 266275) = 44578 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a117_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 117))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 117) 186844) = 267125 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b117_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 117)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 117)) 186844) = 267125 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o117 : xone 117 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a117_0 b117_0 a117_1 b117_1 a117_2 b117_2
    a117_3 b117_3 a117_4 b117_4 a117_5 b117_5

theorem a118_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 118))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 118) 0) = 10140 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b118_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 118)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 118)) 0) = 10140 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a118_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 118))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 118) 305530) = 233454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b118_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 118)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 118)) 305530) = 233454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a118_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 118))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 118) 5604) = 131369 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b118_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 118)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 118)) 5604) = 131369 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a118_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 118))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 118) 221549) = 154021 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b118_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 118)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 118)) 221549) = 154021 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a118_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 118))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 118) 266275) = 280156 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b118_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 118)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 118)) 266275) = 280156 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a118_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 118))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 118) 186844) = 149620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b118_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 118)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 118)) 186844) = 149620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o118 : xone 118 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a118_0 b118_0 a118_1 b118_1 a118_2 b118_2
    a118_3 b118_3 a118_4 b118_4 a118_5 b118_5

theorem a119_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 119))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 119) 0) = 260383 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b119_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 119)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 119)) 0) = 260383 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a119_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 119))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 119) 305530) = 212224 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b119_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 119)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 119)) 305530) = 212224 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a119_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 119))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 119) 5604) = 217846 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b119_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 119)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 119)) 5604) = 217846 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a119_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 119))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 119) 221549) = 216004 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b119_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 119)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 119)) 221549) = 216004 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a119_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 119))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 119) 266275) = 34831 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b119_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 119)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 119)) 266275) = 34831 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a119_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 119))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 119) 186844) = 87249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b119_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 119)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 119)) 186844) = 87249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o119 : xone 119 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a119_0 b119_0 a119_1 b119_1 a119_2 b119_2
    a119_3 b119_3 a119_4 b119_4 a119_5 b119_5

theorem a120_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 120))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 120) 0) = 141573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b120_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 120)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 120)) 0) = 141573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a120_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 120))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 120) 305530) = 171545 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b120_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 120)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 120)) 305530) = 171545 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a120_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 120))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 120) 5604) = 291418 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b120_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 120)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 120)) 5604) = 291418 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a120_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 120))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 120) 221549) = 207098 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b120_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 120)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 120)) 221549) = 207098 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a120_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 120))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 120) 266275) = 95915 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b120_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 120)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 120)) 266275) = 95915 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a120_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 120))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 120) 186844) = 61806 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b120_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 120)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 120)) 186844) = 61806 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o120 : xone 120 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a120_0 b120_0 a120_1 b120_1 a120_2 b120_2
    a120_3 b120_3 a120_4 b120_4 a120_5 b120_5

theorem a121_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 121))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 121) 0) = 232779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b121_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 121)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 121)) 0) = 232779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a121_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 121))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 121) 305530) = 195295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b121_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 121)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 121)) 305530) = 195295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a121_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 121))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 121) 5604) = 266623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b121_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 121)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 121)) 5604) = 266623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a121_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 121))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 121) 221549) = 162852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b121_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 121)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 121)) 221549) = 162852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a121_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 121))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 121) 266275) = 124315 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b121_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 121)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 121)) 266275) = 124315 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a121_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 121))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 121) 186844) = 298364 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b121_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 121)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 121)) 186844) = 298364 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o121 : xone 121 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a121_0 b121_0 a121_1 b121_1 a121_2 b121_2
    a121_3 b121_3 a121_4 b121_4 a121_5 b121_5

theorem a122_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 122))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 122) 0) = 292243 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b122_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 122)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 122)) 0) = 292243 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a122_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 122))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 122) 305530) = 291093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b122_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 122)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 122)) 305530) = 291093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a122_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 122))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 122) 5604) = 169434 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b122_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 122)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 122)) 5604) = 169434 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a122_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 122))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 122) 221549) = 102522 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b122_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 122)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 122)) 221549) = 102522 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a122_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 122))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 122) 266275) = 225366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b122_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 122)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 122)) 266275) = 225366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a122_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 122))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 122) 186844) = 53157 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b122_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 122)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 122)) 186844) = 53157 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o122 : xone 122 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a122_0 b122_0 a122_1 b122_1 a122_2 b122_2
    a122_3 b122_3 a122_4 b122_4 a122_5 b122_5

theorem a123_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 123))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 123) 0) = 39837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b123_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 123)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 123)) 0) = 39837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a123_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 123))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 123) 305530) = 224867 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b123_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 123)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 123)) 305530) = 224867 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a123_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 123))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 123) 5604) = 209514 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b123_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 123)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 123)) 5604) = 209514 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a123_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 123))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 123) 221549) = 19254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b123_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 123)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 123)) 221549) = 19254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a123_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 123))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 123) 266275) = 70828 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b123_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 123)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 123)) 266275) = 70828 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a123_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 123))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 123) 186844) = 190202 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b123_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 123)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 123)) 186844) = 190202 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o123 : xone 123 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a123_0 b123_0 a123_1 b123_1 a123_2 b123_2
    a123_3 b123_3 a123_4 b123_4 a123_5 b123_5

theorem a124_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 124))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 124) 0) = 225442 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b124_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 124)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 124)) 0) = 225442 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a124_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 124))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 124) 305530) = 88236 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b124_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 124)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 124)) 305530) = 88236 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a124_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 124))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 124) 5604) = 139766 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b124_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 124)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 124)) 5604) = 139766 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a124_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 124))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 124) 221549) = 118286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b124_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 124)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 124)) 221549) = 118286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a124_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 124))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 124) 266275) = 250381 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b124_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 124)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 124)) 266275) = 250381 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a124_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 124))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 124) 186844) = 40005 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b124_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 124)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 124)) 186844) = 40005 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o124 : xone 124 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a124_0 b124_0 a124_1 b124_1 a124_2 b124_2
    a124_3 b124_3 a124_4 b124_4 a124_5 b124_5

theorem a125_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 125))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 125) 0) = 83545 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b125_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 125)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 125)) 0) = 83545 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a125_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 125))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 125) 305530) = 233048 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b125_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 125)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 125)) 305530) = 233048 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a125_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 125))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 125) 5604) = 229154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b125_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 125)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 125)) 5604) = 229154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a125_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 125))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 125) 221549) = 39853 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b125_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 125)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 125)) 221549) = 39853 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a125_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 125))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 125) 266275) = 69714 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b125_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 125)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 125)) 266275) = 69714 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a125_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 125))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 125) 186844) = 108640 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b125_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 125)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 125)) 186844) = 108640 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o125 : xone 125 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a125_0 b125_0 a125_1 b125_1 a125_2 b125_2
    a125_3 b125_3 a125_4 b125_4 a125_5 b125_5

theorem a126_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 126))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 126) 0) = 37799 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b126_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 126)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 126)) 0) = 37799 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a126_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 126))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 126) 305530) = 255731 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b126_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 126)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 126)) 305530) = 255731 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a126_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 126))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 126) 5604) = 122337 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b126_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 126)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 126)) 5604) = 122337 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a126_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 126))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 126) 221549) = 259109 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b126_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 126)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 126)) 221549) = 259109 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a126_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 126))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 126) 266275) = 5205 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b126_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 126)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 126)) 266275) = 5205 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a126_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 126))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 126) 186844) = 287872 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b126_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 126)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 126)) 186844) = 287872 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o126 : xone 126 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a126_0 b126_0 a126_1 b126_1 a126_2 b126_2
    a126_3 b126_3 a126_4 b126_4 a126_5 b126_5

theorem a127_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 127))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 127) 0) = 289824 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b127_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 127)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 127)) 0) = 289824 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a127_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 127))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 127) 305530) = 306473 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b127_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 127)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 127)) 305530) = 306473 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a127_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 127))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 127) 5604) = 305640 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b127_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 127)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 127)) 5604) = 305640 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a127_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 127))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 127) 221549) = 172977 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b127_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 127)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 127)) 221549) = 172977 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a127_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 127))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 127) 266275) = 68282 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b127_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 127)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 127)) 266275) = 68282 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a127_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 127))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 127) 186844) = 135623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b127_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 127)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 127)) 186844) = 135623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o127 : xone 127 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a127_0 b127_0 a127_1 b127_1 a127_2 b127_2
    a127_3 b127_3 a127_4 b127_4 a127_5 b127_5

theorem a128_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 128))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 128) 0) = 172472 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b128_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 128)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 128)) 0) = 172472 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a128_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 128))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 128) 305530) = 127847 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b128_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 128)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 128)) 305530) = 127847 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a128_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 128))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 128) 5604) = 58538 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b128_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 128)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 128)) 5604) = 58538 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a128_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 128))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 128) 221549) = 141420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b128_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 128)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 128)) 221549) = 141420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a128_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 128))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 128) 266275) = 105776 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b128_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 128)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 128)) 266275) = 105776 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a128_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 128))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 128) 186844) = 268320 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b128_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 128)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 128)) 186844) = 268320 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o128 : xone 128 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a128_0 b128_0 a128_1 b128_1 a128_2 b128_2
    a128_3 b128_3 a128_4 b128_4 a128_5 b128_5

theorem a129_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 129))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 129) 0) = 151158 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b129_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 129)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 129)) 0) = 151158 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a129_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 129))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 129) 305530) = 172226 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b129_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 129)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 129)) 305530) = 172226 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a129_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 129))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 129) 5604) = 239762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b129_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 129)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 129)) 5604) = 239762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a129_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 129))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 129) 221549) = 173194 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b129_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 129)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 129)) 221549) = 173194 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a129_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 129))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 129) 266275) = 166215 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b129_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 129)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 129)) 266275) = 166215 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a129_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 129))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 129) 186844) = 304707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b129_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 129)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 129)) 186844) = 304707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o129 : xone 129 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a129_0 b129_0 a129_1 b129_1 a129_2 b129_2
    a129_3 b129_3 a129_4 b129_4 a129_5 b129_5

theorem a130_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 130))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 130) 0) = 293436 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b130_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 130)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 130)) 0) = 293436 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a130_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 130))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 130) 305530) = 86659 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b130_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 130)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 130)) 305530) = 86659 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a130_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 130))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 130) 5604) = 63242 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b130_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 130)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 130)) 5604) = 63242 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a130_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 130))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 130) 221549) = 193103 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b130_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 130)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 130)) 221549) = 193103 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a130_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 130))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 130) 266275) = 147742 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b130_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 130)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 130)) 266275) = 147742 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a130_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 130))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 130) 186844) = 166441 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b130_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 130)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 130)) 186844) = 166441 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o130 : xone 130 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a130_0 b130_0 a130_1 b130_1 a130_2 b130_2
    a130_3 b130_3 a130_4 b130_4 a130_5 b130_5

theorem a131_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 131))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 131) 0) = 35657 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b131_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 131)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 131)) 0) = 35657 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a131_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 131))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 131) 305530) = 31807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b131_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 131)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 131)) 305530) = 31807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a131_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 131))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 131) 5604) = 94677 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b131_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 131)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 131)) 5604) = 94677 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a131_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 131))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 131) 221549) = 188833 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b131_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 131)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 131)) 221549) = 188833 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a131_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 131))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 131) 266275) = 200259 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b131_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 131)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 131)) 266275) = 200259 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a131_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 131))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 131) 186844) = 244289 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b131_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 131)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 131)) 186844) = 244289 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o131 : xone 131 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a131_0 b131_0 a131_1 b131_1 a131_2 b131_2
    a131_3 b131_3 a131_4 b131_4 a131_5 b131_5

theorem a132_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 132))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 132) 0) = 218579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b132_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 132)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 132)) 0) = 218579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a132_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 132))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 132) 305530) = 138364 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b132_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 132)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 132)) 305530) = 138364 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a132_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 132))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 132) 5604) = 210653 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b132_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 132)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 132)) 5604) = 210653 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a132_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 132))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 132) 221549) = 123080 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b132_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 132)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 132)) 221549) = 123080 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a132_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 132))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 132) 266275) = 119100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b132_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 132)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 132)) 266275) = 119100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a132_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 132))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 132) 186844) = 175381 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b132_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 132)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 132)) 186844) = 175381 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o132 : xone 132 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a132_0 b132_0 a132_1 b132_1 a132_2 b132_2
    a132_3 b132_3 a132_4 b132_4 a132_5 b132_5

theorem a133_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 133))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 133) 0) = 141278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b133_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 133)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 133)) 0) = 141278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a133_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 133))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 133) 305530) = 211716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b133_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 133)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 133)) 305530) = 211716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a133_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 133))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 133) 5604) = 288734 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b133_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 133)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 133)) 5604) = 288734 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a133_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 133))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 133) 221549) = 87575 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b133_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 133)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 133)) 221549) = 87575 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a133_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 133))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 133) 266275) = 194178 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b133_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 133)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 133)) 266275) = 194178 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a133_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 133))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 133) 186844) = 54817 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b133_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 133)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 133)) 186844) = 54817 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o133 : xone 133 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a133_0 b133_0 a133_1 b133_1 a133_2 b133_2
    a133_3 b133_3 a133_4 b133_4 a133_5 b133_5

theorem a134_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 134))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 134) 0) = 225532 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b134_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 134)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 134)) 0) = 225532 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a134_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 134))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 134) 305530) = 67291 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b134_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 134)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 134)) 305530) = 67291 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a134_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 134))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 134) 5604) = 286572 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b134_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 134)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 134)) 5604) = 286572 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a134_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 134))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 134) 221549) = 200865 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b134_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 134)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 134)) 221549) = 200865 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a134_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 134))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 134) 266275) = 62618 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b134_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 134)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 134)) 266275) = 62618 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a134_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 134))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 134) 186844) = 238163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b134_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 134)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 134)) 186844) = 238163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o134 : xone 134 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a134_0 b134_0 a134_1 b134_1 a134_2 b134_2
    a134_3 b134_3 a134_4 b134_4 a134_5 b134_5

theorem a135_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 135))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 135) 0) = 106073 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b135_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 135)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 135)) 0) = 106073 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a135_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 135))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 135) 305530) = 36788 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b135_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 135)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 135)) 305530) = 36788 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a135_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 135))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 135) 5604) = 39188 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b135_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 135)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 135)) 5604) = 39188 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a135_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 135))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 135) 221549) = 217145 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b135_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 135)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 135)) 221549) = 217145 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a135_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 135))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 135) 266275) = 91702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b135_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 135)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 135)) 266275) = 91702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a135_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 135))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 135) 186844) = 79747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b135_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 135)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 135)) 186844) = 79747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o135 : xone 135 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a135_0 b135_0 a135_1 b135_1 a135_2 b135_2
    a135_3 b135_3 a135_4 b135_4 a135_5 b135_5

theorem a136_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 136))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 136) 0) = 47038 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b136_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 136)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 136)) 0) = 47038 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a136_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 136))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 136) 305530) = 156431 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b136_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 136)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 136)) 305530) = 156431 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a136_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 136))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 136) 5604) = 295384 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b136_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 136)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 136)) 5604) = 295384 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a136_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 136))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 136) 221549) = 68722 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b136_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 136)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 136)) 221549) = 68722 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a136_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 136))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 136) 266275) = 152448 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b136_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 136)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 136)) 266275) = 152448 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a136_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 136))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 136) 186844) = 188809 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b136_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 136)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 136)) 186844) = 188809 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o136 : xone 136 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a136_0 b136_0 a136_1 b136_1 a136_2 b136_2
    a136_3 b136_3 a136_4 b136_4 a136_5 b136_5

theorem a137_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 137))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 137) 0) = 189152 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b137_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 137)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 137)) 0) = 189152 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a137_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 137))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 137) 305530) = 59188 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b137_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 137)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 137)) 305530) = 59188 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a137_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 137))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 137) 5604) = 55207 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b137_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 137)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 137)) 5604) = 55207 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a137_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 137))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 137) 221549) = 225516 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b137_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 137)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 137)) 221549) = 225516 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a137_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 137))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 137) 266275) = 121885 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b137_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 137)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 137)) 266275) = 121885 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a137_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 137))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 137) 186844) = 178531 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b137_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 137)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 137)) 186844) = 178531 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o137 : xone 137 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a137_0 b137_0 a137_1 b137_1 a137_2 b137_2
    a137_3 b137_3 a137_4 b137_4 a137_5 b137_5

theorem a138_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 138))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 138) 0) = 21405 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b138_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 138)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 138)) 0) = 21405 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a138_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 138))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 138) 305530) = 124324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b138_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 138)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 138)) 305530) = 124324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a138_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 138))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 138) 5604) = 48786 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b138_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 138)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 138)) 5604) = 48786 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a138_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 138))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 138) 221549) = 146747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b138_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 138)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 138)) 221549) = 146747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a138_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 138))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 138) 266275) = 156549 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b138_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 138)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 138)) 266275) = 156549 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a138_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 138))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 138) 186844) = 197448 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b138_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 138)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 138)) 186844) = 197448 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o138 : xone 138 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a138_0 b138_0 a138_1 b138_1 a138_2 b138_2
    a138_3 b138_3 a138_4 b138_4 a138_5 b138_5

theorem a139_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 139))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 139) 0) = 162056 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b139_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 139)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 139)) 0) = 162056 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a139_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 139))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 139) 305530) = 27147 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b139_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 139)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 139)) 305530) = 27147 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a139_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 139))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 139) 5604) = 5210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b139_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 139)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 139)) 5604) = 5210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a139_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 139))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 139) 221549) = 220287 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b139_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 139)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 139)) 221549) = 220287 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a139_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 139))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 139) 266275) = 229752 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b139_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 139)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 139)) 266275) = 229752 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a139_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 139))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 139) 186844) = 82784 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b139_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 139)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 139)) 186844) = 82784 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o139 : xone 139 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a139_0 b139_0 a139_1 b139_1 a139_2 b139_2
    a139_3 b139_3 a139_4 b139_4 a139_5 b139_5

theorem a140_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 140))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 140) 0) = 114672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b140_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 140)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 140)) 0) = 114672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a140_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 140))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 140) 305530) = 293391 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b140_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 140)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 140)) 305530) = 293391 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a140_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 140))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 140) 5604) = 129872 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b140_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 140)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 140)) 5604) = 129872 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a140_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 140))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 140) 221549) = 150668 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b140_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 140)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 140)) 221549) = 150668 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a140_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 140))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 140) 266275) = 120106 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b140_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 140)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 140)) 266275) = 120106 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a140_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 140))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 140) 186844) = 113621 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b140_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 140)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 140)) 186844) = 113621 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o140 : xone 140 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a140_0 b140_0 a140_1 b140_1 a140_2 b140_2
    a140_3 b140_3 a140_4 b140_4 a140_5 b140_5

theorem a141_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 141))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 141) 0) = 107701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b141_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 141)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 141)) 0) = 107701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a141_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 141))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 141) 305530) = 83199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b141_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 141)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 141)) 305530) = 83199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a141_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 141))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 141) 5604) = 134956 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b141_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 141)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 141)) 5604) = 134956 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a141_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 141))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 141) 221549) = 246831 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b141_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 141)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 141)) 221549) = 246831 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a141_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 141))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 141) 266275) = 222170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b141_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 141)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 141)) 266275) = 222170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a141_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 141))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 141) 186844) = 239289 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b141_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 141)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 141)) 186844) = 239289 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o141 : xone 141 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a141_0 b141_0 a141_1 b141_1 a141_2 b141_2
    a141_3 b141_3 a141_4 b141_4 a141_5 b141_5

theorem a142_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 142))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 142) 0) = 87900 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b142_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 142)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 142)) 0) = 87900 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a142_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 142))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 142) 305530) = 304762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b142_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 142)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 142)) 305530) = 304762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a142_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 142))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 142) 5604) = 190025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b142_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 142)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 142)) 5604) = 190025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a142_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 142))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 142) 221549) = 295393 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b142_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 142)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 142)) 221549) = 295393 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a142_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 142))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 142) 266275) = 147746 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b142_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 142)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 142)) 266275) = 147746 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a142_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 142))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 142) 186844) = 217940 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b142_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 142)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 142)) 186844) = 217940 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o142 : xone 142 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a142_0 b142_0 a142_1 b142_1 a142_2 b142_2
    a142_3 b142_3 a142_4 b142_4 a142_5 b142_5

theorem a143_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 143))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 143) 0) = 283740 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b143_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 143)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 143)) 0) = 283740 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a143_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 143))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 143) 305530) = 213295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b143_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 143)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 143)) 305530) = 213295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a143_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 143))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 143) 5604) = 188454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b143_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 143)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 143)) 5604) = 188454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a143_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 143))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 143) 221549) = 180526 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b143_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 143)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 143)) 221549) = 180526 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a143_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 143))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 143) 266275) = 114814 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b143_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 143)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 143)) 266275) = 114814 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a143_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 143))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 143) 186844) = 145552 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b143_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 143)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 143)) 186844) = 145552 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o143 : xone 143 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a143_0 b143_0 a143_1 b143_1 a143_2 b143_2
    a143_3 b143_3 a143_4 b143_4 a143_5 b143_5

theorem a144_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 144))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 144) 0) = 231342 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b144_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 144)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 144)) 0) = 231342 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a144_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 144))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 144) 305530) = 198870 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b144_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 144)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 144)) 305530) = 198870 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a144_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 144))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 144) 5604) = 48827 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b144_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 144)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 144)) 5604) = 48827 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a144_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 144))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 144) 221549) = 76338 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b144_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 144)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 144)) 221549) = 76338 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a144_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 144))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 144) 266275) = 266653 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b144_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 144)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 144)) 266275) = 266653 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a144_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 144))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 144) 186844) = 227137 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b144_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 144)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 144)) 186844) = 227137 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o144 : xone 144 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a144_0 b144_0 a144_1 b144_1 a144_2 b144_2
    a144_3 b144_3 a144_4 b144_4 a144_5 b144_5

theorem a145_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 145))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 145) 0) = 48574 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b145_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 145)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 145)) 0) = 48574 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a145_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 145))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 145) 305530) = 84630 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b145_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 145)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 145)) 305530) = 84630 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a145_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 145))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 145) 5604) = 126231 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b145_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 145)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 145)) 5604) = 126231 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a145_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 145))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 145) 221549) = 189592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b145_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 145)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 145)) 221549) = 189592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a145_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 145))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 145) 266275) = 207912 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b145_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 145)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 145)) 266275) = 207912 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a145_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 145))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 145) 186844) = 184611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b145_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 145)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 145)) 186844) = 184611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o145 : xone 145 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a145_0 b145_0 a145_1 b145_1 a145_2 b145_2
    a145_3 b145_3 a145_4 b145_4 a145_5 b145_5

theorem a146_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 146))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 146) 0) = 221197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b146_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 146)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 146)) 0) = 221197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a146_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 146))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 146) 305530) = 270407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b146_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 146)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 146)) 305530) = 270407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a146_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 146))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 146) 5604) = 228419 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b146_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 146)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 146)) 5604) = 228419 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a146_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 146))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 146) 221549) = 147719 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b146_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 146)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 146)) 221549) = 147719 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a146_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 146))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 146) 266275) = 252140 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b146_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 146)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 146)) 266275) = 252140 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a146_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 146))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 146) 186844) = 184363 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b146_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 146)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 146)) 186844) = 184363 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o146 : xone 146 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a146_0 b146_0 a146_1 b146_1 a146_2 b146_2
    a146_3 b146_3 a146_4 b146_4 a146_5 b146_5

theorem a147_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 147))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 147) 0) = 235299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b147_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 147)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 147)) 0) = 235299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a147_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 147))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 147) 305530) = 268667 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b147_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 147)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 147)) 305530) = 268667 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a147_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 147))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 147) 5604) = 194593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b147_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 147)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 147)) 5604) = 194593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a147_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 147))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 147) 221549) = 117699 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b147_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 147)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 147)) 221549) = 117699 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a147_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 147))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 147) 266275) = 230801 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b147_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 147)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 147)) 266275) = 230801 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a147_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 147))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 147) 186844) = 90046 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b147_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 147)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 147)) 186844) = 90046 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o147 : xone 147 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a147_0 b147_0 a147_1 b147_1 a147_2 b147_2
    a147_3 b147_3 a147_4 b147_4 a147_5 b147_5

theorem a148_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 148))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 148) 0) = 96082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b148_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 148)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 148)) 0) = 96082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a148_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 148))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 148) 305530) = 110801 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b148_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 148)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 148)) 305530) = 110801 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a148_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 148))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 148) 5604) = 305825 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b148_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 148)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 148)) 5604) = 305825 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a148_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 148))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 148) 221549) = 213077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b148_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 148)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 148)) 221549) = 213077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a148_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 148))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 148) 266275) = 234673 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b148_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 148)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 148)) 266275) = 234673 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a148_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 148))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 148) 186844) = 63976 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b148_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 148)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 148)) 186844) = 63976 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o148 : xone 148 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a148_0 b148_0 a148_1 b148_1 a148_2 b148_2
    a148_3 b148_3 a148_4 b148_4 a148_5 b148_5

theorem a149_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 149))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 149) 0) = 227251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b149_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 149)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 149)) 0) = 227251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a149_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 149))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 149) 305530) = 172558 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b149_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 149)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 149)) 305530) = 172558 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a149_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 149))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 149) 5604) = 266692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b149_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 149)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 149)) 5604) = 266692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a149_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 149))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 149) 221549) = 137019 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b149_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 149)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 149)) 221549) = 137019 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a149_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 149))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 149) 266275) = 298634 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b149_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 149)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 149)) 266275) = 298634 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a149_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 149))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 149) 186844) = 169410 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b149_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 149)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 149)) 186844) = 169410 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o149 : xone 149 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a149_0 b149_0 a149_1 b149_1 a149_2 b149_2
    a149_3 b149_3 a149_4 b149_4 a149_5 b149_5

theorem a150_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 150))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 150) 0) = 297650 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b150_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 150)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 150)) 0) = 297650 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a150_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 150))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 150) 305530) = 294182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b150_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 150)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 150)) 305530) = 294182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a150_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 150))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 150) 5604) = 92933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b150_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 150)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 150)) 5604) = 92933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a150_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 150))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 150) 221549) = 188835 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b150_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 150)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 150)) 221549) = 188835 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a150_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 150))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 150) 266275) = 190604 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b150_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 150)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 150)) 266275) = 190604 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a150_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 150))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 150) 186844) = 61463 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b150_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 150)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 150)) 186844) = 61463 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o150 : xone 150 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a150_0 b150_0 a150_1 b150_1 a150_2 b150_2
    a150_3 b150_3 a150_4 b150_4 a150_5 b150_5

theorem a151_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 151))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 151) 0) = 2182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b151_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 151)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 151)) 0) = 2182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a151_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 151))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 151) 305530) = 166947 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b151_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 151)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 151)) 305530) = 166947 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a151_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 151))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 151) 5604) = 22796 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b151_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 151)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 151)) 5604) = 22796 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a151_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 151))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 151) 221549) = 198804 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b151_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 151)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 151)) 221549) = 198804 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a151_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 151))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 151) 266275) = 252730 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b151_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 151)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 151)) 266275) = 252730 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a151_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 151))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 151) 186844) = 199483 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b151_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 151)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 151)) 186844) = 199483 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o151 : xone 151 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a151_0 b151_0 a151_1 b151_1 a151_2 b151_2
    a151_3 b151_3 a151_4 b151_4 a151_5 b151_5

theorem a152_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 152))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 152) 0) = 298199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b152_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 152)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 152)) 0) = 298199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a152_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 152))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 152) 305530) = 199306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b152_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 152)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 152)) 305530) = 199306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a152_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 152))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 152) 5604) = 149200 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b152_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 152)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 152)) 5604) = 149200 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a152_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 152))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 152) 221549) = 177036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b152_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 152)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 152)) 221549) = 177036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a152_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 152))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 152) 266275) = 264592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b152_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 152)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 152)) 266275) = 264592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a152_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 152))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 152) 186844) = 91065 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b152_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 152)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 152)) 186844) = 91065 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o152 : xone 152 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a152_0 b152_0 a152_1 b152_1 a152_2 b152_2
    a152_3 b152_3 a152_4 b152_4 a152_5 b152_5

theorem a153_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 153))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 153) 0) = 162877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b153_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 153)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 153)) 0) = 162877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a153_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 153))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 153) 305530) = 111433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b153_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 153)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 153)) 305530) = 111433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a153_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 153))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 153) 5604) = 156765 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b153_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 153)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 153)) 5604) = 156765 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a153_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 153))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 153) 221549) = 142756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b153_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 153)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 153)) 221549) = 142756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a153_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 153))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 153) 266275) = 63516 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b153_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 153)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 153)) 266275) = 63516 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a153_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 153))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 153) 186844) = 61843 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b153_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 153)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 153)) 186844) = 61843 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o153 : xone 153 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a153_0 b153_0 a153_1 b153_1 a153_2 b153_2
    a153_3 b153_3 a153_4 b153_4 a153_5 b153_5

theorem a154_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 154))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 154) 0) = 43254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b154_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 154)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 154)) 0) = 43254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a154_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 154))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 154) 305530) = 194764 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b154_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 154)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 154)) 305530) = 194764 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a154_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 154))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 154) 5604) = 302460 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b154_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 154)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 154)) 5604) = 302460 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a154_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 154))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 154) 221549) = 306086 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b154_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 154)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 154)) 221549) = 306086 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a154_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 154))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 154) 266275) = 204891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b154_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 154)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 154)) 266275) = 204891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a154_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 154))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 154) 186844) = 299261 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b154_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 154)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 154)) 186844) = 299261 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o154 : xone 154 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a154_0 b154_0 a154_1 b154_1 a154_2 b154_2
    a154_3 b154_3 a154_4 b154_4 a154_5 b154_5

theorem a155_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 155))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 155) 0) = 136786 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b155_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 155)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 155)) 0) = 136786 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a155_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 155))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 155) 305530) = 126541 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b155_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 155)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 155)) 305530) = 126541 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a155_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 155))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 155) 5604) = 99443 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b155_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 155)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 155)) 5604) = 99443 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a155_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 155))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 155) 221549) = 273787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b155_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 155)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 155)) 221549) = 273787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a155_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 155))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 155) 266275) = 142657 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b155_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 155)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 155)) 266275) = 142657 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a155_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 155))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 155) 186844) = 19955 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b155_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 155)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 155)) 186844) = 19955 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o155 : xone 155 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a155_0 b155_0 a155_1 b155_1 a155_2 b155_2
    a155_3 b155_3 a155_4 b155_4 a155_5 b155_5

theorem a156_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 156))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 156) 0) = 203721 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b156_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 156)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 156)) 0) = 203721 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a156_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 156))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 156) 305530) = 103343 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b156_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 156)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 156)) 305530) = 103343 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a156_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 156))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 156) 5604) = 265752 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b156_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 156)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 156)) 5604) = 265752 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a156_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 156))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 156) 221549) = 64040 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b156_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 156)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 156)) 221549) = 64040 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a156_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 156))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 156) 266275) = 234473 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b156_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 156)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 156)) 266275) = 234473 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a156_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 156))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 156) 186844) = 78099 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b156_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 156)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 156)) 186844) = 78099 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o156 : xone 156 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a156_0 b156_0 a156_1 b156_1 a156_2 b156_2
    a156_3 b156_3 a156_4 b156_4 a156_5 b156_5

theorem a157_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 157))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 157) 0) = 12104 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b157_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 157)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 157)) 0) = 12104 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a157_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 157))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 157) 305530) = 5409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b157_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 157)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 157)) 305530) = 5409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a157_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 157))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 157) 5604) = 158991 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b157_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 157)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 157)) 5604) = 158991 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a157_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 157))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 157) 221549) = 56058 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b157_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 157)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 157)) 221549) = 56058 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a157_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 157))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 157) 266275) = 13155 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b157_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 157)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 157)) 266275) = 13155 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a157_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 157))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 157) 186844) = 153792 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b157_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 157)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 157)) 186844) = 153792 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o157 : xone 157 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a157_0 b157_0 a157_1 b157_1 a157_2 b157_2
    a157_3 b157_3 a157_4 b157_4 a157_5 b157_5

theorem a158_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 158))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 158) 0) = 15701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b158_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 158)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 158)) 0) = 15701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a158_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 158))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 158) 305530) = 300829 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b158_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 158)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 158)) 305530) = 300829 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a158_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 158))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 158) 5604) = 160775 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b158_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 158)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 158)) 5604) = 160775 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a158_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 158))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 158) 221549) = 224574 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b158_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 158)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 158)) 221549) = 224574 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a158_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 158))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 158) 266275) = 203339 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b158_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 158)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 158)) 266275) = 203339 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a158_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 158))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 158) 186844) = 23978 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b158_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 158)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 158)) 186844) = 23978 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o158 : xone 158 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a158_0 b158_0 a158_1 b158_1 a158_2 b158_2
    a158_3 b158_3 a158_4 b158_4 a158_5 b158_5

theorem a159_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 159))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 159) 0) = 120386 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b159_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 159)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 159)) 0) = 120386 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a159_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 159))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 159) 305530) = 260489 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b159_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 159)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 159)) 305530) = 260489 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a159_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 159))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 159) 5604) = 36724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b159_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 159)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 159)) 5604) = 36724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a159_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 159))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 159) 221549) = 245893 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b159_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 159)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 159)) 221549) = 245893 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a159_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 159))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 159) 266275) = 197056 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b159_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 159)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 159)) 266275) = 197056 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a159_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 159))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 159) 186844) = 91116 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b159_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 159)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 159)) 186844) = 91116 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o159 : xone 159 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a159_0 b159_0 a159_1 b159_1 a159_2 b159_2
    a159_3 b159_3 a159_4 b159_4 a159_5 b159_5

theorem a160_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 160))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 160) 0) = 188717 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b160_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 160)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 160)) 0) = 188717 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a160_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 160))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 160) 305530) = 152510 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b160_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 160)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 160)) 305530) = 152510 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a160_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 160))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 160) 5604) = 222669 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b160_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 160)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 160)) 5604) = 222669 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a160_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 160))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 160) 221549) = 36961 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b160_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 160)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 160)) 221549) = 36961 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a160_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 160))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 160) 266275) = 292865 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b160_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 160)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 160)) 266275) = 292865 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a160_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 160))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 160) 186844) = 210312 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b160_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 160)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 160)) 186844) = 210312 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o160 : xone 160 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a160_0 b160_0 a160_1 b160_1 a160_2 b160_2
    a160_3 b160_3 a160_4 b160_4 a160_5 b160_5

theorem a161_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 161))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 161) 0) = 279540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b161_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 161)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 161)) 0) = 279540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a161_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 161))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 161) 305530) = 15698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b161_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 161)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 161)) 305530) = 15698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a161_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 161))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 161) 5604) = 122847 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b161_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 161)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 161)) 5604) = 122847 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a161_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 161))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 161) 221549) = 86052 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b161_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 161)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 161)) 221549) = 86052 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a161_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 161))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 161) 266275) = 201521 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b161_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 161)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 161)) 266275) = 201521 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a161_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 161))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 161) 186844) = 298269 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b161_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 161)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 161)) 186844) = 298269 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o161 : xone 161 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a161_0 b161_0 a161_1 b161_1 a161_2 b161_2
    a161_3 b161_3 a161_4 b161_4 a161_5 b161_5

theorem a162_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 162))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 162) 0) = 53997 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b162_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 162)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 162)) 0) = 53997 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a162_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 162))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 162) 305530) = 156670 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b162_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 162)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 162)) 305530) = 156670 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a162_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 162))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 162) 5604) = 128917 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b162_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 162)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 162)) 5604) = 128917 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a162_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 162))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 162) 221549) = 184133 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b162_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 162)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 162)) 221549) = 184133 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a162_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 162))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 162) 266275) = 244701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b162_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 162)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 162)) 266275) = 244701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a162_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 162))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 162) 186844) = 30221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b162_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 162)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 162)) 186844) = 30221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o162 : xone 162 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a162_0 b162_0 a162_1 b162_1 a162_2 b162_2
    a162_3 b162_3 a162_4 b162_4 a162_5 b162_5

theorem a163_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 163))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 163) 0) = 81347 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b163_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 163)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 163)) 0) = 81347 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a163_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 163))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 163) 305530) = 246061 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b163_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 163)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 163)) 305530) = 246061 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a163_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 163))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 163) 5604) = 202210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b163_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 163)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 163)) 5604) = 202210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a163_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 163))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 163) 221549) = 143411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b163_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 163)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 163)) 221549) = 143411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a163_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 163))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 163) 266275) = 292391 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b163_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 163)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 163)) 266275) = 292391 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a163_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 163))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 163) 186844) = 1295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b163_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 163)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 163)) 186844) = 1295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o163 : xone 163 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a163_0 b163_0 a163_1 b163_1 a163_2 b163_2
    a163_3 b163_3 a163_4 b163_4 a163_5 b163_5

theorem a164_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 164))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 164) 0) = 41785 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b164_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 164)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 164)) 0) = 41785 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a164_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 164))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 164) 305530) = 70739 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b164_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 164)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 164)) 305530) = 70739 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a164_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 164))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 164) 5604) = 306748 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b164_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 164)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 164)) 5604) = 306748 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a164_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 164))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 164) 221549) = 79006 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b164_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 164)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 164)) 221549) = 79006 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a164_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 164))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 164) 266275) = 38098 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b164_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 164)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 164)) 266275) = 38098 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a164_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 164))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 164) 186844) = 188280 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b164_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 164)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 164)) 186844) = 188280 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o164 : xone 164 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a164_0 b164_0 a164_1 b164_1 a164_2 b164_2
    a164_3 b164_3 a164_4 b164_4 a164_5 b164_5

theorem a165_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 165))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 165) 0) = 149832 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b165_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 165)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 165)) 0) = 149832 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a165_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 165))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 165) 305530) = 153457 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b165_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 165)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 165)) 305530) = 153457 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a165_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 165))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 165) 5604) = 65212 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b165_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 165)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 165)) 5604) = 65212 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a165_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 165))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 165) 221549) = 65631 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b165_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 165)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 165)) 221549) = 65631 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a165_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 165))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 165) 266275) = 241561 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b165_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 165)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 165)) 266275) = 241561 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a165_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 165))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 165) 186844) = 249523 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b165_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 165)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 165)) 186844) = 249523 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o165 : xone 165 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a165_0 b165_0 a165_1 b165_1 a165_2 b165_2
    a165_3 b165_3 a165_4 b165_4 a165_5 b165_5

theorem a166_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 166))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 166) 0) = 163660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b166_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 166)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 166)) 0) = 163660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a166_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 166))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 166) 305530) = 218403 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b166_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 166)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 166)) 305530) = 218403 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a166_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 166))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 166) 5604) = 161690 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b166_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 166)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 166)) 5604) = 161690 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a166_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 166))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 166) 221549) = 139331 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b166_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 166)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 166)) 221549) = 139331 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a166_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 166))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 166) 266275) = 75607 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b166_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 166)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 166)) 266275) = 75607 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a166_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 166))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 166) 186844) = 254256 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b166_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 166)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 166)) 186844) = 254256 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o166 : xone 166 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a166_0 b166_0 a166_1 b166_1 a166_2 b166_2
    a166_3 b166_3 a166_4 b166_4 a166_5 b166_5

theorem a167_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 167))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 167) 0) = 170595 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b167_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 167)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 167)) 0) = 170595 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a167_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 167))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 167) 305530) = 256375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b167_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 167)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 167)) 305530) = 256375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a167_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 167))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 167) 5604) = 137692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b167_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 167)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 167)) 5604) = 137692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a167_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 167))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 167) 221549) = 126219 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b167_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 167)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 167)) 221549) = 126219 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a167_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 167))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 167) 266275) = 143269 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b167_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 167)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 167)) 266275) = 143269 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a167_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 167))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 167) 186844) = 206987 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b167_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 167)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 167)) 186844) = 206987 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o167 : xone 167 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a167_0 b167_0 a167_1 b167_1 a167_2 b167_2
    a167_3 b167_3 a167_4 b167_4 a167_5 b167_5

theorem a168_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 168))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 168) 0) = 101779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b168_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 168)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 168)) 0) = 101779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a168_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 168))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 168) 305530) = 255861 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b168_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 168)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 168)) 305530) = 255861 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a168_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 168))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 168) 5604) = 82143 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b168_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 168)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 168)) 5604) = 82143 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a168_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 168))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 168) 221549) = 31382 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b168_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 168)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 168)) 221549) = 31382 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a168_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 168))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 168) 266275) = 217792 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b168_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 168)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 168)) 266275) = 217792 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a168_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 168))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 168) 186844) = 158420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b168_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 168)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 168)) 186844) = 158420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o168 : xone 168 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a168_0 b168_0 a168_1 b168_1 a168_2 b168_2
    a168_3 b168_3 a168_4 b168_4 a168_5 b168_5

theorem a169_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 169))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 169) 0) = 57395 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b169_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 169)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 169)) 0) = 57395 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a169_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 169))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 169) 305530) = 29563 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b169_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 169)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 169)) 305530) = 29563 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a169_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 169))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 169) 5604) = 186478 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b169_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 169)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 169)) 5604) = 186478 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a169_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 169))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 169) 221549) = 56532 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b169_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 169)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 169)) 221549) = 56532 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a169_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 169))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 169) 266275) = 288129 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b169_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 169)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 169)) 266275) = 288129 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a169_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 169))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 169) 186844) = 13688 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b169_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 169)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 169)) 186844) = 13688 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o169 : xone 169 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a169_0 b169_0 a169_1 b169_1 a169_2 b169_2
    a169_3 b169_3 a169_4 b169_4 a169_5 b169_5

theorem a170_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 170))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 170) 0) = 182317 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b170_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 170)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 170)) 0) = 182317 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a170_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 170))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 170) 305530) = 232160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b170_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 170)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 170)) 305530) = 232160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a170_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 170))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 170) 5604) = 153044 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b170_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 170)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 170)) 5604) = 153044 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a170_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 170))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 170) 221549) = 295561 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b170_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 170)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 170)) 221549) = 295561 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a170_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 170))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 170) 266275) = 96213 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b170_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 170)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 170)) 266275) = 96213 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a170_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 170))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 170) 186844) = 122366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b170_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 170)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 170)) 186844) = 122366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o170 : xone 170 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a170_0 b170_0 a170_1 b170_1 a170_2 b170_2
    a170_3 b170_3 a170_4 b170_4 a170_5 b170_5

theorem a171_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 171))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 171) 0) = 236904 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b171_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 171)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 171)) 0) = 236904 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a171_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 171))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 171) 305530) = 181811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b171_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 171)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 171)) 305530) = 181811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a171_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 171))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 171) 5604) = 140808 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b171_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 171)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 171)) 5604) = 140808 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a171_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 171))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 171) 221549) = 277066 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b171_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 171)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 171)) 221549) = 277066 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a171_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 171))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 171) 266275) = 151937 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b171_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 171)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 171)) 266275) = 151937 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a171_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 171))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 171) 186844) = 190660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b171_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 171)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 171)) 186844) = 190660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o171 : xone 171 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a171_0 b171_0 a171_1 b171_1 a171_2 b171_2
    a171_3 b171_3 a171_4 b171_4 a171_5 b171_5

theorem a172_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 172))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 172) 0) = 305862 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b172_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 172)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 172)) 0) = 305862 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a172_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 172))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 172) 305530) = 97004 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b172_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 172)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 172)) 305530) = 97004 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a172_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 172))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 172) 5604) = 247037 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b172_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 172)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 172)) 5604) = 247037 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a172_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 172))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 172) 221549) = 272604 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b172_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 172)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 172)) 221549) = 272604 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a172_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 172))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 172) 266275) = 141772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b172_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 172)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 172)) 266275) = 141772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a172_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 172))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 172) 186844) = 72093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b172_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 172)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 172)) 186844) = 72093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o172 : xone 172 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a172_0 b172_0 a172_1 b172_1 a172_2 b172_2
    a172_3 b172_3 a172_4 b172_4 a172_5 b172_5

theorem a173_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 173))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 173) 0) = 194548 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b173_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 173)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 173)) 0) = 194548 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a173_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 173))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 173) 305530) = 127468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b173_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 173)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 173)) 305530) = 127468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a173_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 173))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 173) 5604) = 114848 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b173_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 173)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 173)) 5604) = 114848 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a173_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 173))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 173) 221549) = 10445 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b173_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 173)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 173)) 221549) = 10445 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a173_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 173))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 173) 266275) = 256361 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b173_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 173)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 173)) 266275) = 256361 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a173_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 173))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 173) 186844) = 10251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b173_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 173)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 173)) 186844) = 10251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o173 : xone 173 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a173_0 b173_0 a173_1 b173_1 a173_2 b173_2
    a173_3 b173_3 a173_4 b173_4 a173_5 b173_5

theorem a174_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 174))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 174) 0) = 61849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b174_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 174)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 174)) 0) = 61849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a174_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 174))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 174) 305530) = 54554 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b174_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 174)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 174)) 305530) = 54554 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a174_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 174))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 174) 5604) = 214170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b174_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 174)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 174)) 5604) = 214170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a174_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 174))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 174) 221549) = 288420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b174_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 174)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 174)) 221549) = 288420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a174_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 174))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 174) 266275) = 44 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b174_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 174)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 174)) 266275) = 44 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a174_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 174))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 174) 186844) = 50488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b174_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 174)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 174)) 186844) = 50488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o174 : xone 174 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a174_0 b174_0 a174_1 b174_1 a174_2 b174_2
    a174_3 b174_3 a174_4 b174_4 a174_5 b174_5

theorem a175_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 175))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 175) 0) = 250732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b175_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 175)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 175)) 0) = 250732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a175_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 175))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 175) 305530) = 240491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b175_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 175)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 175)) 305530) = 240491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a175_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 175))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 175) 5604) = 273543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b175_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 175)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 175)) 5604) = 273543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a175_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 175))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 175) 221549) = 33515 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b175_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 175)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 175)) 221549) = 33515 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a175_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 175))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 175) 266275) = 29877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b175_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 175)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 175)) 266275) = 29877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a175_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 175))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 175) 186844) = 22496 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b175_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 175)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 175)) 186844) = 22496 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o175 : xone 175 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a175_0 b175_0 a175_1 b175_1 a175_2 b175_2
    a175_3 b175_3 a175_4 b175_4 a175_5 b175_5

theorem a176_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 176))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 176) 0) = 275066 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b176_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 176)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 176)) 0) = 275066 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a176_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 176))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 176) 305530) = 78844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b176_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 176)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 176)) 305530) = 78844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a176_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 176))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 176) 5604) = 4269 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b176_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 176)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 176)) 5604) = 4269 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a176_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 176))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 176) 221549) = 171901 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b176_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 176)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 176)) 221549) = 171901 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a176_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 176))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 176) 266275) = 173364 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b176_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 176)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 176)) 266275) = 173364 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a176_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 176))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 176) 186844) = 100056 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b176_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 176)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 176)) 186844) = 100056 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o176 : xone 176 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a176_0 b176_0 a176_1 b176_1 a176_2 b176_2
    a176_3 b176_3 a176_4 b176_4 a176_5 b176_5

theorem a177_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 177))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 177) 0) = 227519 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b177_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 177)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 177)) 0) = 227519 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a177_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 177))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 177) 305530) = 76153 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b177_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 177)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 177)) 305530) = 76153 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a177_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 177))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 177) 5604) = 155341 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b177_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 177)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 177)) 5604) = 155341 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a177_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 177))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 177) 221549) = 165164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b177_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 177)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 177)) 221549) = 165164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a177_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 177))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 177) 266275) = 290009 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b177_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 177)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 177)) 266275) = 290009 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a177_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 177))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 177) 186844) = 6863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b177_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 177)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 177)) 186844) = 6863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o177 : xone 177 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a177_0 b177_0 a177_1 b177_1 a177_2 b177_2
    a177_3 b177_3 a177_4 b177_4 a177_5 b177_5

theorem a178_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 178))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 178) 0) = 205989 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b178_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 178)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 178)) 0) = 205989 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a178_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 178))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 178) 305530) = 302828 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b178_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 178)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 178)) 305530) = 302828 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a178_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 178))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 178) 5604) = 251888 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b178_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 178)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 178)) 5604) = 251888 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a178_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 178))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 178) 221549) = 79943 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b178_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 178)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 178)) 221549) = 79943 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a178_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 178))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 178) 266275) = 78467 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b178_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 178)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 178)) 266275) = 78467 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a178_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 178))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 178) 186844) = 272674 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b178_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 178)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 178)) 186844) = 272674 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o178 : xone 178 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a178_0 b178_0 a178_1 b178_1 a178_2 b178_2
    a178_3 b178_3 a178_4 b178_4 a178_5 b178_5

theorem a179_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 179))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 179) 0) = 132992 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b179_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 179)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 179)) 0) = 132992 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a179_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 179))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 179) 305530) = 165383 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b179_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 179)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 179)) 305530) = 165383 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a179_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 179))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 179) 5604) = 193623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b179_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 179)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 179)) 5604) = 193623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a179_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 179))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 179) 221549) = 680 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b179_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 179)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 179)) 221549) = 680 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a179_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 179))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 179) 266275) = 88993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b179_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 179)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 179)) 266275) = 88993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a179_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 179))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 179) 186844) = 115566 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b179_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 179)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 179)) 186844) = 115566 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o179 : xone 179 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a179_0 b179_0 a179_1 b179_1 a179_2 b179_2
    a179_3 b179_3 a179_4 b179_4 a179_5 b179_5

theorem a180_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 180))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 180) 0) = 237789 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b180_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 180)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 180)) 0) = 237789 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a180_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 180))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 180) 305530) = 300457 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b180_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 180)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 180)) 305530) = 300457 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a180_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 180))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 180) 5604) = 250411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b180_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 180)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 180)) 5604) = 250411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a180_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 180))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 180) 221549) = 89916 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b180_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 180)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 180)) 221549) = 89916 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a180_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 180))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 180) 266275) = 51913 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b180_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 180)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 180)) 266275) = 51913 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a180_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 180))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 180) 186844) = 104132 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b180_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 180)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 180)) 186844) = 104132 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o180 : xone 180 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a180_0 b180_0 a180_1 b180_1 a180_2 b180_2
    a180_3 b180_3 a180_4 b180_4 a180_5 b180_5

theorem a181_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 181))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 181) 0) = 138920 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b181_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 181)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 181)) 0) = 138920 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a181_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 181))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 181) 305530) = 217814 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b181_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 181)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 181)) 305530) = 217814 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a181_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 181))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 181) 5604) = 212800 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b181_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 181)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 181)) 5604) = 212800 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a181_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 181))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 181) 221549) = 72909 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b181_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 181)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 181)) 221549) = 72909 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a181_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 181))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 181) 266275) = 9622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b181_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 181)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 181)) 266275) = 9622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a181_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 181))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 181) 186844) = 300584 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b181_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 181)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 181)) 186844) = 300584 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o181 : xone 181 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a181_0 b181_0 a181_1 b181_1 a181_2 b181_2
    a181_3 b181_3 a181_4 b181_4 a181_5 b181_5

theorem a182_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 182))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 182) 0) = 85219 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b182_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 182)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 182)) 0) = 85219 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a182_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 182))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 182) 305530) = 72318 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b182_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 182)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 182)) 305530) = 72318 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a182_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 182))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 182) 5604) = 198363 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b182_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 182)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 182)) 5604) = 198363 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a182_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 182))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 182) 221549) = 40536 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b182_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 182)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 182)) 221549) = 40536 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a182_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 182))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 182) 266275) = 28605 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b182_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 182)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 182)) 266275) = 28605 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a182_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 182))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 182) 186844) = 51884 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b182_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 182)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 182)) 186844) = 51884 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o182 : xone 182 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a182_0 b182_0 a182_1 b182_1 a182_2 b182_2
    a182_3 b182_3 a182_4 b182_4 a182_5 b182_5

theorem a183_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 183))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 183) 0) = 11076 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b183_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 183)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 183)) 0) = 11076 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a183_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 183))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 183) 305530) = 151911 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b183_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 183)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 183)) 305530) = 151911 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a183_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 183))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 183) 5604) = 215680 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b183_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 183)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 183)) 5604) = 215680 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a183_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 183))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 183) 221549) = 245291 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b183_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 183)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 183)) 221549) = 245291 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a183_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 183))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 183) 266275) = 56205 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b183_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 183)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 183)) 266275) = 56205 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a183_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 183))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 183) 186844) = 153993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b183_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 183)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 183)) 186844) = 153993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o183 : xone 183 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a183_0 b183_0 a183_1 b183_1 a183_2 b183_2
    a183_3 b183_3 a183_4 b183_4 a183_5 b183_5

theorem a184_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 184))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 184) 0) = 234203 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b184_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 184)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 184)) 0) = 234203 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a184_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 184))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 184) 305530) = 293815 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b184_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 184)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 184)) 305530) = 293815 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a184_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 184))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 184) 5604) = 224737 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b184_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 184)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 184)) 5604) = 224737 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a184_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 184))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 184) 221549) = 292949 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b184_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 184)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 184)) 221549) = 292949 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a184_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 184))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 184) 266275) = 259543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b184_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 184)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 184)) 266275) = 259543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a184_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 184))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 184) 186844) = 197695 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b184_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 184)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 184)) 186844) = 197695 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o184 : xone 184 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a184_0 b184_0 a184_1 b184_1 a184_2 b184_2
    a184_3 b184_3 a184_4 b184_4 a184_5 b184_5

theorem a185_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 185))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 185) 0) = 265687 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b185_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 185)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 185)) 0) = 265687 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a185_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 185))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 185) 305530) = 171200 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b185_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 185)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 185)) 305530) = 171200 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a185_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 185))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 185) 5604) = 136555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b185_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 185)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 185)) 5604) = 136555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a185_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 185))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 185) 221549) = 295290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b185_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 185)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 185)) 221549) = 295290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a185_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 185))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 185) 266275) = 173572 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b185_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 185)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 185)) 266275) = 173572 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a185_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 185))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 185) 186844) = 113768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b185_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 185)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 185)) 186844) = 113768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o185 : xone 185 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a185_0 b185_0 a185_1 b185_1 a185_2 b185_2
    a185_3 b185_3 a185_4 b185_4 a185_5 b185_5

theorem a186_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 186))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 186) 0) = 135383 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b186_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 186)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 186)) 0) = 135383 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a186_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 186))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 186) 305530) = 169868 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b186_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 186)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 186)) 305530) = 169868 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a186_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 186))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 186) 5604) = 215857 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b186_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 186)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 186)) 5604) = 215857 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a186_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 186))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 186) 221549) = 228978 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b186_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 186)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 186)) 221549) = 228978 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a186_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 186))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 186) 266275) = 99995 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b186_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 186)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 186)) 266275) = 99995 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a186_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 186))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 186) 186844) = 37904 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b186_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 186)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 186)) 186844) = 37904 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o186 : xone 186 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a186_0 b186_0 a186_1 b186_1 a186_2 b186_2
    a186_3 b186_3 a186_4 b186_4 a186_5 b186_5

theorem a187_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 187))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 187) 0) = 191259 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b187_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 187)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 187)) 0) = 191259 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a187_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 187))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 187) 305530) = 114732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b187_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 187)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 187)) 305530) = 114732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a187_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 187))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 187) 5604) = 32295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b187_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 187)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 187)) 5604) = 32295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a187_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 187))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 187) 221549) = 57808 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b187_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 187)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 187)) 221549) = 57808 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a187_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 187))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 187) 266275) = 140290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b187_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 187)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 187)) 266275) = 140290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a187_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 187))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 187) 186844) = 281469 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b187_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 187)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 187)) 186844) = 281469 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o187 : xone 187 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a187_0 b187_0 a187_1 b187_1 a187_2 b187_2
    a187_3 b187_3 a187_4 b187_4 a187_5 b187_5

theorem a188_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 188))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 188) 0) = 174954 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b188_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 188)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 188)) 0) = 174954 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a188_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 188))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 188) 305530) = 298787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b188_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 188)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 188)) 305530) = 298787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a188_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 188))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 188) 5604) = 140095 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b188_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 188)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 188)) 5604) = 140095 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a188_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 188))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 188) 221549) = 234602 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b188_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 188)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 188)) 221549) = 234602 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a188_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 188))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 188) 266275) = 61451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b188_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 188)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 188)) 266275) = 61451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a188_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 188))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 188) 186844) = 186361 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b188_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 188)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 188)) 186844) = 186361 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o188 : xone 188 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a188_0 b188_0 a188_1 b188_1 a188_2 b188_2
    a188_3 b188_3 a188_4 b188_4 a188_5 b188_5

theorem a189_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 189))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 189) 0) = 218831 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b189_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 189)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 189)) 0) = 218831 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a189_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 189))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 189) 305530) = 104083 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b189_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 189)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 189)) 305530) = 104083 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a189_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 189))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 189) 5604) = 161281 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b189_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 189)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 189)) 5604) = 161281 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a189_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 189))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 189) 221549) = 71811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b189_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 189)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 189)) 221549) = 71811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a189_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 189))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 189) 266275) = 48966 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b189_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 189)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 189)) 266275) = 48966 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a189_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 189))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 189) 186844) = 215586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b189_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 189)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 189)) 186844) = 215586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o189 : xone 189 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a189_0 b189_0 a189_1 b189_1 a189_2 b189_2
    a189_3 b189_3 a189_4 b189_4 a189_5 b189_5

theorem a190_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 190))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 190) 0) = 224356 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b190_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 190)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 190)) 0) = 224356 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a190_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 190))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 190) 305530) = 251497 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b190_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 190)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 190)) 305530) = 251497 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a190_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 190))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 190) 5604) = 190981 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b190_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 190)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 190)) 5604) = 190981 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a190_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 190))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 190) 221549) = 304904 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b190_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 190)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 190)) 221549) = 304904 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a190_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 190))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 190) 266275) = 118750 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b190_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 190)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 190)) 266275) = 118750 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a190_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 190))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 190) 186844) = 80424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b190_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 190)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 190)) 186844) = 80424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o190 : xone 190 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a190_0 b190_0 a190_1 b190_1 a190_2 b190_2
    a190_3 b190_3 a190_4 b190_4 a190_5 b190_5

theorem a191_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 191))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 191) 0) = 246704 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b191_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 191)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 191)) 0) = 246704 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a191_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 191))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 191) 305530) = 57919 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b191_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 191)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 191)) 305530) = 57919 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a191_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 191))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 191) 5604) = 69372 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b191_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 191)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 191)) 5604) = 69372 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a191_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 191))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 191) 221549) = 253604 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b191_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 191)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 191)) 221549) = 253604 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a191_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 191))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 191) 266275) = 149661 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b191_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 191)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 191)) 266275) = 149661 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a191_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 191))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 191) 186844) = 53398 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b191_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 191)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 191)) 186844) = 53398 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o191 : xone 191 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a191_0 b191_0 a191_1 b191_1 a191_2 b191_2
    a191_3 b191_3 a191_4 b191_4 a191_5 b191_5

theorem a192_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 192))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 192) 0) = 214970 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b192_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 192)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 192)) 0) = 214970 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a192_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 192))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 192) 305530) = 14709 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b192_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 192)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 192)) 305530) = 14709 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a192_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 192))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 192) 5604) = 280115 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b192_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 192)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 192)) 5604) = 280115 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a192_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 192))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 192) 221549) = 16175 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b192_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 192)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 192)) 221549) = 16175 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a192_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 192))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 192) 266275) = 298358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b192_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 192)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 192)) 266275) = 298358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a192_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 192))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 192) 186844) = 82282 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b192_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 192)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 192)) 186844) = 82282 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o192 : xone 192 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a192_0 b192_0 a192_1 b192_1 a192_2 b192_2
    a192_3 b192_3 a192_4 b192_4 a192_5 b192_5

theorem a193_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 193))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 193) 0) = 272062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b193_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 193)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 193)) 0) = 272062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a193_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 193))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 193) 305530) = 245336 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b193_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 193)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 193)) 305530) = 245336 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a193_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 193))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 193) 5604) = 205407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b193_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 193)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 193)) 5604) = 205407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a193_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 193))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 193) 221549) = 275603 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b193_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 193)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 193)) 221549) = 275603 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a193_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 193))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 193) 266275) = 102919 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b193_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 193)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 193)) 266275) = 102919 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a193_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 193))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 193) 186844) = 45213 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b193_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 193)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 193)) 186844) = 45213 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o193 : xone 193 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a193_0 b193_0 a193_1 b193_1 a193_2 b193_2
    a193_3 b193_3 a193_4 b193_4 a193_5 b193_5

theorem a194_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 194))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 194) 0) = 254785 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b194_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 194)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 194)) 0) = 254785 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a194_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 194))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 194) 305530) = 184082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b194_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 194)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 194)) 305530) = 184082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a194_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 194))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 194) 5604) = 95077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b194_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 194)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 194)) 5604) = 95077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a194_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 194))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 194) 221549) = 284148 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b194_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 194)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 194)) 221549) = 284148 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a194_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 194))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 194) 266275) = 193262 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b194_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 194)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 194)) 266275) = 193262 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a194_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 194))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 194) 186844) = 133170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b194_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 194)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 194)) 186844) = 133170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o194 : xone 194 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a194_0 b194_0 a194_1 b194_1 a194_2 b194_2
    a194_3 b194_3 a194_4 b194_4 a194_5 b194_5

theorem a195_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 195))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 195) 0) = 61877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b195_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 195)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 195)) 0) = 61877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a195_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 195))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 195) 305530) = 189031 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b195_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 195)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 195)) 305530) = 189031 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a195_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 195))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 195) 5604) = 262249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b195_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 195)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 195)) 5604) = 262249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a195_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 195))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 195) 221549) = 91716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b195_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 195)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 195)) 221549) = 91716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a195_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 195))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 195) 266275) = 80832 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b195_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 195)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 195)) 266275) = 80832 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a195_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 195))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 195) 186844) = 173600 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b195_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 195)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 195)) 186844) = 173600 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o195 : xone 195 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a195_0 b195_0 a195_1 b195_1 a195_2 b195_2
    a195_3 b195_3 a195_4 b195_4 a195_5 b195_5

theorem a196_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 196))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 196) 0) = 153193 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b196_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 196)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 196)) 0) = 153193 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a196_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 196))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 196) 305530) = 183188 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b196_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 196)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 196)) 305530) = 183188 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a196_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 196))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 196) 5604) = 297459 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b196_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 196)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 196)) 5604) = 297459 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a196_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 196))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 196) 221549) = 278249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b196_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 196)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 196)) 221549) = 278249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a196_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 196))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 196) 266275) = 305480 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b196_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 196)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 196)) 266275) = 305480 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a196_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 196))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 196) 186844) = 154336 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b196_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 196)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 196)) 186844) = 154336 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o196 : xone 196 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a196_0 b196_0 a196_1 b196_1 a196_2 b196_2
    a196_3 b196_3 a196_4 b196_4 a196_5 b196_5

theorem a197_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 197))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 197) 0) = 215883 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b197_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 197)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 197)) 0) = 215883 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a197_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 197))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 197) 305530) = 128503 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b197_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 197)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 197)) 305530) = 128503 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a197_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 197))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 197) 5604) = 28908 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b197_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 197)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 197)) 5604) = 28908 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a197_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 197))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 197) 221549) = 192301 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b197_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 197)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 197)) 221549) = 192301 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a197_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 197))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 197) 266275) = 219867 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b197_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 197)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 197)) 266275) = 219867 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a197_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 197))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 197) 186844) = 226167 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b197_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 197)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 197)) 186844) = 226167 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o197 : xone 197 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a197_0 b197_0 a197_1 b197_1 a197_2 b197_2
    a197_3 b197_3 a197_4 b197_4 a197_5 b197_5

theorem a198_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 198))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 198) 0) = 213850 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b198_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 198)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 198)) 0) = 213850 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a198_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 198))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 198) 305530) = 275320 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b198_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 198)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 198)) 305530) = 275320 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a198_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 198))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 198) 5604) = 67167 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b198_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 198)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 198)) 5604) = 67167 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a198_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 198))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 198) 221549) = 12555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b198_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 198)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 198)) 221549) = 12555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a198_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 198))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 198) 266275) = 142491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b198_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 198)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 198)) 266275) = 142491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a198_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 198))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 198) 186844) = 236989 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b198_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 198)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 198)) 186844) = 236989 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o198 : xone 198 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a198_0 b198_0 a198_1 b198_1 a198_2 b198_2
    a198_3 b198_3 a198_4 b198_4 a198_5 b198_5

theorem a199_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 199))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 199) 0) = 24999 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b199_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 199)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 199)) 0) = 24999 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a199_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 199))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 199) 305530) = 174064 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b199_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 199)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 199)) 305530) = 174064 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a199_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 199))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 199) 5604) = 237845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b199_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 199)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 199)) 5604) = 237845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a199_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 199))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 199) 221549) = 107017 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b199_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 199)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 199)) 221549) = 107017 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a199_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 199))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 199) 266275) = 105278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b199_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 199)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 199)) 266275) = 105278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a199_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 199))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 199) 186844) = 75211 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b199_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 199)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 199)) 186844) = 75211 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o199 : xone 199 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a199_0 b199_0 a199_1 b199_1 a199_2 b199_2
    a199_3 b199_3 a199_4 b199_4 a199_5 b199_5

theorem a200_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 200))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 200) 0) = 72367 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b200_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 200)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 200)) 0) = 72367 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a200_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 200))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 200) 305530) = 166028 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b200_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 200)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 200)) 305530) = 166028 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a200_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 200))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 200) 5604) = 185200 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b200_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 200)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 200)) 5604) = 185200 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a200_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 200))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 200) 221549) = 35109 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b200_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 200)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 200)) 221549) = 35109 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a200_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 200))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 200) 266275) = 38616 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b200_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 200)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 200)) 266275) = 38616 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a200_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 200))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 200) 186844) = 198483 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b200_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 200)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 200)) 186844) = 198483 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o200 : xone 200 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a200_0 b200_0 a200_1 b200_1 a200_2 b200_2
    a200_3 b200_3 a200_4 b200_4 a200_5 b200_5

theorem a201_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 201))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 201) 0) = 179614 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b201_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 201)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 201)) 0) = 179614 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a201_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 201))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 201) 305530) = 112670 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b201_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 201)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 201)) 305530) = 112670 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a201_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 201))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 201) 5604) = 18614 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b201_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 201)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 201)) 5604) = 18614 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a201_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 201))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 201) 221549) = 197533 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b201_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 201)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 201)) 221549) = 197533 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a201_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 201))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 201) 266275) = 247684 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b201_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 201)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 201)) 266275) = 247684 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a201_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 201))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 201) 186844) = 76961 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b201_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 201)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 201)) 186844) = 76961 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o201 : xone 201 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a201_0 b201_0 a201_1 b201_1 a201_2 b201_2
    a201_3 b201_3 a201_4 b201_4 a201_5 b201_5

theorem a202_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 202))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 202) 0) = 206372 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b202_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 202)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 202)) 0) = 206372 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a202_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 202))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 202) 305530) = 189088 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b202_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 202)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 202)) 305530) = 189088 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a202_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 202))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 202) 5604) = 206060 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b202_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 202)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 202)) 5604) = 206060 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a202_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 202))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 202) 221549) = 138945 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b202_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 202)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 202)) 221549) = 138945 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a202_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 202))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 202) 266275) = 116329 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b202_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 202)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 202)) 266275) = 116329 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a202_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 202))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 202) 186844) = 255228 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b202_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 202)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 202)) 186844) = 255228 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o202 : xone 202 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a202_0 b202_0 a202_1 b202_1 a202_2 b202_2
    a202_3 b202_3 a202_4 b202_4 a202_5 b202_5

theorem a203_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 203))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 203) 0) = 167612 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b203_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 203)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 203)) 0) = 167612 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a203_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 203))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 203) 305530) = 195193 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b203_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 203)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 203)) 305530) = 195193 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a203_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 203))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 203) 5604) = 141989 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b203_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 203)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 203)) 5604) = 141989 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a203_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 203))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 203) 221549) = 214687 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b203_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 203)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 203)) 221549) = 214687 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a203_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 203))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 203) 266275) = 292202 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b203_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 203)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 203)) 266275) = 292202 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a203_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 203))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 203) 186844) = 172830 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b203_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 203)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 203)) 186844) = 172830 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o203 : xone 203 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a203_0 b203_0 a203_1 b203_1 a203_2 b203_2
    a203_3 b203_3 a203_4 b203_4 a203_5 b203_5

theorem a204_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 204))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 204) 0) = 110221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b204_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 204)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 204)) 0) = 110221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a204_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 204))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 204) 305530) = 238975 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b204_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 204)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 204)) 305530) = 238975 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a204_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 204))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 204) 5604) = 131408 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b204_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 204)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 204)) 5604) = 131408 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a204_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 204))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 204) 221549) = 100523 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b204_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 204)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 204)) 221549) = 100523 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a204_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 204))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 204) 266275) = 139552 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b204_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 204)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 204)) 266275) = 139552 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a204_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 204))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 204) 186844) = 37311 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b204_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 204)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 204)) 186844) = 37311 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o204 : xone 204 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a204_0 b204_0 a204_1 b204_1 a204_2 b204_2
    a204_3 b204_3 a204_4 b204_4 a204_5 b204_5

theorem a205_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 205))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 205) 0) = 117014 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b205_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 205)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 205)) 0) = 117014 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a205_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 205))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 205) 305530) = 49773 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b205_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 205)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 205)) 305530) = 49773 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a205_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 205))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 205) 5604) = 303448 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b205_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 205)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 205)) 5604) = 303448 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a205_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 205))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 205) 221549) = 39463 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b205_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 205)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 205)) 221549) = 39463 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a205_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 205))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 205) 266275) = 245775 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b205_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 205)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 205)) 266275) = 245775 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a205_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 205))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 205) 186844) = 209197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b205_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 205)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 205)) 186844) = 209197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o205 : xone 205 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a205_0 b205_0 a205_1 b205_1 a205_2 b205_2
    a205_3 b205_3 a205_4 b205_4 a205_5 b205_5

theorem a206_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 206))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 206) 0) = 215199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b206_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 206)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 206)) 0) = 215199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a206_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 206))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 206) 305530) = 233392 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b206_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 206)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 206)) 305530) = 233392 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a206_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 206))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 206) 5604) = 11611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b206_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 206)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 206)) 5604) = 11611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a206_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 206))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 206) 221549) = 276512 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b206_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 206)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 206)) 221549) = 276512 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a206_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 206))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 206) 266275) = 115185 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b206_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 206)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 206)) 266275) = 115185 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a206_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 206))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 206) 186844) = 281553 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b206_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 206)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 206)) 186844) = 281553 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o206 : xone 206 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a206_0 b206_0 a206_1 b206_1 a206_2 b206_2
    a206_3 b206_3 a206_4 b206_4 a206_5 b206_5

theorem a207_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 207))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 207) 0) = 176842 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b207_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 207)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 207)) 0) = 176842 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a207_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 207))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 207) 305530) = 172395 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b207_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 207)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 207)) 305530) = 172395 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a207_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 207))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 207) 5604) = 217733 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b207_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 207)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 207)) 5604) = 217733 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a207_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 207))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 207) 221549) = 70876 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b207_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 207)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 207)) 221549) = 70876 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a207_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 207))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 207) 266275) = 93494 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b207_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 207)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 207)) 266275) = 93494 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a207_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 207))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 207) 186844) = 147357 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b207_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 207)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 207)) 186844) = 147357 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o207 : xone 207 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a207_0 b207_0 a207_1 b207_1 a207_2 b207_2
    a207_3 b207_3 a207_4 b207_4 a207_5 b207_5

end CFSG.KD.Fi24Pc.Ck

public section

namespace CFSG.KD.Fi24Pc.Ck

theorem x0 : CFSG.KD.Fi24Pc.xck (nat_lit 0) = true :=
  xck_of o0 (by quickRfl) o1 (by quickRfl) o2 (by quickRfl) o3 (by quickRfl)
    o4 (by quickRfl) o5 (by quickRfl) o6 (by quickRfl) o7 (by quickRfl)

theorem x1 : CFSG.KD.Fi24Pc.xck (nat_lit 1) = true :=
  xck_of o8 (by quickRfl) o9 (by quickRfl) o10 (by quickRfl) o11 (by quickRfl)
    o12 (by quickRfl) o13 (by quickRfl) o14 (by quickRfl) o15 (by quickRfl)

theorem x2 : CFSG.KD.Fi24Pc.xck (nat_lit 2) = true :=
  xck_of o16 (by quickRfl) o17 (by quickRfl) o18 (by quickRfl) o19 (by quickRfl)
    o20 (by quickRfl) o21 (by quickRfl) o22 (by quickRfl) o23 (by quickRfl)

theorem x3 : CFSG.KD.Fi24Pc.xck (nat_lit 3) = true :=
  xck_of o24 (by quickRfl) o25 (by quickRfl) o26 (by quickRfl) o27 (by quickRfl)
    o28 (by quickRfl) o29 (by quickRfl) o30 (by quickRfl) o31 (by quickRfl)

theorem x4 : CFSG.KD.Fi24Pc.xck (nat_lit 4) = true :=
  xck_of o32 (by quickRfl) o33 (by quickRfl) o34 (by quickRfl) o35 (by quickRfl)
    o36 (by quickRfl) o37 (by quickRfl) o38 (by quickRfl) o39 (by quickRfl)

theorem x5 : CFSG.KD.Fi24Pc.xck (nat_lit 5) = true :=
  xck_of o40 (by quickRfl) o41 (by quickRfl) o42 (by quickRfl) o43 (by quickRfl)
    o44 (by quickRfl) o45 (by quickRfl) o46 (by quickRfl) o47 (by quickRfl)

theorem x6 : CFSG.KD.Fi24Pc.xck (nat_lit 6) = true :=
  xck_of o48 (by quickRfl) o49 (by quickRfl) o50 (by quickRfl) o51 (by quickRfl)
    o52 (by quickRfl) o53 (by quickRfl) o54 (by quickRfl) o55 (by quickRfl)

theorem x7 : CFSG.KD.Fi24Pc.xck (nat_lit 7) = true :=
  xck_of o56 (by quickRfl) o57 (by quickRfl) o58 (by quickRfl) o59 (by quickRfl)
    o60 (by quickRfl) o61 (by quickRfl) o62 (by quickRfl) o63 (by quickRfl)

theorem x8 : CFSG.KD.Fi24Pc.xck (nat_lit 8) = true :=
  xck_of o64 (by quickRfl) o65 (by quickRfl) o66 (by quickRfl) o67 (by quickRfl)
    o68 (by quickRfl) o69 (by quickRfl) o70 (by quickRfl) o71 (by quickRfl)

theorem x9 : CFSG.KD.Fi24Pc.xck (nat_lit 9) = true :=
  xck_of o72 (by quickRfl) o73 (by quickRfl) o74 (by quickRfl) o75 (by quickRfl)
    o76 (by quickRfl) o77 (by quickRfl) o78 (by quickRfl) o79 (by quickRfl)

theorem x10 : CFSG.KD.Fi24Pc.xck (nat_lit 10) = true :=
  xck_of o80 (by quickRfl) o81 (by quickRfl) o82 (by quickRfl) o83 (by quickRfl)
    o84 (by quickRfl) o85 (by quickRfl) o86 (by quickRfl) o87 (by quickRfl)

theorem x11 : CFSG.KD.Fi24Pc.xck (nat_lit 11) = true :=
  xck_of o88 (by quickRfl) o89 (by quickRfl) o90 (by quickRfl) o91 (by quickRfl)
    o92 (by quickRfl) o93 (by quickRfl) o94 (by quickRfl) o95 (by quickRfl)

theorem x12 : CFSG.KD.Fi24Pc.xck (nat_lit 12) = true :=
  xck_of o96 (by quickRfl) o97 (by quickRfl) o98 (by quickRfl) o99 (by quickRfl)
    o100 (by quickRfl) o101 (by quickRfl) o102 (by quickRfl) o103 (by quickRfl)

theorem x13 : CFSG.KD.Fi24Pc.xck (nat_lit 13) = true :=
  xck_of o104 (by quickRfl) o105 (by quickRfl) o106 (by quickRfl) o107 (by quickRfl)
    o108 (by quickRfl) o109 (by quickRfl) o110 (by quickRfl) o111 (by quickRfl)

theorem x14 : CFSG.KD.Fi24Pc.xck (nat_lit 14) = true :=
  xck_of o112 (by quickRfl) o113 (by quickRfl) o114 (by quickRfl) o115 (by quickRfl)
    o116 (by quickRfl) o117 (by quickRfl) o118 (by quickRfl) o119 (by quickRfl)

theorem x15 : CFSG.KD.Fi24Pc.xck (nat_lit 15) = true :=
  xck_of o120 (by quickRfl) o121 (by quickRfl) o122 (by quickRfl) o123 (by quickRfl)
    o124 (by quickRfl) o125 (by quickRfl) o126 (by quickRfl) o127 (by quickRfl)

theorem x16 : CFSG.KD.Fi24Pc.xck (nat_lit 16) = true :=
  xck_of o128 (by quickRfl) o129 (by quickRfl) o130 (by quickRfl) o131 (by quickRfl)
    o132 (by quickRfl) o133 (by quickRfl) o134 (by quickRfl) o135 (by quickRfl)

theorem x17 : CFSG.KD.Fi24Pc.xck (nat_lit 17) = true :=
  xck_of o136 (by quickRfl) o137 (by quickRfl) o138 (by quickRfl) o139 (by quickRfl)
    o140 (by quickRfl) o141 (by quickRfl) o142 (by quickRfl) o143 (by quickRfl)

theorem x18 : CFSG.KD.Fi24Pc.xck (nat_lit 18) = true :=
  xck_of o144 (by quickRfl) o145 (by quickRfl) o146 (by quickRfl) o147 (by quickRfl)
    o148 (by quickRfl) o149 (by quickRfl) o150 (by quickRfl) o151 (by quickRfl)

theorem x19 : CFSG.KD.Fi24Pc.xck (nat_lit 19) = true :=
  xck_of o152 (by quickRfl) o153 (by quickRfl) o154 (by quickRfl) o155 (by quickRfl)
    o156 (by quickRfl) o157 (by quickRfl) o158 (by quickRfl) o159 (by quickRfl)

theorem x20 : CFSG.KD.Fi24Pc.xck (nat_lit 20) = true :=
  xck_of o160 (by quickRfl) o161 (by quickRfl) o162 (by quickRfl) o163 (by quickRfl)
    o164 (by quickRfl) o165 (by quickRfl) o166 (by quickRfl) o167 (by quickRfl)

theorem x21 : CFSG.KD.Fi24Pc.xck (nat_lit 21) = true :=
  xck_of o168 (by quickRfl) o169 (by quickRfl) o170 (by quickRfl) o171 (by quickRfl)
    o172 (by quickRfl) o173 (by quickRfl) o174 (by quickRfl) o175 (by quickRfl)

theorem x22 : CFSG.KD.Fi24Pc.xck (nat_lit 22) = true :=
  xck_of o176 (by quickRfl) o177 (by quickRfl) o178 (by quickRfl) o179 (by quickRfl)
    o180 (by quickRfl) o181 (by quickRfl) o182 (by quickRfl) o183 (by quickRfl)

theorem x23 : CFSG.KD.Fi24Pc.xck (nat_lit 23) = true :=
  xck_of o184 (by quickRfl) o185 (by quickRfl) o186 (by quickRfl) o187 (by quickRfl)
    o188 (by quickRfl) o189 (by quickRfl) o190 (by quickRfl) o191 (by quickRfl)

theorem x24 : CFSG.KD.Fi24Pc.xck (nat_lit 24) = true :=
  xck_of o192 (by quickRfl) o193 (by quickRfl) o194 (by quickRfl) o195 (by quickRfl)
    o196 (by quickRfl) o197 (by quickRfl) o198 (by quickRfl) o199 (by quickRfl)

theorem x25 : CFSG.KD.Fi24Pc.xck (nat_lit 25) = true :=
  xck_of o200 (by quickRfl) o201 (by quickRfl) o202 (by quickRfl) o203 (by quickRfl)
    o204 (by quickRfl) o205 (by quickRfl) o206 (by quickRfl) o207 (by quickRfl)

end CFSG.KD.Fi24Pc.Ck

end
