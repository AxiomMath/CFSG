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

theorem a208_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 208))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 208) 0) = 132610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b208_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 208)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 208)) 0) = 132610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a208_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 208))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 208) 305530) = 105312 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b208_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 208)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 208)) 305530) = 105312 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a208_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 208))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 208) 5604) = 243404 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b208_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 208)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 208)) 5604) = 243404 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a208_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 208))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 208) 221549) = 22578 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b208_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 208)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 208)) 221549) = 22578 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a208_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 208))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 208) 266275) = 220821 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b208_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 208)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 208)) 266275) = 220821 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a208_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 208))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 208) 186844) = 260747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b208_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 208)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 208)) 186844) = 260747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o208 : xone 208 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a208_0 b208_0 a208_1 b208_1 a208_2 b208_2
    a208_3 b208_3 a208_4 b208_4 a208_5 b208_5

theorem a209_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 209))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 209) 0) = 89083 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b209_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 209)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 209)) 0) = 89083 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a209_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 209))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 209) 305530) = 275389 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b209_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 209)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 209)) 305530) = 275389 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a209_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 209))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 209) 5604) = 187964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b209_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 209)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 209)) 5604) = 187964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a209_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 209))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 209) 221549) = 289279 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b209_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 209)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 209)) 221549) = 289279 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a209_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 209))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 209) 266275) = 175446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b209_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 209)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 209)) 266275) = 175446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a209_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 209))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 209) 186844) = 119286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b209_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 209)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 209)) 186844) = 119286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o209 : xone 209 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a209_0 b209_0 a209_1 b209_1 a209_2 b209_2
    a209_3 b209_3 a209_4 b209_4 a209_5 b209_5

theorem a210_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 210))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 210) 0) = 158407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b210_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 210)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 210)) 0) = 158407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a210_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 210))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 210) 305530) = 58468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b210_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 210)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 210)) 305530) = 58468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a210_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 210))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 210) 5604) = 197549 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b210_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 210)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 210)) 5604) = 197549 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a210_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 210))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 210) 221549) = 145126 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b210_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 210)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 210)) 221549) = 145126 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a210_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 210))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 210) 266275) = 135128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b210_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 210)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 210)) 266275) = 135128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a210_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 210))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 210) 186844) = 212180 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b210_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 210)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 210)) 186844) = 212180 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o210 : xone 210 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a210_0 b210_0 a210_1 b210_1 a210_2 b210_2
    a210_3 b210_3 a210_4 b210_4 a210_5 b210_5

theorem a211_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 211))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 211) 0) = 170879 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b211_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 211)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 211)) 0) = 170879 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a211_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 211))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 211) 305530) = 40186 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b211_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 211)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 211)) 305530) = 40186 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a211_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 211))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 211) 5604) = 304518 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b211_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 211)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 211)) 5604) = 304518 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a211_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 211))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 211) 221549) = 286489 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b211_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 211)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 211)) 221549) = 286489 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a211_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 211))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 211) 266275) = 165820 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b211_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 211)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 211)) 266275) = 165820 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a211_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 211))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 211) 186844) = 268849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b211_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 211)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 211)) 186844) = 268849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o211 : xone 211 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a211_0 b211_0 a211_1 b211_1 a211_2 b211_2
    a211_3 b211_3 a211_4 b211_4 a211_5 b211_5

theorem a212_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 212))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 212) 0) = 260807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b212_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 212)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 212)) 0) = 260807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a212_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 212))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 212) 305530) = 295350 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b212_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 212)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 212)) 305530) = 295350 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a212_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 212))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 212) 5604) = 236921 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b212_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 212)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 212)) 5604) = 236921 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a212_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 212))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 212) 221549) = 124410 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b212_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 212)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 212)) 221549) = 124410 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a212_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 212))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 212) 266275) = 222392 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b212_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 212)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 212)) 266275) = 222392 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a212_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 212))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 212) 186844) = 199400 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b212_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 212)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 212)) 186844) = 199400 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o212 : xone 212 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a212_0 b212_0 a212_1 b212_1 a212_2 b212_2
    a212_3 b212_3 a212_4 b212_4 a212_5 b212_5

theorem a213_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 213))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 213) 0) = 33437 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b213_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 213)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 213)) 0) = 33437 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a213_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 213))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 213) 305530) = 37657 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b213_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 213)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 213)) 305530) = 37657 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a213_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 213))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 213) 5604) = 121274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b213_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 213)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 213)) 5604) = 121274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a213_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 213))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 213) 221549) = 46527 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b213_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 213)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 213)) 221549) = 46527 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a213_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 213))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 213) 266275) = 59081 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b213_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 213)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 213)) 266275) = 59081 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a213_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 213))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 213) 186844) = 269990 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b213_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 213)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 213)) 186844) = 269990 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o213 : xone 213 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a213_0 b213_0 a213_1 b213_1 a213_2 b213_2
    a213_3 b213_3 a213_4 b213_4 a213_5 b213_5

theorem a214_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 214))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 214) 0) = 105257 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b214_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 214)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 214)) 0) = 105257 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a214_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 214))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 214) 305530) = 69742 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b214_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 214)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 214)) 305530) = 69742 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a214_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 214))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 214) 5604) = 203444 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b214_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 214)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 214)) 5604) = 203444 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a214_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 214))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 214) 221549) = 146780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b214_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 214)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 214)) 221549) = 146780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a214_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 214))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 214) 266275) = 12351 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b214_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 214)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 214)) 266275) = 12351 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a214_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 214))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 214) 186844) = 183393 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b214_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 214)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 214)) 186844) = 183393 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o214 : xone 214 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a214_0 b214_0 a214_1 b214_1 a214_2 b214_2
    a214_3 b214_3 a214_4 b214_4 a214_5 b214_5

theorem a215_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 215))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 215) 0) = 303433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b215_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 215)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 215)) 0) = 303433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a215_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 215))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 215) 305530) = 296050 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b215_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 215)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 215)) 305530) = 296050 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a215_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 215))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 215) 5604) = 42803 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b215_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 215)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 215)) 5604) = 42803 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a215_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 215))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 215) 221549) = 306235 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b215_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 215)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 215)) 221549) = 306235 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a215_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 215))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 215) 266275) = 186208 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b215_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 215)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 215)) 266275) = 186208 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a215_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 215))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 215) 186844) = 59576 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b215_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 215)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 215)) 186844) = 59576 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o215 : xone 215 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a215_0 b215_0 a215_1 b215_1 a215_2 b215_2
    a215_3 b215_3 a215_4 b215_4 a215_5 b215_5

theorem a216_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 216))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 216) 0) = 112543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b216_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 216)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 216)) 0) = 112543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a216_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 216))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 216) 305530) = 151571 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b216_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 216)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 216)) 305530) = 151571 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a216_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 216))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 216) 5604) = 73886 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b216_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 216)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 216)) 5604) = 73886 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a216_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 216))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 216) 221549) = 108670 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b216_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 216)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 216)) 221549) = 108670 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a216_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 216))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 216) 266275) = 239363 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b216_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 216)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 216)) 266275) = 239363 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a216_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 216))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 216) 186844) = 255109 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b216_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 216)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 216)) 186844) = 255109 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o216 : xone 216 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a216_0 b216_0 a216_1 b216_1 a216_2 b216_2
    a216_3 b216_3 a216_4 b216_4 a216_5 b216_5

theorem a217_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 217))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 217) 0) = 99686 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b217_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 217)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 217)) 0) = 99686 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a217_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 217))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 217) 305530) = 258200 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b217_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 217)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 217)) 305530) = 258200 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a217_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 217))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 217) 5604) = 56522 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b217_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 217)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 217)) 5604) = 56522 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a217_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 217))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 217) 221549) = 118701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b217_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 217)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 217)) 221549) = 118701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a217_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 217))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 217) 266275) = 96833 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b217_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 217)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 217)) 266275) = 96833 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a217_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 217))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 217) 186844) = 79203 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b217_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 217)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 217)) 186844) = 79203 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o217 : xone 217 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a217_0 b217_0 a217_1 b217_1 a217_2 b217_2
    a217_3 b217_3 a217_4 b217_4 a217_5 b217_5

theorem a218_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 218))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 218) 0) = 234345 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b218_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 218)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 218)) 0) = 234345 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a218_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 218))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 218) 305530) = 51125 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b218_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 218)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 218)) 305530) = 51125 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a218_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 218))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 218) 5604) = 296394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b218_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 218)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 218)) 5604) = 296394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a218_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 218))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 218) 221549) = 82172 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b218_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 218)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 218)) 221549) = 82172 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a218_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 218))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 218) 266275) = 17515 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b218_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 218)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 218)) 266275) = 17515 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a218_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 218))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 218) 186844) = 81689 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b218_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 218)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 218)) 186844) = 81689 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o218 : xone 218 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a218_0 b218_0 a218_1 b218_1 a218_2 b218_2
    a218_3 b218_3 a218_4 b218_4 a218_5 b218_5

theorem a219_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 219))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 219) 0) = 275231 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b219_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 219)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 219)) 0) = 275231 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a219_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 219))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 219) 305530) = 62838 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b219_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 219)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 219)) 305530) = 62838 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a219_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 219))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 219) 5604) = 292927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b219_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 219)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 219)) 5604) = 292927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a219_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 219))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 219) 221549) = 306406 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b219_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 219)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 219)) 221549) = 306406 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a219_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 219))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 219) 266275) = 274094 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b219_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 219)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 219)) 266275) = 274094 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a219_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 219))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 219) 186844) = 79103 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b219_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 219)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 219)) 186844) = 79103 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o219 : xone 219 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a219_0 b219_0 a219_1 b219_1 a219_2 b219_2
    a219_3 b219_3 a219_4 b219_4 a219_5 b219_5

theorem a220_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 220))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 220) 0) = 6396 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b220_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 220)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 220)) 0) = 6396 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a220_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 220))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 220) 305530) = 187204 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b220_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 220)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 220)) 305530) = 187204 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a220_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 220))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 220) 5604) = 143665 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b220_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 220)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 220)) 5604) = 143665 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a220_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 220))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 220) 221549) = 108867 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b220_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 220)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 220)) 221549) = 108867 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a220_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 220))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 220) 266275) = 117820 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b220_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 220)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 220)) 266275) = 117820 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a220_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 220))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 220) 186844) = 68374 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b220_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 220)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 220)) 186844) = 68374 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o220 : xone 220 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a220_0 b220_0 a220_1 b220_1 a220_2 b220_2
    a220_3 b220_3 a220_4 b220_4 a220_5 b220_5

theorem a221_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 221))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 221) 0) = 231394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b221_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 221)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 221)) 0) = 231394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a221_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 221))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 221) 305530) = 221602 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b221_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 221)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 221)) 305530) = 221602 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a221_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 221))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 221) 5604) = 40780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b221_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 221)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 221)) 5604) = 40780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a221_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 221))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 221) 221549) = 24947 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b221_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 221)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 221)) 221549) = 24947 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a221_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 221))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 221) 266275) = 216613 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b221_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 221)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 221)) 266275) = 216613 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a221_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 221))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 221) 186844) = 300940 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b221_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 221)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 221)) 186844) = 300940 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o221 : xone 221 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a221_0 b221_0 a221_1 b221_1 a221_2 b221_2
    a221_3 b221_3 a221_4 b221_4 a221_5 b221_5

theorem a222_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 222))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 222) 0) = 201115 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b222_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 222)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 222)) 0) = 201115 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a222_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 222))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 222) 305530) = 199711 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b222_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 222)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 222)) 305530) = 199711 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a222_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 222))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 222) 5604) = 5571 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b222_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 222)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 222)) 5604) = 5571 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a222_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 222))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 222) 221549) = 285863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b222_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 222)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 222)) 221549) = 285863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a222_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 222))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 222) 266275) = 11080 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b222_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 222)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 222)) 266275) = 11080 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a222_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 222))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 222) 186844) = 226887 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b222_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 222)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 222)) 186844) = 226887 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o222 : xone 222 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a222_0 b222_0 a222_1 b222_1 a222_2 b222_2
    a222_3 b222_3 a222_4 b222_4 a222_5 b222_5

theorem a223_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 223))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 223) 0) = 81050 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b223_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 223)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 223)) 0) = 81050 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a223_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 223))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 223) 305530) = 56784 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b223_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 223)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 223)) 305530) = 56784 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a223_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 223))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 223) 5604) = 231925 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b223_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 223)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 223)) 5604) = 231925 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a223_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 223))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 223) 221549) = 306229 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b223_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 223)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 223)) 221549) = 306229 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a223_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 223))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 223) 266275) = 297142 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b223_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 223)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 223)) 266275) = 297142 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a223_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 223))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 223) 186844) = 260110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b223_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 223)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 223)) 186844) = 260110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o223 : xone 223 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a223_0 b223_0 a223_1 b223_1 a223_2 b223_2
    a223_3 b223_3 a223_4 b223_4 a223_5 b223_5

theorem a224_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 224))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 224) 0) = 41821 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b224_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 224)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 224)) 0) = 41821 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a224_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 224))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 224) 305530) = 83521 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b224_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 224)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 224)) 305530) = 83521 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a224_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 224))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 224) 5604) = 138759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b224_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 224)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 224)) 5604) = 138759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a224_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 224))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 224) 221549) = 151903 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b224_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 224)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 224)) 221549) = 151903 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a224_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 224))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 224) 266275) = 89727 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b224_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 224)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 224)) 266275) = 89727 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a224_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 224))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 224) 186844) = 144004 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b224_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 224)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 224)) 186844) = 144004 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o224 : xone 224 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a224_0 b224_0 a224_1 b224_1 a224_2 b224_2
    a224_3 b224_3 a224_4 b224_4 a224_5 b224_5

theorem a225_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 225))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 225) 0) = 31899 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b225_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 225)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 225)) 0) = 31899 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a225_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 225))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 225) 305530) = 93206 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b225_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 225)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 225)) 305530) = 93206 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a225_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 225))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 225) 5604) = 246131 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b225_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 225)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 225)) 5604) = 246131 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a225_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 225))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 225) 221549) = 59770 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b225_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 225)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 225)) 221549) = 59770 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a225_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 225))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 225) 266275) = 254450 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b225_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 225)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 225)) 266275) = 254450 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a225_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 225))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 225) 186844) = 239940 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b225_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 225)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 225)) 186844) = 239940 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o225 : xone 225 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a225_0 b225_0 a225_1 b225_1 a225_2 b225_2
    a225_3 b225_3 a225_4 b225_4 a225_5 b225_5

theorem a226_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 226))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 226) 0) = 164095 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b226_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 226)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 226)) 0) = 164095 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a226_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 226))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 226) 305530) = 179739 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b226_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 226)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 226)) 305530) = 179739 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a226_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 226))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 226) 5604) = 204578 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b226_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 226)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 226)) 5604) = 204578 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a226_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 226))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 226) 221549) = 158963 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b226_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 226)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 226)) 221549) = 158963 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a226_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 226))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 226) 266275) = 64924 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b226_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 226)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 226)) 266275) = 64924 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a226_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 226))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 226) 186844) = 99650 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b226_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 226)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 226)) 186844) = 99650 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o226 : xone 226 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a226_0 b226_0 a226_1 b226_1 a226_2 b226_2
    a226_3 b226_3 a226_4 b226_4 a226_5 b226_5

theorem a227_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 227))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 227) 0) = 254274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b227_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 227)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 227)) 0) = 254274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a227_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 227))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 227) 305530) = 164152 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b227_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 227)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 227)) 305530) = 164152 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a227_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 227))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 227) 5604) = 180486 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b227_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 227)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 227)) 5604) = 180486 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a227_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 227))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 227) 221549) = 22513 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b227_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 227)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 227)) 221549) = 22513 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a227_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 227))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 227) 266275) = 297329 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b227_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 227)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 227)) 266275) = 297329 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a227_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 227))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 227) 186844) = 176217 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b227_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 227)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 227)) 186844) = 176217 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o227 : xone 227 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a227_0 b227_0 a227_1 b227_1 a227_2 b227_2
    a227_3 b227_3 a227_4 b227_4 a227_5 b227_5

theorem a228_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 228))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 228) 0) = 298209 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b228_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 228)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 228)) 0) = 298209 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a228_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 228))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 228) 305530) = 89288 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b228_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 228)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 228)) 305530) = 89288 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a228_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 228))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 228) 5604) = 274601 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b228_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 228)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 228)) 5604) = 274601 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a228_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 228))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 228) 221549) = 225826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b228_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 228)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 228)) 221549) = 225826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a228_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 228))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 228) 266275) = 64927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b228_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 228)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 228)) 266275) = 64927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a228_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 228))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 228) 186844) = 118280 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b228_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 228)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 228)) 186844) = 118280 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o228 : xone 228 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a228_0 b228_0 a228_1 b228_1 a228_2 b228_2
    a228_3 b228_3 a228_4 b228_4 a228_5 b228_5

theorem a229_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 229))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 229) 0) = 43990 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b229_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 229)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 229)) 0) = 43990 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a229_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 229))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 229) 305530) = 277697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b229_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 229)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 229)) 305530) = 277697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a229_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 229))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 229) 5604) = 252241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b229_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 229)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 229)) 5604) = 252241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a229_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 229))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 229) 221549) = 92777 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b229_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 229)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 229)) 221549) = 92777 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a229_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 229))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 229) 266275) = 38103 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b229_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 229)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 229)) 266275) = 38103 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a229_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 229))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 229) 186844) = 251805 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b229_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 229)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 229)) 186844) = 251805 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o229 : xone 229 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a229_0 b229_0 a229_1 b229_1 a229_2 b229_2
    a229_3 b229_3 a229_4 b229_4 a229_5 b229_5

theorem a230_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 230))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 230) 0) = 259697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b230_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 230)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 230)) 0) = 259697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a230_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 230))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 230) 305530) = 279851 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b230_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 230)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 230)) 305530) = 279851 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a230_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 230))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 230) 5604) = 247474 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b230_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 230)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 230)) 5604) = 247474 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a230_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 230))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 230) 221549) = 140592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b230_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 230)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 230)) 221549) = 140592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a230_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 230))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 230) 266275) = 13527 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b230_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 230)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 230)) 266275) = 13527 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a230_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 230))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 230) 186844) = 187897 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b230_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 230)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 230)) 186844) = 187897 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o230 : xone 230 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a230_0 b230_0 a230_1 b230_1 a230_2 b230_2
    a230_3 b230_3 a230_4 b230_4 a230_5 b230_5

theorem a231_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 231))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 231) 0) = 211443 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b231_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 231)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 231)) 0) = 211443 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a231_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 231))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 231) 305530) = 275333 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b231_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 231)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 231)) 305530) = 275333 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a231_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 231))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 231) 5604) = 50116 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b231_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 231)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 231)) 5604) = 50116 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a231_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 231))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 231) 221549) = 187715 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b231_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 231)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 231)) 221549) = 187715 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a231_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 231))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 231) 266275) = 221672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b231_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 231)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 231)) 266275) = 221672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a231_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 231))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 231) 186844) = 89093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b231_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 231)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 231)) 186844) = 89093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o231 : xone 231 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a231_0 b231_0 a231_1 b231_1 a231_2 b231_2
    a231_3 b231_3 a231_4 b231_4 a231_5 b231_5

theorem a232_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 232))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 232) 0) = 237839 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b232_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 232)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 232)) 0) = 237839 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a232_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 232))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 232) 305530) = 268077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b232_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 232)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 232)) 305530) = 268077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a232_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 232))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 232) 5604) = 95619 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b232_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 232)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 232)) 5604) = 95619 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a232_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 232))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 232) 221549) = 160028 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b232_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 232)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 232)) 221549) = 160028 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a232_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 232))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 232) 266275) = 302731 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b232_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 232)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 232)) 266275) = 302731 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a232_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 232))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 232) 186844) = 227285 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b232_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 232)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 232)) 186844) = 227285 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o232 : xone 232 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a232_0 b232_0 a232_1 b232_1 a232_2 b232_2
    a232_3 b232_3 a232_4 b232_4 a232_5 b232_5

theorem a233_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 233))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 233) 0) = 95109 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b233_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 233)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 233)) 0) = 95109 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a233_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 233))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 233) 305530) = 88444 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b233_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 233)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 233)) 305530) = 88444 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a233_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 233))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 233) 5604) = 37215 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b233_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 233)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 233)) 5604) = 37215 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a233_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 233))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 233) 221549) = 70376 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b233_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 233)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 233)) 221549) = 70376 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a233_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 233))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 233) 266275) = 241698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b233_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 233)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 233)) 266275) = 241698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a233_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 233))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 233) 186844) = 67391 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b233_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 233)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 233)) 186844) = 67391 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o233 : xone 233 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a233_0 b233_0 a233_1 b233_1 a233_2 b233_2
    a233_3 b233_3 a233_4 b233_4 a233_5 b233_5

theorem a234_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 234))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 234) 0) = 194697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b234_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 234)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 234)) 0) = 194697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a234_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 234))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 234) 305530) = 114562 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b234_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 234)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 234)) 305530) = 114562 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a234_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 234))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 234) 5604) = 140484 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b234_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 234)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 234)) 5604) = 140484 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a234_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 234))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 234) 221549) = 82935 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b234_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 234)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 234)) 221549) = 82935 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a234_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 234))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 234) 266275) = 289774 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b234_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 234)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 234)) 266275) = 289774 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a234_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 234))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 234) 186844) = 77952 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b234_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 234)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 234)) 186844) = 77952 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o234 : xone 234 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a234_0 b234_0 a234_1 b234_1 a234_2 b234_2
    a234_3 b234_3 a234_4 b234_4 a234_5 b234_5

theorem a235_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 235))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 235) 0) = 177922 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b235_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 235)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 235)) 0) = 177922 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a235_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 235))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 235) 305530) = 253932 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b235_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 235)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 235)) 305530) = 253932 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a235_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 235))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 235) 5604) = 292375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b235_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 235)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 235)) 5604) = 292375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a235_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 235))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 235) 221549) = 265568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b235_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 235)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 235)) 221549) = 265568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a235_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 235))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 235) 266275) = 80080 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b235_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 235)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 235)) 266275) = 80080 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a235_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 235))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 235) 186844) = 157748 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b235_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 235)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 235)) 186844) = 157748 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o235 : xone 235 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a235_0 b235_0 a235_1 b235_1 a235_2 b235_2
    a235_3 b235_3 a235_4 b235_4 a235_5 b235_5

theorem a236_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 236))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 236) 0) = 119292 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b236_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 236)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 236)) 0) = 119292 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a236_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 236))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 236) 305530) = 160960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b236_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 236)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 236)) 305530) = 160960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a236_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 236))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 236) 5604) = 266902 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b236_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 236)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 236)) 5604) = 266902 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a236_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 236))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 236) 221549) = 112054 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b236_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 236)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 236)) 221549) = 112054 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a236_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 236))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 236) 266275) = 31882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b236_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 236)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 236)) 266275) = 31882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a236_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 236))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 236) 186844) = 80933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b236_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 236)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 236)) 186844) = 80933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o236 : xone 236 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a236_0 b236_0 a236_1 b236_1 a236_2 b236_2
    a236_3 b236_3 a236_4 b236_4 a236_5 b236_5

theorem a237_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 237))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 237) 0) = 228609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b237_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 237)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 237)) 0) = 228609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a237_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 237))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 237) 305530) = 100523 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b237_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 237)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 237)) 305530) = 100523 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a237_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 237))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 237) 5604) = 104367 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b237_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 237)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 237)) 5604) = 104367 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a237_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 237))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 237) 221549) = 30432 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b237_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 237)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 237)) 221549) = 30432 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a237_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 237))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 237) 266275) = 131388 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b237_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 237)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 237)) 266275) = 131388 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a237_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 237))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 237) 186844) = 8153 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b237_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 237)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 237)) 186844) = 8153 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o237 : xone 237 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a237_0 b237_0 a237_1 b237_1 a237_2 b237_2
    a237_3 b237_3 a237_4 b237_4 a237_5 b237_5

theorem a238_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 238))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 238) 0) = 38025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b238_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 238)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 238)) 0) = 38025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a238_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 238))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 238) 305530) = 260912 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b238_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 238)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 238)) 305530) = 260912 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a238_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 238))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 238) 5604) = 180740 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b238_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 238)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 238)) 5604) = 180740 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a238_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 238))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 238) 221549) = 107665 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b238_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 238)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 238)) 221549) = 107665 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a238_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 238))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 238) 266275) = 262420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b238_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 238)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 238)) 266275) = 262420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a238_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 238))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 238) 186844) = 122491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b238_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 238)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 238)) 186844) = 122491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o238 : xone 238 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a238_0 b238_0 a238_1 b238_1 a238_2 b238_2
    a238_3 b238_3 a238_4 b238_4 a238_5 b238_5

theorem a239_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 239))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 239) 0) = 259222 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b239_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 239)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 239)) 0) = 259222 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a239_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 239))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 239) 305530) = 190876 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b239_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 239)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 239)) 305530) = 190876 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a239_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 239))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 239) 5604) = 272599 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b239_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 239)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 239)) 5604) = 272599 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a239_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 239))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 239) 221549) = 58348 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b239_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 239)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 239)) 221549) = 58348 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a239_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 239))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 239) 266275) = 200446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b239_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 239)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 239)) 266275) = 200446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a239_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 239))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 239) 186844) = 18543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b239_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 239)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 239)) 186844) = 18543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o239 : xone 239 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a239_0 b239_0 a239_1 b239_1 a239_2 b239_2
    a239_3 b239_3 a239_4 b239_4 a239_5 b239_5

theorem a240_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 240))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 240) 0) = 13018 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b240_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 240)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 240)) 0) = 13018 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a240_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 240))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 240) 305530) = 244452 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b240_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 240)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 240)) 305530) = 244452 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a240_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 240))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 240) 5604) = 216531 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b240_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 240)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 240)) 5604) = 216531 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a240_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 240))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 240) 221549) = 83446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b240_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 240)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 240)) 221549) = 83446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a240_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 240))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 240) 266275) = 226208 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b240_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 240)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 240)) 266275) = 226208 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a240_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 240))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 240) 186844) = 19608 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b240_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 240)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 240)) 186844) = 19608 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o240 : xone 240 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a240_0 b240_0 a240_1 b240_1 a240_2 b240_2
    a240_3 b240_3 a240_4 b240_4 a240_5 b240_5

theorem a241_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 241))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 241) 0) = 164201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b241_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 241)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 241)) 0) = 164201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a241_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 241))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 241) 305530) = 241603 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b241_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 241)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 241)) 305530) = 241603 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a241_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 241))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 241) 5604) = 62344 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b241_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 241)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 241)) 5604) = 62344 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a241_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 241))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 241) 221549) = 295800 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b241_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 241)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 241)) 221549) = 295800 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a241_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 241))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 241) 266275) = 274320 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b241_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 241)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 241)) 266275) = 274320 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a241_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 241))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 241) 186844) = 120834 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b241_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 241)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 241)) 186844) = 120834 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o241 : xone 241 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a241_0 b241_0 a241_1 b241_1 a241_2 b241_2
    a241_3 b241_3 a241_4 b241_4 a241_5 b241_5

theorem a242_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 242))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 242) 0) = 284666 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b242_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 242)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 242)) 0) = 284666 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a242_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 242))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 242) 305530) = 265981 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b242_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 242)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 242)) 305530) = 265981 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a242_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 242))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 242) 5604) = 253468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b242_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 242)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 242)) 5604) = 253468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a242_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 242))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 242) 221549) = 143079 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b242_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 242)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 242)) 221549) = 143079 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a242_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 242))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 242) 266275) = 71733 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b242_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 242)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 242)) 266275) = 71733 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a242_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 242))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 242) 186844) = 96228 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b242_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 242)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 242)) 186844) = 96228 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o242 : xone 242 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a242_0 b242_0 a242_1 b242_1 a242_2 b242_2
    a242_3 b242_3 a242_4 b242_4 a242_5 b242_5

theorem a243_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 243))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 243) 0) = 173552 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b243_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 243)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 243)) 0) = 173552 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a243_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 243))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 243) 305530) = 204820 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b243_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 243)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 243)) 305530) = 204820 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a243_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 243))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 243) 5604) = 198687 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b243_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 243)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 243)) 5604) = 198687 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a243_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 243))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 243) 221549) = 80118 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b243_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 243)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 243)) 221549) = 80118 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a243_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 243))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 243) 266275) = 130428 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b243_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 243)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 243)) 266275) = 130428 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a243_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 243))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 243) 186844) = 55816 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b243_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 243)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 243)) 186844) = 55816 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o243 : xone 243 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a243_0 b243_0 a243_1 b243_1 a243_2 b243_2
    a243_3 b243_3 a243_4 b243_4 a243_5 b243_5

theorem a244_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 244))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 244) 0) = 40759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b244_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 244)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 244)) 0) = 40759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a244_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 244))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 244) 305530) = 153297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b244_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 244)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 244)) 305530) = 153297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a244_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 244))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 244) 5604) = 240840 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b244_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 244)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 244)) 5604) = 240840 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a244_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 244))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 244) 221549) = 32288 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b244_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 244)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 244)) 221549) = 32288 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a244_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 244))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 244) 266275) = 171744 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b244_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 244)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 244)) 266275) = 171744 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a244_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 244))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 244) 186844) = 265531 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b244_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 244)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 244)) 186844) = 265531 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o244 : xone 244 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a244_0 b244_0 a244_1 b244_1 a244_2 b244_2
    a244_3 b244_3 a244_4 b244_4 a244_5 b244_5

theorem a245_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 245))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 245) 0) = 98645 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b245_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 245)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 245)) 0) = 98645 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a245_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 245))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 245) 305530) = 162693 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b245_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 245)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 245)) 305530) = 162693 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a245_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 245))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 245) 5604) = 225459 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b245_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 245)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 245)) 5604) = 225459 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a245_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 245))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 245) 221549) = 13953 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b245_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 245)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 245)) 221549) = 13953 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a245_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 245))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 245) 266275) = 249403 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b245_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 245)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 245)) 266275) = 249403 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a245_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 245))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 245) 186844) = 19611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b245_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 245)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 245)) 186844) = 19611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o245 : xone 245 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a245_0 b245_0 a245_1 b245_1 a245_2 b245_2
    a245_3 b245_3 a245_4 b245_4 a245_5 b245_5

theorem a246_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 246))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 246) 0) = 158577 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b246_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 246)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 246)) 0) = 158577 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a246_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 246))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 246) 305530) = 22535 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b246_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 246)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 246)) 305530) = 22535 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a246_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 246))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 246) 5604) = 185352 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b246_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 246)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 246)) 5604) = 185352 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a246_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 246))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 246) 221549) = 216716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b246_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 246)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 246)) 221549) = 216716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a246_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 246))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 246) 266275) = 139793 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b246_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 246)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 246)) 266275) = 139793 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a246_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 246))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 246) 186844) = 170349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b246_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 246)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 246)) 186844) = 170349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o246 : xone 246 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a246_0 b246_0 a246_1 b246_1 a246_2 b246_2
    a246_3 b246_3 a246_4 b246_4 a246_5 b246_5

theorem a247_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 247))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 247) 0) = 259425 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b247_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 247)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 247)) 0) = 259425 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a247_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 247))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 247) 305530) = 156772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b247_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 247)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 247)) 305530) = 156772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a247_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 247))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 247) 5604) = 68115 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b247_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 247)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 247)) 5604) = 68115 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a247_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 247))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 247) 221549) = 194247 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b247_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 247)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 247)) 221549) = 194247 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a247_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 247))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 247) 266275) = 127540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b247_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 247)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 247)) 266275) = 127540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a247_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 247))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 247) 186844) = 259634 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b247_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 247)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 247)) 186844) = 259634 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o247 : xone 247 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a247_0 b247_0 a247_1 b247_1 a247_2 b247_2
    a247_3 b247_3 a247_4 b247_4 a247_5 b247_5

theorem a248_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 248))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 248) 0) = 203957 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b248_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 248)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 248)) 0) = 203957 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a248_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 248))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 248) 305530) = 260426 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b248_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 248)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 248)) 305530) = 260426 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a248_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 248))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 248) 5604) = 241900 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b248_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 248)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 248)) 5604) = 241900 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a248_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 248))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 248) 221549) = 165555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b248_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 248)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 248)) 221549) = 165555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a248_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 248))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 248) 266275) = 193646 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b248_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 248)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 248)) 266275) = 193646 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a248_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 248))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 248) 186844) = 105065 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b248_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 248)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 248)) 186844) = 105065 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o248 : xone 248 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a248_0 b248_0 a248_1 b248_1 a248_2 b248_2
    a248_3 b248_3 a248_4 b248_4 a248_5 b248_5

theorem a249_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 249))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 249) 0) = 186896 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b249_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 249)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 249)) 0) = 186896 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a249_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 249))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 249) 305530) = 83154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b249_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 249)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 249)) 305530) = 83154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a249_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 249))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 249) 5604) = 304245 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b249_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 249)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 249)) 5604) = 304245 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a249_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 249))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 249) 221549) = 121120 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b249_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 249)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 249)) 221549) = 121120 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a249_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 249))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 249) 266275) = 3202 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b249_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 249)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 249)) 266275) = 3202 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a249_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 249))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 249) 186844) = 52846 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b249_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 249)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 249)) 186844) = 52846 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o249 : xone 249 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a249_0 b249_0 a249_1 b249_1 a249_2 b249_2
    a249_3 b249_3 a249_4 b249_4 a249_5 b249_5

theorem a250_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 250))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 250) 0) = 293035 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b250_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 250)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 250)) 0) = 293035 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a250_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 250))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 250) 305530) = 105240 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b250_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 250)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 250)) 305530) = 105240 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a250_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 250))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 250) 5604) = 274240 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b250_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 250)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 250)) 5604) = 274240 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a250_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 250))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 250) 221549) = 303906 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b250_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 250)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 250)) 221549) = 303906 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a250_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 250))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 250) 266275) = 196092 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b250_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 250)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 250)) 266275) = 196092 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a250_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 250))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 250) 186844) = 127414 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b250_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 250)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 250)) 186844) = 127414 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o250 : xone 250 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a250_0 b250_0 a250_1 b250_1 a250_2 b250_2
    a250_3 b250_3 a250_4 b250_4 a250_5 b250_5

theorem a251_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 251))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 251) 0) = 32196 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b251_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 251)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 251)) 0) = 32196 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a251_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 251))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 251) 305530) = 67359 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b251_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 251)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 251)) 305530) = 67359 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a251_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 251))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 251) 5604) = 71612 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b251_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 251)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 251)) 5604) = 71612 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a251_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 251))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 251) 221549) = 152342 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b251_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 251)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 251)) 221549) = 152342 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a251_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 251))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 251) 266275) = 56260 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b251_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 251)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 251)) 266275) = 56260 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a251_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 251))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 251) 186844) = 93973 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b251_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 251)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 251)) 186844) = 93973 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o251 : xone 251 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a251_0 b251_0 a251_1 b251_1 a251_2 b251_2
    a251_3 b251_3 a251_4 b251_4 a251_5 b251_5

theorem a252_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 252))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 252) 0) = 153678 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b252_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 252)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 252)) 0) = 153678 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a252_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 252))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 252) 305530) = 245361 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b252_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 252)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 252)) 305530) = 245361 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a252_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 252))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 252) 5604) = 84894 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b252_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 252)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 252)) 5604) = 84894 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a252_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 252))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 252) 221549) = 1716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b252_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 252)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 252)) 221549) = 1716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a252_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 252))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 252) 266275) = 93934 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b252_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 252)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 252)) 266275) = 93934 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a252_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 252))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 252) 186844) = 165304 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b252_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 252)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 252)) 186844) = 165304 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o252 : xone 252 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a252_0 b252_0 a252_1 b252_1 a252_2 b252_2
    a252_3 b252_3 a252_4 b252_4 a252_5 b252_5

theorem a253_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 253))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 253) 0) = 207466 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b253_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 253)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 253)) 0) = 207466 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a253_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 253))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 253) 305530) = 181093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b253_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 253)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 253)) 305530) = 181093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a253_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 253))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 253) 5604) = 25825 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b253_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 253)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 253)) 5604) = 25825 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a253_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 253))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 253) 221549) = 151084 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b253_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 253)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 253)) 221549) = 151084 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a253_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 253))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 253) 266275) = 283684 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b253_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 253)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 253)) 266275) = 283684 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a253_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 253))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 253) 186844) = 108869 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b253_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 253)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 253)) 186844) = 108869 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o253 : xone 253 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a253_0 b253_0 a253_1 b253_1 a253_2 b253_2
    a253_3 b253_3 a253_4 b253_4 a253_5 b253_5

theorem a254_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 254))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 254) 0) = 50859 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b254_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 254)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 254)) 0) = 50859 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a254_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 254))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 254) 305530) = 52312 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b254_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 254)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 254)) 305530) = 52312 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a254_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 254))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 254) 5604) = 175211 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b254_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 254)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 254)) 5604) = 175211 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a254_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 254))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 254) 221549) = 98022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b254_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 254)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 254)) 221549) = 98022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a254_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 254))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 254) 266275) = 217197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b254_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 254)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 254)) 266275) = 217197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a254_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 254))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 254) 186844) = 37241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b254_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 254)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 254)) 186844) = 37241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o254 : xone 254 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a254_0 b254_0 a254_1 b254_1 a254_2 b254_2
    a254_3 b254_3 a254_4 b254_4 a254_5 b254_5

theorem a255_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 255))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 255) 0) = 200254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b255_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 255)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 255)) 0) = 200254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a255_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 255))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 255) 305530) = 99720 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b255_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 255)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 255)) 305530) = 99720 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a255_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 255))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 255) 5604) = 144925 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b255_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 255)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 255)) 5604) = 144925 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a255_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 255))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 255) 221549) = 239568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b255_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 255)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 255)) 221549) = 239568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a255_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 255))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 255) 266275) = 201067 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b255_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 255)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 255)) 266275) = 201067 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a255_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 255))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 255) 186844) = 164424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b255_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 255)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 255)) 186844) = 164424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o255 : xone 255 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a255_0 b255_0 a255_1 b255_1 a255_2 b255_2
    a255_3 b255_3 a255_4 b255_4 a255_5 b255_5

theorem a256_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 256))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 256) 0) = 26635 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b256_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 256)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 256)) 0) = 26635 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a256_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 256))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 256) 305530) = 190768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b256_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 256)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 256)) 305530) = 190768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a256_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 256))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 256) 5604) = 210176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b256_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 256)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 256)) 5604) = 210176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a256_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 256))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 256) 221549) = 127933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b256_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 256)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 256)) 221549) = 127933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a256_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 256))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 256) 266275) = 166318 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b256_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 256)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 256)) 266275) = 166318 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a256_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 256))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 256) 186844) = 38804 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b256_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 256)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 256)) 186844) = 38804 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o256 : xone 256 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a256_0 b256_0 a256_1 b256_1 a256_2 b256_2
    a256_3 b256_3 a256_4 b256_4 a256_5 b256_5

theorem a257_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 257))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 257) 0) = 7253 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b257_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 257)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 257)) 0) = 7253 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a257_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 257))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 257) 305530) = 8777 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b257_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 257)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 257)) 305530) = 8777 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a257_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 257))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 257) 5604) = 100449 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b257_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 257)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 257)) 5604) = 100449 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a257_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 257))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 257) 221549) = 259553 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b257_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 257)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 257)) 221549) = 259553 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a257_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 257))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 257) 266275) = 252040 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b257_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 257)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 257)) 266275) = 252040 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a257_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 257))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 257) 186844) = 218594 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b257_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 257)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 257)) 186844) = 218594 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o257 : xone 257 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a257_0 b257_0 a257_1 b257_1 a257_2 b257_2
    a257_3 b257_3 a257_4 b257_4 a257_5 b257_5

theorem a258_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 258))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 258) 0) = 23401 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b258_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 258)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 258)) 0) = 23401 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a258_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 258))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 258) 305530) = 132692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b258_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 258)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 258)) 305530) = 132692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a258_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 258))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 258) 5604) = 140765 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b258_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 258)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 258)) 5604) = 140765 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a258_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 258))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 258) 221549) = 274988 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b258_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 258)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 258)) 221549) = 274988 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a258_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 258))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 258) 266275) = 294904 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b258_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 258)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 258)) 266275) = 294904 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a258_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 258))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 258) 186844) = 163776 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b258_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 258)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 258)) 186844) = 163776 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o258 : xone 258 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a258_0 b258_0 a258_1 b258_1 a258_2 b258_2
    a258_3 b258_3 a258_4 b258_4 a258_5 b258_5

theorem a259_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 259))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 259) 0) = 88468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b259_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 259)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 259)) 0) = 88468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a259_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 259))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 259) 305530) = 107081 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b259_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 259)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 259)) 305530) = 107081 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a259_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 259))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 259) 5604) = 103130 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b259_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 259)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 259)) 5604) = 103130 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a259_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 259))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 259) 221549) = 26126 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b259_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 259)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 259)) 221549) = 26126 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a259_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 259))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 259) 266275) = 210113 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b259_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 259)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 259)) 266275) = 210113 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a259_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 259))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 259) 186844) = 94887 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b259_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 259)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 259)) 186844) = 94887 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o259 : xone 259 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a259_0 b259_0 a259_1 b259_1 a259_2 b259_2
    a259_3 b259_3 a259_4 b259_4 a259_5 b259_5

theorem a260_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 260))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 260) 0) = 69330 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b260_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 260)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 260)) 0) = 69330 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a260_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 260))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 260) 305530) = 251366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b260_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 260)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 260)) 305530) = 251366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a260_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 260))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 260) 5604) = 11938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b260_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 260)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 260)) 5604) = 11938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a260_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 260))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 260) 221549) = 163518 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b260_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 260)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 260)) 221549) = 163518 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a260_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 260))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 260) 266275) = 46586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b260_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 260)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 260)) 266275) = 46586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a260_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 260))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 260) 186844) = 101074 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b260_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 260)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 260)) 186844) = 101074 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o260 : xone 260 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a260_0 b260_0 a260_1 b260_1 a260_2 b260_2
    a260_3 b260_3 a260_4 b260_4 a260_5 b260_5

theorem a261_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 261))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 261) 0) = 137445 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b261_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 261)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 261)) 0) = 137445 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a261_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 261))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 261) 305530) = 3154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b261_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 261)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 261)) 305530) = 3154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a261_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 261))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 261) 5604) = 147089 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b261_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 261)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 261)) 5604) = 147089 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a261_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 261))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 261) 221549) = 28014 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b261_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 261)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 261)) 221549) = 28014 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a261_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 261))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 261) 266275) = 141606 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b261_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 261)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 261)) 266275) = 141606 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a261_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 261))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 261) 186844) = 83508 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b261_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 261)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 261)) 186844) = 83508 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o261 : xone 261 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a261_0 b261_0 a261_1 b261_1 a261_2 b261_2
    a261_3 b261_3 a261_4 b261_4 a261_5 b261_5

theorem a262_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 262))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 262) 0) = 114779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b262_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 262)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 262)) 0) = 114779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a262_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 262))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 262) 305530) = 117112 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b262_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 262)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 262)) 305530) = 117112 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a262_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 262))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 262) 5604) = 252170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b262_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 262)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 262)) 5604) = 252170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a262_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 262))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 262) 221549) = 260674 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b262_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 262)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 262)) 221549) = 260674 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a262_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 262))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 262) 266275) = 279146 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b262_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 262)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 262)) 266275) = 279146 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a262_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 262))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 262) 186844) = 108918 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b262_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 262)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 262)) 186844) = 108918 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o262 : xone 262 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a262_0 b262_0 a262_1 b262_1 a262_2 b262_2
    a262_3 b262_3 a262_4 b262_4 a262_5 b262_5

theorem a263_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 263))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 263) 0) = 247858 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b263_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 263)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 263)) 0) = 247858 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a263_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 263))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 263) 305530) = 83801 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b263_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 263)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 263)) 305530) = 83801 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a263_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 263))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 263) 5604) = 267236 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b263_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 263)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 263)) 5604) = 267236 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a263_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 263))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 263) 221549) = 149416 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b263_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 263)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 263)) 221549) = 149416 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a263_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 263))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 263) 266275) = 70799 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b263_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 263)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 263)) 266275) = 70799 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a263_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 263))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 263) 186844) = 243318 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b263_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 263)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 263)) 186844) = 243318 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o263 : xone 263 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a263_0 b263_0 a263_1 b263_1 a263_2 b263_2
    a263_3 b263_3 a263_4 b263_4 a263_5 b263_5

theorem a264_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 264))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 264) 0) = 128680 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b264_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 264)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 264)) 0) = 128680 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a264_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 264))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 264) 305530) = 14782 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b264_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 264)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 264)) 305530) = 14782 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a264_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 264))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 264) 5604) = 117253 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b264_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 264)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 264)) 5604) = 117253 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a264_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 264))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 264) 221549) = 35038 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b264_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 264)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 264)) 221549) = 35038 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a264_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 264))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 264) 266275) = 12295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b264_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 264)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 264)) 266275) = 12295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a264_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 264))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 264) 186844) = 233754 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b264_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 264)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 264)) 186844) = 233754 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o264 : xone 264 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a264_0 b264_0 a264_1 b264_1 a264_2 b264_2
    a264_3 b264_3 a264_4 b264_4 a264_5 b264_5

theorem a265_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 265))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 265) 0) = 60409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b265_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 265)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 265)) 0) = 60409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a265_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 265))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 265) 305530) = 153355 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b265_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 265)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 265)) 305530) = 153355 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a265_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 265))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 265) 5604) = 5100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b265_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 265)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 265)) 5604) = 5100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a265_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 265))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 265) 221549) = 139484 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b265_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 265)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 265)) 221549) = 139484 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a265_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 265))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 265) 266275) = 57329 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b265_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 265)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 265)) 266275) = 57329 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a265_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 265))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 265) 186844) = 242073 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b265_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 265)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 265)) 186844) = 242073 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o265 : xone 265 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a265_0 b265_0 a265_1 b265_1 a265_2 b265_2
    a265_3 b265_3 a265_4 b265_4 a265_5 b265_5

theorem a266_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 266))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 266) 0) = 74947 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b266_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 266)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 266)) 0) = 74947 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a266_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 266))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 266) 305530) = 205943 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b266_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 266)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 266)) 305530) = 205943 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a266_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 266))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 266) 5604) = 96290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b266_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 266)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 266)) 5604) = 96290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a266_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 266))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 266) 221549) = 107284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b266_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 266)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 266)) 221549) = 107284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a266_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 266))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 266) 266275) = 23254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b266_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 266)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 266)) 266275) = 23254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a266_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 266))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 266) 186844) = 31567 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b266_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 266)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 266)) 186844) = 31567 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o266 : xone 266 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a266_0 b266_0 a266_1 b266_1 a266_2 b266_2
    a266_3 b266_3 a266_4 b266_4 a266_5 b266_5

theorem a267_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 267))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 267) 0) = 4100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b267_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 267)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 267)) 0) = 4100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a267_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 267))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 267) 305530) = 297697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b267_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 267)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 267)) 305530) = 297697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a267_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 267))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 267) 5604) = 99506 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b267_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 267)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 267)) 5604) = 99506 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a267_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 267))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 267) 221549) = 136592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b267_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 267)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 267)) 221549) = 136592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a267_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 267))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 267) 266275) = 301480 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b267_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 267)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 267)) 266275) = 301480 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a267_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 267))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 267) 186844) = 17925 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b267_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 267)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 267)) 186844) = 17925 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o267 : xone 267 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a267_0 b267_0 a267_1 b267_1 a267_2 b267_2
    a267_3 b267_3 a267_4 b267_4 a267_5 b267_5

theorem a268_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 268))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 268) 0) = 163334 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b268_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 268)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 268)) 0) = 163334 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a268_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 268))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 268) 305530) = 96236 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b268_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 268)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 268)) 305530) = 96236 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a268_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 268))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 268) 5604) = 136554 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b268_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 268)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 268)) 5604) = 136554 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a268_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 268))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 268) 221549) = 173259 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b268_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 268)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 268)) 221549) = 173259 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a268_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 268))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 268) 266275) = 265542 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b268_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 268)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 268)) 266275) = 265542 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a268_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 268))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 268) 186844) = 293588 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b268_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 268)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 268)) 186844) = 293588 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o268 : xone 268 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a268_0 b268_0 a268_1 b268_1 a268_2 b268_2
    a268_3 b268_3 a268_4 b268_4 a268_5 b268_5

theorem a269_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 269))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 269) 0) = 291796 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b269_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 269)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 269)) 0) = 291796 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a269_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 269))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 269) 305530) = 65064 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b269_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 269)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 269)) 305530) = 65064 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a269_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 269))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 269) 5604) = 294503 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b269_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 269)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 269)) 5604) = 294503 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a269_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 269))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 269) 221549) = 192555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b269_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 269)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 269)) 221549) = 192555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a269_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 269))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 269) 266275) = 264934 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b269_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 269)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 269)) 266275) = 264934 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a269_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 269))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 269) 186844) = 98228 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b269_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 269)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 269)) 186844) = 98228 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o269 : xone 269 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a269_0 b269_0 a269_1 b269_1 a269_2 b269_2
    a269_3 b269_3 a269_4 b269_4 a269_5 b269_5

theorem a270_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 270))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 270) 0) = 164006 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b270_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 270)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 270)) 0) = 164006 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a270_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 270))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 270) 305530) = 116036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b270_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 270)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 270)) 305530) = 116036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a270_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 270))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 270) 5604) = 47027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b270_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 270)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 270)) 5604) = 47027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a270_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 270))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 270) 221549) = 263249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b270_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 270)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 270)) 221549) = 263249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a270_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 270))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 270) 266275) = 177680 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b270_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 270)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 270)) 266275) = 177680 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a270_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 270))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 270) 186844) = 94312 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b270_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 270)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 270)) 186844) = 94312 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o270 : xone 270 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a270_0 b270_0 a270_1 b270_1 a270_2 b270_2
    a270_3 b270_3 a270_4 b270_4 a270_5 b270_5

theorem a271_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 271))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 271) 0) = 2956 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b271_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 271)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 271)) 0) = 2956 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a271_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 271))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 271) 305530) = 137590 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b271_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 271)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 271)) 305530) = 137590 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a271_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 271))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 271) 5604) = 235975 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b271_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 271)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 271)) 5604) = 235975 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a271_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 271))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 271) 221549) = 133130 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b271_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 271)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 271)) 221549) = 133130 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a271_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 271))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 271) 266275) = 243820 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b271_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 271)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 271)) 266275) = 243820 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a271_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 271))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 271) 186844) = 279011 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b271_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 271)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 271)) 186844) = 279011 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o271 : xone 271 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a271_0 b271_0 a271_1 b271_1 a271_2 b271_2
    a271_3 b271_3 a271_4 b271_4 a271_5 b271_5

theorem a272_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 272))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 272) 0) = 53770 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b272_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 272)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 272)) 0) = 53770 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a272_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 272))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 272) 305530) = 102219 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b272_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 272)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 272)) 305530) = 102219 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a272_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 272))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 272) 5604) = 73272 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b272_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 272)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 272)) 5604) = 73272 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a272_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 272))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 272) 221549) = 158060 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b272_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 272)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 272)) 221549) = 158060 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a272_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 272))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 272) 266275) = 268822 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b272_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 272)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 272)) 266275) = 268822 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a272_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 272))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 272) 186844) = 27231 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b272_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 272)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 272)) 186844) = 27231 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o272 : xone 272 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a272_0 b272_0 a272_1 b272_1 a272_2 b272_2
    a272_3 b272_3 a272_4 b272_4 a272_5 b272_5

theorem a273_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 273))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 273) 0) = 2495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b273_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 273)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 273)) 0) = 2495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a273_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 273))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 273) 305530) = 223916 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b273_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 273)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 273)) 305530) = 223916 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a273_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 273))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 273) 5604) = 143545 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b273_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 273)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 273)) 5604) = 143545 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a273_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 273))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 273) 221549) = 82833 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b273_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 273)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 273)) 221549) = 82833 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a273_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 273))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 273) 266275) = 101210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b273_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 273)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 273)) 266275) = 101210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a273_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 273))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 273) 186844) = 190110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b273_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 273)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 273)) 186844) = 190110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o273 : xone 273 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a273_0 b273_0 a273_1 b273_1 a273_2 b273_2
    a273_3 b273_3 a273_4 b273_4 a273_5 b273_5

theorem a274_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 274))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 274) 0) = 97679 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b274_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 274)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 274)) 0) = 97679 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a274_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 274))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 274) 305530) = 28392 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b274_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 274)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 274)) 305530) = 28392 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a274_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 274))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 274) 5604) = 122239 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b274_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 274)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 274)) 5604) = 122239 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a274_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 274))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 274) 221549) = 139593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b274_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 274)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 274)) 221549) = 139593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a274_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 274))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 274) 266275) = 197448 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b274_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 274)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 274)) 266275) = 197448 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a274_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 274))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 274) 186844) = 207082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b274_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 274)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 274)) 186844) = 207082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o274 : xone 274 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a274_0 b274_0 a274_1 b274_1 a274_2 b274_2
    a274_3 b274_3 a274_4 b274_4 a274_5 b274_5

theorem a275_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 275))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 275) 0) = 215205 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b275_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 275)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 275)) 0) = 215205 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a275_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 275))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 275) 305530) = 293711 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b275_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 275)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 275)) 305530) = 293711 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a275_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 275))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 275) 5604) = 247908 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b275_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 275)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 275)) 5604) = 247908 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a275_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 275))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 275) 221549) = 303341 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b275_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 275)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 275)) 221549) = 303341 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a275_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 275))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 275) 266275) = 16115 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b275_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 275)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 275)) 266275) = 16115 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a275_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 275))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 275) 186844) = 174609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b275_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 275)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 275)) 186844) = 174609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o275 : xone 275 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a275_0 b275_0 a275_1 b275_1 a275_2 b275_2
    a275_3 b275_3 a275_4 b275_4 a275_5 b275_5

theorem a276_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 276))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 276) 0) = 18424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b276_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 276)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 276)) 0) = 18424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a276_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 276))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 276) 305530) = 208147 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b276_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 276)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 276)) 305530) = 208147 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a276_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 276))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 276) 5604) = 104316 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b276_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 276)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 276)) 5604) = 104316 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a276_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 276))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 276) 221549) = 238 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b276_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 276)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 276)) 221549) = 238 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a276_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 276))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 276) 266275) = 97531 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b276_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 276)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 276)) 266275) = 97531 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a276_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 276))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 276) 186844) = 152185 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b276_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 276)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 276)) 186844) = 152185 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o276 : xone 276 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a276_0 b276_0 a276_1 b276_1 a276_2 b276_2
    a276_3 b276_3 a276_4 b276_4 a276_5 b276_5

theorem a277_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 277))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 277) 0) = 195531 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b277_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 277)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 277)) 0) = 195531 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a277_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 277))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 277) 305530) = 112835 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b277_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 277)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 277)) 305530) = 112835 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a277_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 277))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 277) 5604) = 247804 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b277_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 277)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 277)) 5604) = 247804 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a277_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 277))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 277) 221549) = 29601 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b277_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 277)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 277)) 221549) = 29601 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a277_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 277))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 277) 266275) = 173632 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b277_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 277)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 277)) 266275) = 173632 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a277_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 277))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 277) 186844) = 159539 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b277_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 277)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 277)) 186844) = 159539 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o277 : xone 277 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a277_0 b277_0 a277_1 b277_1 a277_2 b277_2
    a277_3 b277_3 a277_4 b277_4 a277_5 b277_5

theorem a278_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 278))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 278) 0) = 66797 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b278_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 278)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 278)) 0) = 66797 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a278_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 278))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 278) 305530) = 224055 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b278_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 278)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 278)) 305530) = 224055 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a278_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 278))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 278) 5604) = 21621 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b278_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 278)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 278)) 5604) = 21621 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a278_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 278))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 278) 221549) = 40261 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b278_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 278)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 278)) 221549) = 40261 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a278_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 278))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 278) 266275) = 267147 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b278_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 278)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 278)) 266275) = 267147 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a278_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 278))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 278) 186844) = 151985 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b278_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 278)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 278)) 186844) = 151985 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o278 : xone 278 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a278_0 b278_0 a278_1 b278_1 a278_2 b278_2
    a278_3 b278_3 a278_4 b278_4 a278_5 b278_5

theorem a279_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 279))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 279) 0) = 300290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b279_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 279)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 279)) 0) = 300290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a279_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 279))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 279) 305530) = 20199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b279_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 279)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 279)) 305530) = 20199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a279_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 279))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 279) 5604) = 29132 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b279_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 279)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 279)) 5604) = 29132 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a279_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 279))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 279) 221549) = 151085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b279_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 279)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 279)) 221549) = 151085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a279_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 279))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 279) 266275) = 102362 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b279_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 279)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 279)) 266275) = 102362 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a279_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 279))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 279) 186844) = 188836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b279_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 279)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 279)) 186844) = 188836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o279 : xone 279 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a279_0 b279_0 a279_1 b279_1 a279_2 b279_2
    a279_3 b279_3 a279_4 b279_4 a279_5 b279_5

theorem a280_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 280))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 280) 0) = 261749 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b280_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 280)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 280)) 0) = 261749 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a280_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 280))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 280) 305530) = 121216 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b280_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 280)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 280)) 305530) = 121216 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a280_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 280))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 280) 5604) = 33793 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b280_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 280)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 280)) 5604) = 33793 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a280_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 280))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 280) 221549) = 127504 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b280_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 280)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 280)) 221549) = 127504 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a280_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 280))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 280) 266275) = 210954 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b280_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 280)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 280)) 266275) = 210954 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a280_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 280))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 280) 186844) = 110881 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b280_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 280)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 280)) 186844) = 110881 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o280 : xone 280 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a280_0 b280_0 a280_1 b280_1 a280_2 b280_2
    a280_3 b280_3 a280_4 b280_4 a280_5 b280_5

theorem a281_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 281))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 281) 0) = 19110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b281_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 281)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 281)) 0) = 19110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a281_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 281))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 281) 305530) = 291385 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b281_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 281)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 281)) 305530) = 291385 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a281_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 281))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 281) 5604) = 22610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b281_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 281)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 281)) 5604) = 22610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a281_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 281))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 281) 221549) = 52661 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b281_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 281)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 281)) 221549) = 52661 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a281_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 281))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 281) 266275) = 292897 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b281_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 281)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 281)) 266275) = 292897 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a281_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 281))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 281) 186844) = 168728 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b281_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 281)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 281)) 186844) = 168728 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o281 : xone 281 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a281_0 b281_0 a281_1 b281_1 a281_2 b281_2
    a281_3 b281_3 a281_4 b281_4 a281_5 b281_5

theorem a282_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 282))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 282) 0) = 271632 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b282_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 282)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 282)) 0) = 271632 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a282_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 282))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 282) 305530) = 42351 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b282_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 282)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 282)) 305530) = 42351 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a282_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 282))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 282) 5604) = 284780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b282_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 282)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 282)) 5604) = 284780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a282_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 282))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 282) 221549) = 244125 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b282_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 282)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 282)) 221549) = 244125 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a282_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 282))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 282) 266275) = 89496 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b282_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 282)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 282)) 266275) = 89496 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a282_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 282))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 282) 186844) = 107138 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b282_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 282)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 282)) 186844) = 107138 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o282 : xone 282 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a282_0 b282_0 a282_1 b282_1 a282_2 b282_2
    a282_3 b282_3 a282_4 b282_4 a282_5 b282_5

theorem a283_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 283))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 283) 0) = 13102 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b283_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 283)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 283)) 0) = 13102 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a283_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 283))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 283) 305530) = 67241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b283_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 283)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 283)) 305530) = 67241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a283_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 283))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 283) 5604) = 161627 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b283_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 283)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 283)) 5604) = 161627 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a283_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 283))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 283) 221549) = 122198 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b283_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 283)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 283)) 221549) = 122198 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a283_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 283))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 283) 266275) = 129754 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b283_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 283)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 283)) 266275) = 129754 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a283_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 283))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 283) 186844) = 6877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b283_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 283)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 283)) 186844) = 6877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o283 : xone 283 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a283_0 b283_0 a283_1 b283_1 a283_2 b283_2
    a283_3 b283_3 a283_4 b283_4 a283_5 b283_5

theorem a284_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 284))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 284) 0) = 191001 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b284_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 284)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 284)) 0) = 191001 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a284_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 284))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 284) 305530) = 13370 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b284_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 284)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 284)) 305530) = 13370 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a284_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 284))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 284) 5604) = 178671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b284_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 284)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 284)) 5604) = 178671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a284_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 284))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 284) 221549) = 126469 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b284_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 284)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 284)) 221549) = 126469 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a284_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 284))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 284) 266275) = 207238 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b284_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 284)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 284)) 266275) = 207238 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a284_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 284))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 284) 186844) = 298606 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b284_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 284)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 284)) 186844) = 298606 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o284 : xone 284 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a284_0 b284_0 a284_1 b284_1 a284_2 b284_2
    a284_3 b284_3 a284_4 b284_4 a284_5 b284_5

theorem a285_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 285))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 285) 0) = 81623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b285_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 285)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 285)) 0) = 81623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a285_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 285))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 285) 305530) = 252754 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b285_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 285)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 285)) 305530) = 252754 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a285_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 285))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 285) 5604) = 128849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b285_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 285)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 285)) 5604) = 128849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a285_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 285))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 285) 221549) = 166082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b285_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 285)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 285)) 221549) = 166082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a285_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 285))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 285) 266275) = 47525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b285_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 285)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 285)) 266275) = 47525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a285_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 285))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 285) 186844) = 122582 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b285_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 285)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 285)) 186844) = 122582 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o285 : xone 285 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a285_0 b285_0 a285_1 b285_1 a285_2 b285_2
    a285_3 b285_3 a285_4 b285_4 a285_5 b285_5

theorem a286_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 286))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 286) 0) = 568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b286_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 286)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 286)) 0) = 568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a286_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 286))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 286) 305530) = 254979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b286_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 286)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 286)) 305530) = 254979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a286_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 286))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 286) 5604) = 112998 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b286_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 286)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 286)) 5604) = 112998 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a286_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 286))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 286) 221549) = 35308 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b286_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 286)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 286)) 221549) = 35308 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a286_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 286))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 286) 266275) = 112903 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b286_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 286)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 286)) 266275) = 112903 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a286_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 286))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 286) 186844) = 42215 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b286_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 286)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 286)) 186844) = 42215 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o286 : xone 286 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a286_0 b286_0 a286_1 b286_1 a286_2 b286_2
    a286_3 b286_3 a286_4 b286_4 a286_5 b286_5

theorem a287_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 287))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 287) 0) = 251445 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b287_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 287)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 287)) 0) = 251445 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a287_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 287))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 287) 305530) = 209940 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b287_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 287)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 287)) 305530) = 209940 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a287_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 287))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 287) 5604) = 278168 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b287_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 287)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 287)) 5604) = 278168 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a287_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 287))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 287) 221549) = 32134 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b287_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 287)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 287)) 221549) = 32134 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a287_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 287))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 287) 266275) = 217951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b287_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 287)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 287)) 266275) = 217951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a287_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 287))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 287) 186844) = 26374 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b287_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 287)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 287)) 186844) = 26374 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o287 : xone 287 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a287_0 b287_0 a287_1 b287_1 a287_2 b287_2
    a287_3 b287_3 a287_4 b287_4 a287_5 b287_5

theorem a288_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 288))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 288) 0) = 192888 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b288_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 288)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 288)) 0) = 192888 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a288_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 288))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 288) 305530) = 244498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b288_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 288)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 288)) 305530) = 244498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a288_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 288))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 288) 5604) = 83768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b288_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 288)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 288)) 5604) = 83768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a288_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 288))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 288) 221549) = 194029 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b288_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 288)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 288)) 221549) = 194029 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a288_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 288))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 288) 266275) = 282429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b288_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 288)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 288)) 266275) = 282429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a288_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 288))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 288) 186844) = 89654 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b288_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 288)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 288)) 186844) = 89654 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o288 : xone 288 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a288_0 b288_0 a288_1 b288_1 a288_2 b288_2
    a288_3 b288_3 a288_4 b288_4 a288_5 b288_5

theorem a289_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 289))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 289) 0) = 63864 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b289_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 289)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 289)) 0) = 63864 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a289_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 289))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 289) 305530) = 101933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b289_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 289)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 289)) 305530) = 101933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a289_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 289))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 289) 5604) = 130724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b289_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 289)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 289)) 5604) = 130724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a289_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 289))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 289) 221549) = 189505 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b289_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 289)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 289)) 221549) = 189505 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a289_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 289))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 289) 266275) = 227514 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b289_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 289)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 289)) 266275) = 227514 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a289_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 289))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 289) 186844) = 48527 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b289_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 289)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 289)) 186844) = 48527 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o289 : xone 289 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a289_0 b289_0 a289_1 b289_1 a289_2 b289_2
    a289_3 b289_3 a289_4 b289_4 a289_5 b289_5

theorem a290_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 290))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 290) 0) = 22132 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b290_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 290)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 290)) 0) = 22132 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a290_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 290))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 290) 305530) = 82955 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b290_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 290)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 290)) 305530) = 82955 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a290_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 290))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 290) 5604) = 10759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b290_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 290)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 290)) 5604) = 10759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a290_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 290))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 290) 221549) = 178183 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b290_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 290)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 290)) 221549) = 178183 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a290_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 290))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 290) 266275) = 297669 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b290_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 290)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 290)) 266275) = 297669 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a290_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 290))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 290) 186844) = 95644 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b290_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 290)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 290)) 186844) = 95644 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o290 : xone 290 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a290_0 b290_0 a290_1 b290_1 a290_2 b290_2
    a290_3 b290_3 a290_4 b290_4 a290_5 b290_5

theorem a291_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 291))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 291) 0) = 294005 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b291_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 291)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 291)) 0) = 294005 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a291_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 291))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 291) 305530) = 95764 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b291_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 291)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 291)) 305530) = 95764 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a291_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 291))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 291) 5604) = 197828 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b291_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 291)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 291)) 5604) = 197828 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a291_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 291))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 291) 221549) = 293007 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b291_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 291)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 291)) 221549) = 293007 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a291_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 291))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 291) 266275) = 139951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b291_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 291)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 291)) 266275) = 139951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a291_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 291))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 291) 186844) = 146164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b291_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 291)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 291)) 186844) = 146164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o291 : xone 291 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a291_0 b291_0 a291_1 b291_1 a291_2 b291_2
    a291_3 b291_3 a291_4 b291_4 a291_5 b291_5

theorem a292_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 292))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 292) 0) = 144452 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b292_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 292)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 292)) 0) = 144452 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a292_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 292))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 292) 305530) = 262803 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b292_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 292)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 292)) 305530) = 262803 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a292_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 292))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 292) 5604) = 288481 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b292_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 292)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 292)) 5604) = 288481 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a292_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 292))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 292) 221549) = 166358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b292_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 292)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 292)) 221549) = 166358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a292_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 292))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 292) 266275) = 222941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b292_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 292)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 292)) 266275) = 222941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a292_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 292))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 292) 186844) = 270184 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b292_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 292)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 292)) 186844) = 270184 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o292 : xone 292 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a292_0 b292_0 a292_1 b292_1 a292_2 b292_2
    a292_3 b292_3 a292_4 b292_4 a292_5 b292_5

theorem a293_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 293))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 293) 0) = 179612 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b293_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 293)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 293)) 0) = 179612 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a293_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 293))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 293) 305530) = 302105 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b293_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 293)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 293)) 305530) = 302105 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a293_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 293))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 293) 5604) = 294623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b293_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 293)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 293)) 5604) = 294623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a293_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 293))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 293) 221549) = 292945 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b293_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 293)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 293)) 221549) = 292945 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a293_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 293))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 293) 266275) = 304936 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b293_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 293)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 293)) 266275) = 304936 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a293_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 293))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 293) 186844) = 87983 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b293_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 293)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 293)) 186844) = 87983 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o293 : xone 293 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a293_0 b293_0 a293_1 b293_1 a293_2 b293_2
    a293_3 b293_3 a293_4 b293_4 a293_5 b293_5

theorem a294_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 294))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 294) 0) = 238928 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b294_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 294)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 294)) 0) = 238928 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a294_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 294))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 294) 305530) = 67786 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b294_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 294)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 294)) 305530) = 67786 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a294_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 294))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 294) 5604) = 266984 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b294_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 294)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 294)) 5604) = 266984 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a294_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 294))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 294) 221549) = 275876 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b294_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 294)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 294)) 221549) = 275876 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a294_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 294))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 294) 266275) = 85378 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b294_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 294)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 294)) 266275) = 85378 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a294_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 294))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 294) 186844) = 18702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b294_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 294)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 294)) 186844) = 18702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o294 : xone 294 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a294_0 b294_0 a294_1 b294_1 a294_2 b294_2
    a294_3 b294_3 a294_4 b294_4 a294_5 b294_5

theorem a295_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 295))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 295) 0) = 154633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b295_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 295)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 295)) 0) = 154633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a295_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 295))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 295) 305530) = 301596 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b295_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 295)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 295)) 305530) = 301596 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a295_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 295))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 295) 5604) = 185216 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b295_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 295)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 295)) 5604) = 185216 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a295_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 295))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 295) 221549) = 17027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b295_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 295)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 295)) 221549) = 17027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a295_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 295))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 295) 266275) = 201136 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b295_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 295)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 295)) 266275) = 201136 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a295_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 295))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 295) 186844) = 4480 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b295_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 295)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 295)) 186844) = 4480 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o295 : xone 295 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a295_0 b295_0 a295_1 b295_1 a295_2 b295_2
    a295_3 b295_3 a295_4 b295_4 a295_5 b295_5

theorem a296_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 296))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 296) 0) = 123332 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b296_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 296)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 296)) 0) = 123332 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a296_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 296))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 296) 305530) = 20422 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b296_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 296)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 296)) 305530) = 20422 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a296_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 296))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 296) 5604) = 39131 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b296_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 296)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 296)) 5604) = 39131 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a296_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 296))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 296) 221549) = 295924 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b296_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 296)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 296)) 221549) = 295924 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a296_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 296))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 296) 266275) = 32307 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b296_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 296)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 296)) 266275) = 32307 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a296_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 296))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 296) 186844) = 141610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b296_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 296)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 296)) 186844) = 141610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o296 : xone 296 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a296_0 b296_0 a296_1 b296_1 a296_2 b296_2
    a296_3 b296_3 a296_4 b296_4 a296_5 b296_5

theorem a297_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 297))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 297) 0) = 299254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b297_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 297)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 297)) 0) = 299254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a297_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 297))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 297) 305530) = 210537 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b297_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 297)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 297)) 305530) = 210537 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a297_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 297))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 297) 5604) = 275195 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b297_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 297)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 297)) 5604) = 275195 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a297_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 297))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 297) 221549) = 86705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b297_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 297)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 297)) 221549) = 86705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a297_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 297))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 297) 266275) = 166128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b297_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 297)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 297)) 266275) = 166128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a297_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 297))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 297) 186844) = 81995 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b297_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 297)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 297)) 186844) = 81995 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o297 : xone 297 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a297_0 b297_0 a297_1 b297_1 a297_2 b297_2
    a297_3 b297_3 a297_4 b297_4 a297_5 b297_5

theorem a298_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 298))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 298) 0) = 150129 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b298_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 298)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 298)) 0) = 150129 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a298_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 298))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 298) 305530) = 61316 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b298_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 298)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 298)) 305530) = 61316 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a298_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 298))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 298) 5604) = 294754 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b298_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 298)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 298)) 5604) = 294754 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a298_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 298))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 298) 221549) = 17516 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b298_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 298)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 298)) 221549) = 17516 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a298_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 298))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 298) 266275) = 190841 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b298_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 298)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 298)) 266275) = 190841 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a298_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 298))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 298) 186844) = 294090 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b298_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 298)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 298)) 186844) = 294090 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o298 : xone 298 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a298_0 b298_0 a298_1 b298_1 a298_2 b298_2
    a298_3 b298_3 a298_4 b298_4 a298_5 b298_5

theorem a299_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 299))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 299) 0) = 257737 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b299_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 299)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 299)) 0) = 257737 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a299_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 299))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 299) 305530) = 191744 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b299_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 299)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 299)) 305530) = 191744 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a299_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 299))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 299) 5604) = 250324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b299_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 299)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 299)) 5604) = 250324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a299_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 299))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 299) 221549) = 283271 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b299_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 299)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 299)) 221549) = 283271 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a299_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 299))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 299) 266275) = 207149 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b299_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 299)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 299)) 266275) = 207149 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a299_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 299))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 299) 186844) = 304688 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b299_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 299)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 299)) 186844) = 304688 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o299 : xone 299 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a299_0 b299_0 a299_1 b299_1 a299_2 b299_2
    a299_3 b299_3 a299_4 b299_4 a299_5 b299_5

theorem a300_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 300))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 300) 0) = 277456 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b300_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 300)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 300)) 0) = 277456 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a300_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 300))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 300) 305530) = 68423 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b300_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 300)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 300)) 305530) = 68423 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a300_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 300))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 300) 5604) = 3116 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b300_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 300)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 300)) 5604) = 3116 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a300_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 300))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 300) 221549) = 256248 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b300_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 300)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 300)) 221549) = 256248 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a300_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 300))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 300) 266275) = 218450 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b300_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 300)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 300)) 266275) = 218450 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a300_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 300))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 300) 186844) = 35015 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b300_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 300)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 300)) 186844) = 35015 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o300 : xone 300 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a300_0 b300_0 a300_1 b300_1 a300_2 b300_2
    a300_3 b300_3 a300_4 b300_4 a300_5 b300_5

theorem a301_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 301))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 301) 0) = 14791 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b301_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 301)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 301)) 0) = 14791 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a301_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 301))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 301) 305530) = 100154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b301_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 301)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 301)) 305530) = 100154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a301_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 301))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 301) 5604) = 4506 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b301_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 301)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 301)) 5604) = 4506 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a301_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 301))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 301) 221549) = 48772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b301_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 301)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 301)) 221549) = 48772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a301_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 301))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 301) 266275) = 220455 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b301_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 301)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 301)) 266275) = 220455 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a301_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 301))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 301) 186844) = 106407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b301_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 301)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 301)) 186844) = 106407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o301 : xone 301 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a301_0 b301_0 a301_1 b301_1 a301_2 b301_2
    a301_3 b301_3 a301_4 b301_4 a301_5 b301_5

theorem a302_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 302))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 302) 0) = 107938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b302_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 302)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 302)) 0) = 107938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a302_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 302))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 302) 305530) = 133156 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b302_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 302)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 302)) 305530) = 133156 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a302_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 302))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 302) 5604) = 118180 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b302_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 302)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 302)) 5604) = 118180 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a302_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 302))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 302) 221549) = 269969 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b302_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 302)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 302)) 221549) = 269969 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a302_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 302))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 302) 266275) = 260647 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b302_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 302)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 302)) 266275) = 260647 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a302_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 302))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 302) 186844) = 30586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b302_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 302)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 302)) 186844) = 30586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o302 : xone 302 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a302_0 b302_0 a302_1 b302_1 a302_2 b302_2
    a302_3 b302_3 a302_4 b302_4 a302_5 b302_5

theorem a303_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 303))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 303) 0) = 97186 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b303_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 303)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 303)) 0) = 97186 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a303_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 303))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 303) 305530) = 18281 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b303_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 303)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 303)) 305530) = 18281 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a303_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 303))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 303) 5604) = 266281 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b303_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 303)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 303)) 5604) = 266281 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a303_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 303))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 303) 221549) = 202260 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b303_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 303)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 303)) 221549) = 202260 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a303_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 303))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 303) 266275) = 122100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b303_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 303)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 303)) 266275) = 122100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a303_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 303))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 303) 186844) = 7098 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b303_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 303)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 303)) 186844) = 7098 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o303 : xone 303 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a303_0 b303_0 a303_1 b303_1 a303_2 b303_2
    a303_3 b303_3 a303_4 b303_4 a303_5 b303_5

theorem a304_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 304))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 304) 0) = 128313 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b304_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 304)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 304)) 0) = 128313 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a304_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 304))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 304) 305530) = 130025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b304_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 304)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 304)) 305530) = 130025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a304_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 304))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 304) 5604) = 57065 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b304_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 304)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 304)) 5604) = 57065 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a304_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 304))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 304) 221549) = 206159 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b304_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 304)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 304)) 221549) = 206159 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a304_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 304))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 304) 266275) = 83455 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b304_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 304)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 304)) 266275) = 83455 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a304_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 304))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 304) 186844) = 187842 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b304_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 304)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 304)) 186844) = 187842 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o304 : xone 304 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a304_0 b304_0 a304_1 b304_1 a304_2 b304_2
    a304_3 b304_3 a304_4 b304_4 a304_5 b304_5

theorem a305_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 305))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 305) 0) = 125139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b305_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 305)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 305)) 0) = 125139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a305_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 305))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 305) 305530) = 209703 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b305_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 305)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 305)) 305530) = 209703 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a305_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 305))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 305) 5604) = 293224 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b305_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 305)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 305)) 5604) = 293224 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a305_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 305))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 305) 221549) = 93362 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b305_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 305)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 305)) 221549) = 93362 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a305_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 305))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 305) 266275) = 272256 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b305_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 305)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 305)) 266275) = 272256 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a305_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 305))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 305) 186844) = 277264 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b305_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 305)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 305)) 186844) = 277264 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o305 : xone 305 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a305_0 b305_0 a305_1 b305_1 a305_2 b305_2
    a305_3 b305_3 a305_4 b305_4 a305_5 b305_5

theorem a306_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 306))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 306) 0) = 38488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b306_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 306)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 306)) 0) = 38488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a306_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 306))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 306) 305530) = 151731 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b306_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 306)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 306)) 305530) = 151731 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a306_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 306))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 306) 5604) = 264251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b306_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 306)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 306)) 5604) = 264251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a306_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 306))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 306) 221549) = 94201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b306_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 306)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 306)) 221549) = 94201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a306_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 306))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 306) 266275) = 298237 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b306_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 306)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 306)) 266275) = 298237 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a306_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 306))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 306) 186844) = 116288 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b306_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 306)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 306)) 186844) = 116288 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o306 : xone 306 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a306_0 b306_0 a306_1 b306_1 a306_2 b306_2
    a306_3 b306_3 a306_4 b306_4 a306_5 b306_5

theorem a307_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 307))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 307) 0) = 199104 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b307_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 307)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 307)) 0) = 199104 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a307_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 307))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 307) 305530) = 197813 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b307_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 307)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 307)) 305530) = 197813 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a307_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 307))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 307) 5604) = 259319 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b307_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 307)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 307)) 5604) = 259319 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a307_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 307))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 307) 221549) = 28663 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b307_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 307)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 307)) 221549) = 28663 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a307_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 307))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 307) 266275) = 233570 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b307_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 307)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 307)) 266275) = 233570 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a307_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 307))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 307) 186844) = 264062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b307_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 307)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 307)) 186844) = 264062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o307 : xone 307 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a307_0 b307_0 a307_1 b307_1 a307_2 b307_2
    a307_3 b307_3 a307_4 b307_4 a307_5 b307_5

theorem a308_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 308))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 308) 0) = 228686 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b308_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 308)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 308)) 0) = 228686 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a308_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 308))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 308) 305530) = 108066 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b308_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 308)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 308)) 305530) = 108066 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a308_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 308))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 308) 5604) = 176256 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b308_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 308)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 308)) 5604) = 176256 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a308_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 308))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 308) 221549) = 286901 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b308_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 308)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 308)) 221549) = 286901 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a308_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 308))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 308) 266275) = 232823 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b308_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 308)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 308)) 266275) = 232823 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a308_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 308))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 308) 186844) = 46468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b308_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 308)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 308)) 186844) = 46468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o308 : xone 308 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a308_0 b308_0 a308_1 b308_1 a308_2 b308_2
    a308_3 b308_3 a308_4 b308_4 a308_5 b308_5

theorem a309_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 309))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 309) 0) = 188235 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b309_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 309)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 309)) 0) = 188235 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a309_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 309))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 309) 305530) = 155924 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b309_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 309)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 309)) 305530) = 155924 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a309_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 309))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 309) 5604) = 24264 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b309_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 309)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 309)) 5604) = 24264 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a309_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 309))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 309) 221549) = 276074 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b309_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 309)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 309)) 221549) = 276074 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a309_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 309))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 309) 266275) = 295143 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b309_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 309)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 309)) 266275) = 295143 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a309_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 309))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 309) 186844) = 280494 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b309_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 309)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 309)) 186844) = 280494 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o309 : xone 309 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a309_0 b309_0 a309_1 b309_1 a309_2 b309_2
    a309_3 b309_3 a309_4 b309_4 a309_5 b309_5

theorem a310_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 310))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 310) 0) = 161616 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b310_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 310)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 310)) 0) = 161616 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a310_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 310))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 310) 305530) = 131023 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b310_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 310)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 310)) 305530) = 131023 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a310_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 310))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 310) 5604) = 182606 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b310_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 310)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 310)) 5604) = 182606 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a310_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 310))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 310) 221549) = 298417 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b310_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 310)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 310)) 221549) = 298417 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a310_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 310))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 310) 266275) = 128593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b310_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 310)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 310)) 266275) = 128593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a310_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 310))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 310) 186844) = 223481 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b310_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 310)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 310)) 186844) = 223481 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o310 : xone 310 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a310_0 b310_0 a310_1 b310_1 a310_2 b310_2
    a310_3 b310_3 a310_4 b310_4 a310_5 b310_5

theorem a311_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 311))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 311) 0) = 77165 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b311_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 311)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 311)) 0) = 77165 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a311_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 311))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 311) 305530) = 131455 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b311_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 311)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 311)) 305530) = 131455 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a311_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 311))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 311) 5604) = 275830 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b311_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 311)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 311)) 5604) = 275830 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a311_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 311))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 311) 221549) = 132151 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b311_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 311)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 311)) 221549) = 132151 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a311_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 311))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 311) 266275) = 263559 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b311_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 311)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 311)) 266275) = 263559 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a311_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 311))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 311) 186844) = 64437 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b311_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 311)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 311)) 186844) = 64437 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o311 : xone 311 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a311_0 b311_0 a311_1 b311_1 a311_2 b311_2
    a311_3 b311_3 a311_4 b311_4 a311_5 b311_5

theorem a312_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 312))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 312) 0) = 93802 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b312_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 312)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 312)) 0) = 93802 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a312_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 312))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 312) 305530) = 59698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b312_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 312)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 312)) 305530) = 59698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a312_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 312))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 312) 5604) = 249867 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b312_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 312)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 312)) 5604) = 249867 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a312_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 312))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 312) 221549) = 215350 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b312_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 312)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 312)) 221549) = 215350 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a312_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 312))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 312) 266275) = 219813 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b312_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 312)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 312)) 266275) = 219813 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a312_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 312))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 312) 186844) = 241379 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b312_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 312)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 312)) 186844) = 241379 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o312 : xone 312 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a312_0 b312_0 a312_1 b312_1 a312_2 b312_2
    a312_3 b312_3 a312_4 b312_4 a312_5 b312_5

theorem a313_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 313))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 313) 0) = 64603 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b313_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 313)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 313)) 0) = 64603 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a313_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 313))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 313) 305530) = 181384 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b313_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 313)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 313)) 305530) = 181384 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a313_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 313))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 313) 5604) = 29351 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b313_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 313)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 313)) 5604) = 29351 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a313_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 313))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 313) 221549) = 109375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b313_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 313)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 313)) 221549) = 109375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a313_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 313))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 313) 266275) = 259110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b313_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 313)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 313)) 266275) = 259110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a313_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 313))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 313) 186844) = 116769 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b313_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 313)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 313)) 186844) = 116769 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o313 : xone 313 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a313_0 b313_0 a313_1 b313_1 a313_2 b313_2
    a313_3 b313_3 a313_4 b313_4 a313_5 b313_5

theorem a314_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 314))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 314) 0) = 25987 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b314_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 314)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 314)) 0) = 25987 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a314_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 314))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 314) 305530) = 146835 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b314_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 314)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 314)) 305530) = 146835 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a314_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 314))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 314) 5604) = 12696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b314_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 314)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 314)) 5604) = 12696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a314_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 314))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 314) 221549) = 151072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b314_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 314)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 314)) 221549) = 151072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a314_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 314))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 314) 266275) = 194385 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b314_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 314)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 314)) 266275) = 194385 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a314_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 314))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 314) 186844) = 281988 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b314_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 314)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 314)) 186844) = 281988 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o314 : xone 314 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a314_0 b314_0 a314_1 b314_1 a314_2 b314_2
    a314_3 b314_3 a314_4 b314_4 a314_5 b314_5

theorem a315_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 315))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 315) 0) = 240229 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b315_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 315)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 315)) 0) = 240229 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a315_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 315))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 315) 305530) = 199806 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b315_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 315)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 315)) 305530) = 199806 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a315_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 315))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 315) 5604) = 90635 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b315_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 315)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 315)) 5604) = 90635 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a315_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 315))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 315) 221549) = 273933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b315_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 315)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 315)) 221549) = 273933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a315_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 315))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 315) 266275) = 275169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b315_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 315)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 315)) 266275) = 275169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a315_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 315))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 315) 186844) = 220273 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b315_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 315)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 315)) 186844) = 220273 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o315 : xone 315 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a315_0 b315_0 a315_1 b315_1 a315_2 b315_2
    a315_3 b315_3 a315_4 b315_4 a315_5 b315_5

theorem a316_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 316))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 316) 0) = 783 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b316_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 316)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 316)) 0) = 783 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a316_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 316))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 316) 305530) = 23823 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b316_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 316)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 316)) 305530) = 23823 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a316_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 316))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 316) 5604) = 161123 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b316_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 316)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 316)) 5604) = 161123 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a316_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 316))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 316) 221549) = 228886 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b316_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 316)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 316)) 221549) = 228886 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a316_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 316))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 316) 266275) = 291036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b316_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 316)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 316)) 266275) = 291036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a316_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 316))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 316) 186844) = 38514 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b316_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 316)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 316)) 186844) = 38514 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o316 : xone 316 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a316_0 b316_0 a316_1 b316_1 a316_2 b316_2
    a316_3 b316_3 a316_4 b316_4 a316_5 b316_5

theorem a317_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 317))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 317) 0) = 222865 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b317_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 317)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 317)) 0) = 222865 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a317_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 317))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 317) 305530) = 233247 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b317_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 317)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 317)) 305530) = 233247 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a317_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 317))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 317) 5604) = 124873 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b317_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 317)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 317)) 5604) = 124873 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a317_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 317))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 317) 221549) = 211942 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b317_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 317)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 317)) 221549) = 211942 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a317_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 317))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 317) 266275) = 90187 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b317_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 317)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 317)) 266275) = 90187 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a317_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 317))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 317) 186844) = 214096 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b317_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 317)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 317)) 186844) = 214096 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o317 : xone 317 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a317_0 b317_0 a317_1 b317_1 a317_2 b317_2
    a317_3 b317_3 a317_4 b317_4 a317_5 b317_5

theorem a318_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 318))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 318) 0) = 260174 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b318_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 318)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 318)) 0) = 260174 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a318_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 318))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 318) 305530) = 205639 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b318_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 318)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 318)) 305530) = 205639 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a318_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 318))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 318) 5604) = 31987 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b318_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 318)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 318)) 5604) = 31987 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a318_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 318))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 318) 221549) = 133836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b318_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 318)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 318)) 221549) = 133836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a318_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 318))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 318) 266275) = 172555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b318_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 318)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 318)) 266275) = 172555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a318_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 318))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 318) 186844) = 147690 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b318_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 318)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 318)) 186844) = 147690 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o318 : xone 318 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a318_0 b318_0 a318_1 b318_1 a318_2 b318_2
    a318_3 b318_3 a318_4 b318_4 a318_5 b318_5

theorem a319_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 319))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 319) 0) = 302695 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b319_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 319)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 319)) 0) = 302695 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a319_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 319))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 319) 305530) = 263372 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b319_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 319)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 319)) 305530) = 263372 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a319_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 319))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 319) 5604) = 254025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b319_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 319)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 319)) 5604) = 254025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a319_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 319))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 319) 221549) = 83581 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b319_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 319)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 319)) 221549) = 83581 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a319_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 319))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 319) 266275) = 226734 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b319_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 319)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 319)) 266275) = 226734 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a319_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 319))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 319) 186844) = 177734 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b319_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 319)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 319)) 186844) = 177734 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o319 : xone 319 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a319_0 b319_0 a319_1 b319_1 a319_2 b319_2
    a319_3 b319_3 a319_4 b319_4 a319_5 b319_5

theorem a320_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 320))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 320) 0) = 174655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b320_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 320)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 320)) 0) = 174655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a320_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 320))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 320) 305530) = 79332 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b320_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 320)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 320)) 305530) = 79332 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a320_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 320))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 320) 5604) = 117038 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b320_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 320)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 320)) 5604) = 117038 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a320_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 320))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 320) 221549) = 88412 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b320_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 320)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 320)) 221549) = 88412 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a320_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 320))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 320) 266275) = 49691 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b320_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 320)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 320)) 266275) = 49691 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a320_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 320))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 320) 186844) = 264979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b320_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 320)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 320)) 186844) = 264979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o320 : xone 320 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a320_0 b320_0 a320_1 b320_1 a320_2 b320_2
    a320_3 b320_3 a320_4 b320_4 a320_5 b320_5

theorem a321_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 321))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 321) 0) = 260400 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b321_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 321)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 321)) 0) = 260400 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a321_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 321))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 321) 305530) = 202073 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b321_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 321)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 321)) 305530) = 202073 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a321_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 321))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 321) 5604) = 160082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b321_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 321)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 321)) 5604) = 160082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a321_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 321))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 321) 221549) = 171250 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b321_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 321)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 321)) 221549) = 171250 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a321_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 321))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 321) 266275) = 49789 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b321_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 321)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 321)) 266275) = 49789 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a321_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 321))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 321) 186844) = 57642 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b321_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 321)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 321)) 186844) = 57642 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o321 : xone 321 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a321_0 b321_0 a321_1 b321_1 a321_2 b321_2
    a321_3 b321_3 a321_4 b321_4 a321_5 b321_5

theorem a322_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 322))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 322) 0) = 284960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b322_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 322)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 322)) 0) = 284960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a322_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 322))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 322) 305530) = 4852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b322_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 322)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 322)) 305530) = 4852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a322_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 322))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 322) 5604) = 39567 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b322_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 322)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 322)) 5604) = 39567 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a322_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 322))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 322) 221549) = 296207 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b322_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 322)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 322)) 221549) = 296207 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a322_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 322))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 322) 266275) = 34062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b322_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 322)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 322)) 266275) = 34062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a322_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 322))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 322) 186844) = 137250 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b322_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 322)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 322)) 186844) = 137250 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o322 : xone 322 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a322_0 b322_0 a322_1 b322_1 a322_2 b322_2
    a322_3 b322_3 a322_4 b322_4 a322_5 b322_5

theorem a323_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 323))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 323) 0) = 227039 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b323_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 323)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 323)) 0) = 227039 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a323_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 323))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 323) 305530) = 221422 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b323_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 323)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 323)) 305530) = 221422 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a323_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 323))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 323) 5604) = 183915 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b323_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 323)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 323)) 5604) = 183915 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a323_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 323))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 323) 221549) = 1591 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b323_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 323)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 323)) 221549) = 1591 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a323_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 323))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 323) 266275) = 31836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b323_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 323)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 323)) 266275) = 31836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a323_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 323))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 323) 186844) = 304115 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b323_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 323)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 323)) 186844) = 304115 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o323 : xone 323 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a323_0 b323_0 a323_1 b323_1 a323_2 b323_2
    a323_3 b323_3 a323_4 b323_4 a323_5 b323_5

theorem a324_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 324))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 324) 0) = 206494 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b324_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 324)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 324)) 0) = 206494 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a324_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 324))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 324) 305530) = 150767 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b324_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 324)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 324)) 305530) = 150767 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a324_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 324))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 324) 5604) = 245873 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b324_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 324)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 324)) 5604) = 245873 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a324_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 324))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 324) 221549) = 288464 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b324_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 324)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 324)) 221549) = 288464 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a324_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 324))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 324) 266275) = 299233 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b324_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 324)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 324)) 266275) = 299233 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a324_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 324))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 324) 186844) = 220587 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b324_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 324)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 324)) 186844) = 220587 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o324 : xone 324 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a324_0 b324_0 a324_1 b324_1 a324_2 b324_2
    a324_3 b324_3 a324_4 b324_4 a324_5 b324_5

theorem a325_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 325))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 325) 0) = 157215 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b325_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 325)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 325)) 0) = 157215 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a325_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 325))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 325) 305530) = 180979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b325_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 325)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 325)) 305530) = 180979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a325_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 325))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 325) 5604) = 237718 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b325_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 325)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 325)) 5604) = 237718 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a325_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 325))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 325) 221549) = 69696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b325_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 325)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 325)) 221549) = 69696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a325_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 325))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 325) 266275) = 133001 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b325_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 325)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 325)) 266275) = 133001 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a325_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 325))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 325) 186844) = 17 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b325_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 325)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 325)) 186844) = 17 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o325 : xone 325 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a325_0 b325_0 a325_1 b325_1 a325_2 b325_2
    a325_3 b325_3 a325_4 b325_4 a325_5 b325_5

theorem a326_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 326))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 326) 0) = 157182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b326_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 326)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 326)) 0) = 157182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a326_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 326))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 326) 305530) = 124702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b326_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 326)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 326)) 305530) = 124702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a326_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 326))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 326) 5604) = 81053 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b326_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 326)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 326)) 5604) = 81053 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a326_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 326))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 326) 221549) = 5217 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b326_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 326)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 326)) 221549) = 5217 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a326_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 326))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 326) 266275) = 134433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b326_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 326)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 326)) 266275) = 134433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a326_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 326))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 326) 186844) = 285913 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b326_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 326)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 326)) 186844) = 285913 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o326 : xone 326 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a326_0 b326_0 a326_1 b326_1 a326_2 b326_2
    a326_3 b326_3 a326_4 b326_4 a326_5 b326_5

theorem a327_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 327))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 327) 0) = 117059 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b327_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 327)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 327)) 0) = 117059 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a327_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 327))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 327) 305530) = 89624 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b327_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 327)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 327)) 305530) = 89624 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a327_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 327))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 327) 5604) = 186230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b327_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 327)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 327)) 5604) = 186230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a327_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 327))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 327) 221549) = 276745 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b327_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 327)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 327)) 221549) = 276745 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a327_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 327))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 327) 266275) = 303907 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b327_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 327)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 327)) 266275) = 303907 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a327_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 327))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 327) 186844) = 215437 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b327_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 327)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 327)) 186844) = 215437 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o327 : xone 327 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a327_0 b327_0 a327_1 b327_1 a327_2 b327_2
    a327_3 b327_3 a327_4 b327_4 a327_5 b327_5

theorem a328_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 328))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 328) 0) = 255286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b328_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 328)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 328)) 0) = 255286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a328_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 328))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 328) 305530) = 208191 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b328_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 328)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 328)) 305530) = 208191 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a328_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 328))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 328) 5604) = 228622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b328_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 328)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 328)) 5604) = 228622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a328_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 328))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 328) 221549) = 13608 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b328_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 328)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 328)) 221549) = 13608 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a328_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 328))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 328) 266275) = 51016 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b328_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 328)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 328)) 266275) = 51016 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a328_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 328))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 328) 186844) = 42215 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b328_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 328)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 328)) 186844) = 42215 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o328 : xone 328 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a328_0 b328_0 a328_1 b328_1 a328_2 b328_2
    a328_3 b328_3 a328_4 b328_4 a328_5 b328_5

theorem a329_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 329))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 329) 0) = 31997 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b329_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 329)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 329)) 0) = 31997 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a329_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 329))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 329) 305530) = 39145 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b329_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 329)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 329)) 305530) = 39145 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a329_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 329))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 329) 5604) = 105577 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b329_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 329)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 329)) 5604) = 105577 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a329_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 329))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 329) 221549) = 133582 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b329_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 329)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 329)) 221549) = 133582 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a329_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 329))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 329) 266275) = 170753 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b329_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 329)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 329)) 266275) = 170753 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a329_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 329))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 329) 186844) = 193850 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b329_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 329)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 329)) 186844) = 193850 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o329 : xone 329 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a329_0 b329_0 a329_1 b329_1 a329_2 b329_2
    a329_3 b329_3 a329_4 b329_4 a329_5 b329_5

theorem a330_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 330))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 330) 0) = 251393 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b330_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 330)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 330)) 0) = 251393 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a330_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 330))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 330) 305530) = 191707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b330_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 330)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 330)) 305530) = 191707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a330_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 330))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 330) 5604) = 90345 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b330_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 330)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 330)) 5604) = 90345 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a330_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 330))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 330) 221549) = 130856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b330_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 330)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 330)) 221549) = 130856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a330_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 330))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 330) 266275) = 213560 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b330_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 330)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 330)) 266275) = 213560 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a330_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 330))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 330) 186844) = 209138 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b330_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 330)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 330)) 186844) = 209138 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o330 : xone 330 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a330_0 b330_0 a330_1 b330_1 a330_2 b330_2
    a330_3 b330_3 a330_4 b330_4 a330_5 b330_5

theorem a331_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 331))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 331) 0) = 137865 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b331_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 331)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 331)) 0) = 137865 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a331_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 331))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 331) 305530) = 128800 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b331_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 331)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 331)) 305530) = 128800 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a331_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 331))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 331) 5604) = 114124 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b331_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 331)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 331)) 5604) = 114124 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a331_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 331))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 331) 221549) = 204650 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b331_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 331)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 331)) 221549) = 204650 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a331_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 331))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 331) 266275) = 35722 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b331_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 331)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 331)) 266275) = 35722 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a331_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 331))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 331) 186844) = 74174 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b331_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 331)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 331)) 186844) = 74174 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o331 : xone 331 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a331_0 b331_0 a331_1 b331_1 a331_2 b331_2
    a331_3 b331_3 a331_4 b331_4 a331_5 b331_5

theorem a332_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 332))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 332) 0) = 74862 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b332_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 332)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 332)) 0) = 74862 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a332_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 332))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 332) 305530) = 26067 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b332_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 332)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 332)) 305530) = 26067 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a332_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 332))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 332) 5604) = 50659 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b332_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 332)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 332)) 5604) = 50659 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a332_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 332))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 332) 221549) = 68072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b332_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 332)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 332)) 221549) = 68072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a332_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 332))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 332) 266275) = 181810 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b332_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 332)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 332)) 266275) = 181810 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a332_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 332))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 332) 186844) = 39973 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b332_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 332)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 332)) 186844) = 39973 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o332 : xone 332 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a332_0 b332_0 a332_1 b332_1 a332_2 b332_2
    a332_3 b332_3 a332_4 b332_4 a332_5 b332_5

theorem a333_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 333))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 333) 0) = 101293 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b333_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 333)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 333)) 0) = 101293 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a333_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 333))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 333) 305530) = 174413 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b333_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 333)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 333)) 305530) = 174413 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a333_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 333))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 333) 5604) = 203587 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b333_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 333)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 333)) 5604) = 203587 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a333_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 333))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 333) 221549) = 191525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b333_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 333)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 333)) 221549) = 191525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a333_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 333))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 333) 266275) = 147235 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b333_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 333)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 333)) 266275) = 147235 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a333_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 333))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 333) 186844) = 43026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b333_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 333)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 333)) 186844) = 43026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o333 : xone 333 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a333_0 b333_0 a333_1 b333_1 a333_2 b333_2
    a333_3 b333_3 a333_4 b333_4 a333_5 b333_5

theorem a334_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 334))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 334) 0) = 21050 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b334_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 334)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 334)) 0) = 21050 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a334_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 334))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 334) 305530) = 133729 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b334_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 334)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 334)) 305530) = 133729 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a334_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 334))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 334) 5604) = 65287 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b334_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 334)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 334)) 5604) = 65287 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a334_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 334))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 334) 221549) = 17600 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b334_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 334)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 334)) 221549) = 17600 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a334_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 334))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 334) 266275) = 189361 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b334_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 334)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 334)) 266275) = 189361 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a334_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 334))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 334) 186844) = 14792 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b334_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 334)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 334)) 186844) = 14792 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o334 : xone 334 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a334_0 b334_0 a334_1 b334_1 a334_2 b334_2
    a334_3 b334_3 a334_4 b334_4 a334_5 b334_5

theorem a335_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 335))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 335) 0) = 148461 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b335_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 335)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 335)) 0) = 148461 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a335_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 335))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 335) 305530) = 268044 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b335_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 335)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 335)) 305530) = 268044 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a335_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 335))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 335) 5604) = 55600 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b335_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 335)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 335)) 5604) = 55600 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a335_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 335))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 335) 221549) = 147771 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b335_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 335)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 335)) 221549) = 147771 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a335_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 335))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 335) 266275) = 279067 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b335_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 335)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 335)) 266275) = 279067 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a335_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 335))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 335) 186844) = 99134 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b335_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 335)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 335)) 186844) = 99134 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o335 : xone 335 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a335_0 b335_0 a335_1 b335_1 a335_2 b335_2
    a335_3 b335_3 a335_4 b335_4 a335_5 b335_5

theorem a336_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 336))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 336) 0) = 45801 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b336_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 336)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 336)) 0) = 45801 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a336_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 336))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 336) 305530) = 197800 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b336_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 336)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 336)) 305530) = 197800 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a336_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 336))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 336) 5604) = 75686 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b336_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 336)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 336)) 5604) = 75686 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a336_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 336))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 336) 221549) = 213004 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b336_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 336)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 336)) 221549) = 213004 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a336_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 336))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 336) 266275) = 217401 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b336_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 336)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 336)) 266275) = 217401 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a336_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 336))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 336) 186844) = 197559 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b336_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 336)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 336)) 186844) = 197559 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o336 : xone 336 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a336_0 b336_0 a336_1 b336_1 a336_2 b336_2
    a336_3 b336_3 a336_4 b336_4 a336_5 b336_5

theorem a337_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 337))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 337) 0) = 51667 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b337_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 337)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 337)) 0) = 51667 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a337_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 337))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 337) 305530) = 267781 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b337_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 337)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 337)) 305530) = 267781 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a337_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 337))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 337) 5604) = 288552 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b337_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 337)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 337)) 5604) = 288552 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a337_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 337))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 337) 221549) = 200627 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b337_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 337)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 337)) 221549) = 200627 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a337_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 337))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 337) 266275) = 264582 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b337_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 337)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 337)) 266275) = 264582 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a337_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 337))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 337) 186844) = 302251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b337_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 337)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 337)) 186844) = 302251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o337 : xone 337 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a337_0 b337_0 a337_1 b337_1 a337_2 b337_2
    a337_3 b337_3 a337_4 b337_4 a337_5 b337_5

theorem a338_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 338))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 338) 0) = 185011 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b338_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 338)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 338)) 0) = 185011 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a338_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 338))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 338) 305530) = 14592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b338_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 338)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 338)) 305530) = 14592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a338_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 338))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 338) 5604) = 225952 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b338_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 338)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 338)) 5604) = 225952 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a338_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 338))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 338) 221549) = 106946 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b338_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 338)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 338)) 221549) = 106946 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a338_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 338))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 338) 266275) = 29196 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b338_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 338)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 338)) 266275) = 29196 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a338_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 338))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 338) 186844) = 113002 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b338_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 338)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 338)) 186844) = 113002 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o338 : xone 338 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a338_0 b338_0 a338_1 b338_1 a338_2 b338_2
    a338_3 b338_3 a338_4 b338_4 a338_5 b338_5

theorem a339_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 339))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 339) 0) = 49468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b339_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 339)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 339)) 0) = 49468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a339_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 339))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 339) 305530) = 240891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b339_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 339)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 339)) 305530) = 240891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a339_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 339))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 339) 5604) = 86282 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b339_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 339)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 339)) 5604) = 86282 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a339_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 339))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 339) 221549) = 251328 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b339_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 339)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 339)) 221549) = 251328 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a339_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 339))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 339) 266275) = 249723 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b339_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 339)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 339)) 266275) = 249723 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a339_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 339))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 339) 186844) = 146655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b339_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 339)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 339)) 186844) = 146655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o339 : xone 339 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a339_0 b339_0 a339_1 b339_1 a339_2 b339_2
    a339_3 b339_3 a339_4 b339_4 a339_5 b339_5

theorem a340_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 340))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 340) 0) = 255736 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b340_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 340)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 340)) 0) = 255736 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a340_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 340))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 340) 305530) = 296486 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b340_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 340)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 340)) 305530) = 296486 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a340_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 340))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 340) 5604) = 14699 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b340_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 340)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 340)) 5604) = 14699 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a340_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 340))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 340) 221549) = 178150 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b340_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 340)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 340)) 221549) = 178150 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a340_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 340))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 340) 266275) = 55935 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b340_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 340)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 340)) 266275) = 55935 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a340_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 340))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 340) 186844) = 165696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b340_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 340)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 340)) 186844) = 165696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o340 : xone 340 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a340_0 b340_0 a340_1 b340_1 a340_2 b340_2
    a340_3 b340_3 a340_4 b340_4 a340_5 b340_5

theorem a341_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 341))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 341) 0) = 89095 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b341_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 341)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 341)) 0) = 89095 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a341_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 341))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 341) 305530) = 120917 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b341_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 341)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 341)) 305530) = 120917 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a341_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 341))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 341) 5604) = 62042 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b341_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 341)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 341)) 5604) = 62042 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a341_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 341))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 341) 221549) = 305741 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b341_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 341)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 341)) 221549) = 305741 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a341_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 341))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 341) 266275) = 270015 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b341_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 341)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 341)) 266275) = 270015 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a341_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 341))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 341) 186844) = 78674 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b341_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 341)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 341)) 186844) = 78674 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o341 : xone 341 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a341_0 b341_0 a341_1 b341_1 a341_2 b341_2
    a341_3 b341_3 a341_4 b341_4 a341_5 b341_5

theorem a342_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 342))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 342) 0) = 201763 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b342_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 342)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 342)) 0) = 201763 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a342_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 342))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 342) 305530) = 268540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b342_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 342)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 342)) 305530) = 268540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a342_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 342))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 342) 5604) = 137206 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b342_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 342)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 342)) 5604) = 137206 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a342_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 342))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 342) 221549) = 278687 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b342_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 342)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 342)) 221549) = 278687 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a342_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 342))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 342) 266275) = 53478 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b342_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 342)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 342)) 266275) = 53478 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a342_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 342))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 342) 186844) = 35257 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b342_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 342)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 342)) 186844) = 35257 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o342 : xone 342 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a342_0 b342_0 a342_1 b342_1 a342_2 b342_2
    a342_3 b342_3 a342_4 b342_4 a342_5 b342_5

theorem a343_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 343))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 343) 0) = 25556 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b343_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 343)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 343)) 0) = 25556 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a343_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 343))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 343) 305530) = 251742 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b343_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 343)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 343)) 305530) = 251742 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a343_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 343))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 343) 5604) = 206740 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b343_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 343)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 343)) 5604) = 206740 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a343_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 343))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 343) 221549) = 243080 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b343_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 343)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 343)) 221549) = 243080 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a343_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 343))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 343) 266275) = 15847 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b343_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 343)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 343)) 266275) = 15847 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a343_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 343))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 343) 186844) = 119525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b343_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 343)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 343)) 186844) = 119525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o343 : xone 343 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a343_0 b343_0 a343_1 b343_1 a343_2 b343_2
    a343_3 b343_3 a343_4 b343_4 a343_5 b343_5

theorem a344_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 344))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 344) 0) = 231548 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b344_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 344)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 344)) 0) = 231548 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a344_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 344))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 344) 305530) = 267455 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b344_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 344)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 344)) 305530) = 267455 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a344_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 344))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 344) 5604) = 217659 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b344_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 344)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 344)) 5604) = 217659 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a344_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 344))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 344) 221549) = 62352 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b344_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 344)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 344)) 221549) = 62352 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a344_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 344))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 344) 266275) = 247264 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b344_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 344)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 344)) 266275) = 247264 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a344_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 344))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 344) 186844) = 172826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b344_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 344)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 344)) 186844) = 172826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o344 : xone 344 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a344_0 b344_0 a344_1 b344_1 a344_2 b344_2
    a344_3 b344_3 a344_4 b344_4 a344_5 b344_5

theorem a345_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 345))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 345) 0) = 60575 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b345_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 345)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 345)) 0) = 60575 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a345_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 345))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 345) 305530) = 146329 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b345_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 345)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 345)) 305530) = 146329 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a345_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 345))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 345) 5604) = 40310 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b345_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 345)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 345)) 5604) = 40310 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a345_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 345))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 345) 221549) = 60073 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b345_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 345)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 345)) 221549) = 60073 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a345_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 345))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 345) 266275) = 163938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b345_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 345)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 345)) 266275) = 163938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a345_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 345))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 345) 186844) = 255265 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b345_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 345)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 345)) 186844) = 255265 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o345 : xone 345 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a345_0 b345_0 a345_1 b345_1 a345_2 b345_2
    a345_3 b345_3 a345_4 b345_4 a345_5 b345_5

theorem a346_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 346))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 346) 0) = 4367 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b346_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 346)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 346)) 0) = 4367 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a346_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 346))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 346) 305530) = 243800 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b346_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 346)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 346)) 305530) = 243800 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a346_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 346))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 346) 5604) = 281400 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b346_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 346)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 346)) 5604) = 281400 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a346_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 346))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 346) 221549) = 161182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b346_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 346)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 346)) 221549) = 161182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a346_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 346))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 346) 266275) = 120647 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b346_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 346)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 346)) 266275) = 120647 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a346_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 346))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 346) 186844) = 276272 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b346_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 346)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 346)) 186844) = 276272 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o346 : xone 346 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a346_0 b346_0 a346_1 b346_1 a346_2 b346_2
    a346_3 b346_3 a346_4 b346_4 a346_5 b346_5

theorem a347_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 347))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 347) 0) = 122960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b347_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 347)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 347)) 0) = 122960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a347_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 347))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 347) 305530) = 192607 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b347_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 347)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 347)) 305530) = 192607 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a347_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 347))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 347) 5604) = 87938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b347_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 347)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 347)) 5604) = 87938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a347_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 347))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 347) 221549) = 106757 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b347_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 347)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 347)) 221549) = 106757 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a347_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 347))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 347) 266275) = 266284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b347_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 347)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 347)) 266275) = 266284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a347_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 347))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 347) 186844) = 90493 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b347_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 347)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 347)) 186844) = 90493 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o347 : xone 347 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a347_0 b347_0 a347_1 b347_1 a347_2 b347_2
    a347_3 b347_3 a347_4 b347_4 a347_5 b347_5

theorem a348_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 348))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 348) 0) = 123587 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b348_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 348)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 348)) 0) = 123587 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a348_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 348))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 348) 305530) = 231994 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b348_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 348)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 348)) 305530) = 231994 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a348_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 348))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 348) 5604) = 55282 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b348_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 348)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 348)) 5604) = 55282 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a348_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 348))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 348) 221549) = 306184 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b348_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 348)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 348)) 221549) = 306184 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a348_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 348))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 348) 266275) = 42660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b348_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 348)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 348)) 266275) = 42660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a348_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 348))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 348) 186844) = 230305 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b348_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 348)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 348)) 186844) = 230305 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o348 : xone 348 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a348_0 b348_0 a348_1 b348_1 a348_2 b348_2
    a348_3 b348_3 a348_4 b348_4 a348_5 b348_5

theorem a349_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 349))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 349) 0) = 272299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b349_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 349)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 349)) 0) = 272299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a349_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 349))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 349) 305530) = 263186 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b349_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 349)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 349)) 305530) = 263186 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a349_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 349))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 349) 5604) = 184865 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b349_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 349)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 349)) 5604) = 184865 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a349_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 349))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 349) 221549) = 29507 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b349_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 349)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 349)) 221549) = 29507 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a349_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 349))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 349) 266275) = 107620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b349_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 349)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 349)) 266275) = 107620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a349_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 349))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 349) 186844) = 230747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b349_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 349)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 349)) 186844) = 230747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o349 : xone 349 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a349_0 b349_0 a349_1 b349_1 a349_2 b349_2
    a349_3 b349_3 a349_4 b349_4 a349_5 b349_5

theorem a350_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 350))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 350) 0) = 296132 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b350_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 350)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 350)) 0) = 296132 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a350_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 350))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 350) 305530) = 246837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b350_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 350)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 350)) 305530) = 246837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a350_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 350))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 350) 5604) = 130682 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b350_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 350)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 350)) 5604) = 130682 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a350_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 350))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 350) 221549) = 32219 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b350_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 350)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 350)) 221549) = 32219 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a350_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 350))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 350) 266275) = 16224 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b350_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 350)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 350)) 266275) = 16224 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a350_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 350))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 350) 186844) = 28635 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b350_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 350)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 350)) 186844) = 28635 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o350 : xone 350 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a350_0 b350_0 a350_1 b350_1 a350_2 b350_2
    a350_3 b350_3 a350_4 b350_4 a350_5 b350_5

theorem a351_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 351))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 351) 0) = 208648 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b351_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 351)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 351)) 0) = 208648 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a351_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 351))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 351) 305530) = 73622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b351_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 351)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 351)) 305530) = 73622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a351_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 351))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 351) 5604) = 196371 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b351_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 351)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 351)) 5604) = 196371 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a351_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 351))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 351) 221549) = 8296 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b351_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 351)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 351)) 221549) = 8296 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a351_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 351))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 351) 266275) = 142558 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b351_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 351)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 351)) 266275) = 142558 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a351_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 351))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 351) 186844) = 300206 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b351_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 351)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 351)) 186844) = 300206 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o351 : xone 351 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a351_0 b351_0 a351_1 b351_1 a351_2 b351_2
    a351_3 b351_3 a351_4 b351_4 a351_5 b351_5

theorem a352_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 352))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 352) 0) = 217182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b352_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 352)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 352)) 0) = 217182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a352_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 352))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 352) 305530) = 77152 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b352_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 352)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 352)) 305530) = 77152 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a352_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 352))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 352) 5604) = 19732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b352_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 352)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 352)) 5604) = 19732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a352_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 352))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 352) 221549) = 88500 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b352_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 352)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 352)) 221549) = 88500 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a352_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 352))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 352) 266275) = 167237 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b352_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 352)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 352)) 266275) = 167237 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a352_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 352))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 352) 186844) = 34331 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b352_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 352)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 352)) 186844) = 34331 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o352 : xone 352 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a352_0 b352_0 a352_1 b352_1 a352_2 b352_2
    a352_3 b352_3 a352_4 b352_4 a352_5 b352_5

theorem a353_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 353))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 353) 0) = 48355 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b353_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 353)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 353)) 0) = 48355 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a353_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 353))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 353) 305530) = 134717 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b353_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 353)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 353)) 305530) = 134717 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a353_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 353))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 353) 5604) = 26250 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b353_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 353)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 353)) 5604) = 26250 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a353_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 353))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 353) 221549) = 274856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b353_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 353)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 353)) 221549) = 274856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a353_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 353))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 353) 266275) = 112909 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b353_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 353)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 353)) 266275) = 112909 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a353_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 353))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 353) 186844) = 130862 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b353_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 353)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 353)) 186844) = 130862 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o353 : xone 353 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a353_0 b353_0 a353_1 b353_1 a353_2 b353_2
    a353_3 b353_3 a353_4 b353_4 a353_5 b353_5

theorem a354_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 354))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 354) 0) = 40463 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b354_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 354)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 354)) 0) = 40463 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a354_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 354))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 354) 305530) = 101006 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b354_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 354)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 354)) 305530) = 101006 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a354_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 354))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 354) 5604) = 189489 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b354_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 354)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 354)) 5604) = 189489 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a354_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 354))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 354) 221549) = 106437 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b354_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 354)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 354)) 221549) = 106437 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a354_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 354))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 354) 266275) = 119622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b354_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 354)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 354)) 266275) = 119622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a354_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 354))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 354) 186844) = 149216 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b354_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 354)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 354)) 186844) = 149216 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o354 : xone 354 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a354_0 b354_0 a354_1 b354_1 a354_2 b354_2
    a354_3 b354_3 a354_4 b354_4 a354_5 b354_5

theorem a355_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 355))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 355) 0) = 162589 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b355_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 355)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 355)) 0) = 162589 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a355_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 355))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 355) 305530) = 200330 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b355_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 355)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 355)) 305530) = 200330 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a355_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 355))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 355) 5604) = 50946 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b355_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 355)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 355)) 5604) = 50946 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a355_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 355))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 355) 221549) = 125659 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b355_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 355)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 355)) 221549) = 125659 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a355_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 355))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 355) 266275) = 305064 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b355_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 355)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 355)) 266275) = 305064 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a355_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 355))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 355) 186844) = 145297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b355_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 355)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 355)) 186844) = 145297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o355 : xone 355 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a355_0 b355_0 a355_1 b355_1 a355_2 b355_2
    a355_3 b355_3 a355_4 b355_4 a355_5 b355_5

theorem a356_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 356))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 356) 0) = 17164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b356_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 356)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 356)) 0) = 17164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a356_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 356))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 356) 305530) = 7592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b356_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 356)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 356)) 305530) = 7592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a356_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 356))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 356) 5604) = 16339 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b356_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 356)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 356)) 5604) = 16339 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a356_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 356))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 356) 221549) = 260299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b356_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 356)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 356)) 221549) = 260299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a356_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 356))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 356) 266275) = 38323 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b356_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 356)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 356)) 266275) = 38323 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a356_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 356))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 356) 186844) = 41294 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b356_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 356)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 356)) 186844) = 41294 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o356 : xone 356 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a356_0 b356_0 a356_1 b356_1 a356_2 b356_2
    a356_3 b356_3 a356_4 b356_4 a356_5 b356_5

theorem a357_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 357))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 357) 0) = 143534 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b357_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 357)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 357)) 0) = 143534 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a357_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 357))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 357) 305530) = 284705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b357_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 357)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 357)) 305530) = 284705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a357_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 357))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 357) 5604) = 15017 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b357_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 357)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 357)) 5604) = 15017 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a357_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 357))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 357) 221549) = 24739 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b357_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 357)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 357)) 221549) = 24739 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a357_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 357))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 357) 266275) = 212899 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b357_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 357)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 357)) 266275) = 212899 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a357_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 357))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 357) 186844) = 48158 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b357_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 357)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 357)) 186844) = 48158 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o357 : xone 357 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a357_0 b357_0 a357_1 b357_1 a357_2 b357_2
    a357_3 b357_3 a357_4 b357_4 a357_5 b357_5

theorem a358_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 358))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 358) 0) = 145324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b358_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 358)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 358)) 0) = 145324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a358_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 358))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 358) 305530) = 108041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b358_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 358)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 358)) 305530) = 108041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a358_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 358))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 358) 5604) = 119228 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b358_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 358)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 358)) 5604) = 119228 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a358_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 358))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 358) 221549) = 306483 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b358_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 358)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 358)) 221549) = 306483 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a358_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 358))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 358) 266275) = 41596 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b358_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 358)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 358)) 266275) = 41596 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a358_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 358))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 358) 186844) = 270088 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b358_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 358)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 358)) 186844) = 270088 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o358 : xone 358 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a358_0 b358_0 a358_1 b358_1 a358_2 b358_2
    a358_3 b358_3 a358_4 b358_4 a358_5 b358_5

theorem a359_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 359))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 359) 0) = 279763 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b359_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 359)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 359)) 0) = 279763 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a359_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 359))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 359) 305530) = 125941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b359_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 359)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 359)) 305530) = 125941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a359_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 359))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 359) 5604) = 3023 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b359_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 359)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 359)) 5604) = 3023 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a359_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 359))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 359) 221549) = 54509 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b359_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 359)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 359)) 221549) = 54509 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a359_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 359))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 359) 266275) = 306176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b359_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 359)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 359)) 266275) = 306176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a359_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 359))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 359) 186844) = 183273 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b359_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 359)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 359)) 186844) = 183273 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o359 : xone 359 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a359_0 b359_0 a359_1 b359_1 a359_2 b359_2
    a359_3 b359_3 a359_4 b359_4 a359_5 b359_5

theorem a360_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 360))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 360) 0) = 6529 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b360_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 360)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 360)) 0) = 6529 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a360_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 360))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 360) 305530) = 176150 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b360_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 360)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 360)) 305530) = 176150 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a360_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 360))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 360) 5604) = 56201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b360_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 360)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 360)) 5604) = 56201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a360_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 360))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 360) 221549) = 222982 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b360_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 360)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 360)) 221549) = 222982 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a360_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 360))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 360) 266275) = 113433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b360_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 360)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 360)) 266275) = 113433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a360_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 360))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 360) 186844) = 71762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b360_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 360)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 360)) 186844) = 71762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o360 : xone 360 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a360_0 b360_0 a360_1 b360_1 a360_2 b360_2
    a360_3 b360_3 a360_4 b360_4 a360_5 b360_5

theorem a361_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 361))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 361) 0) = 109209 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b361_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 361)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 361)) 0) = 109209 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a361_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 361))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 361) 305530) = 7599 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b361_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 361)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 361)) 305530) = 7599 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a361_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 361))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 361) 5604) = 259193 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b361_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 361)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 361)) 5604) = 259193 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a361_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 361))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 361) 221549) = 118671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b361_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 361)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 361)) 221549) = 118671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a361_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 361))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 361) 266275) = 220279 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b361_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 361)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 361)) 266275) = 220279 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a361_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 361))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 361) 186844) = 161053 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b361_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 361)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 361)) 186844) = 161053 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o361 : xone 361 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a361_0 b361_0 a361_1 b361_1 a361_2 b361_2
    a361_3 b361_3 a361_4 b361_4 a361_5 b361_5

theorem a362_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 362))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 362) 0) = 206600 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b362_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 362)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 362)) 0) = 206600 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a362_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 362))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 362) 305530) = 61041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b362_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 362)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 362)) 305530) = 61041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a362_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 362))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 362) 5604) = 247006 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b362_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 362)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 362)) 5604) = 247006 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a362_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 362))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 362) 221549) = 151228 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b362_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 362)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 362)) 221549) = 151228 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a362_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 362))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 362) 266275) = 135171 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b362_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 362)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 362)) 266275) = 135171 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a362_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 362))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 362) 186844) = 205836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b362_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 362)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 362)) 186844) = 205836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o362 : xone 362 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a362_0 b362_0 a362_1 b362_1 a362_2 b362_2
    a362_3 b362_3 a362_4 b362_4 a362_5 b362_5

theorem a363_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 363))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 363) 0) = 124793 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b363_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 363)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 363)) 0) = 124793 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a363_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 363))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 363) 305530) = 89095 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b363_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 363)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 363)) 305530) = 89095 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a363_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 363))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 363) 5604) = 207465 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b363_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 363)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 363)) 5604) = 207465 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a363_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 363))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 363) 221549) = 110741 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b363_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 363)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 363)) 221549) = 110741 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a363_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 363))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 363) 266275) = 71902 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b363_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 363)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 363)) 266275) = 71902 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a363_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 363))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 363) 186844) = 285899 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b363_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 363)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 363)) 186844) = 285899 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o363 : xone 363 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a363_0 b363_0 a363_1 b363_1 a363_2 b363_2
    a363_3 b363_3 a363_4 b363_4 a363_5 b363_5

theorem a364_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 364))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 364) 0) = 2075 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b364_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 364)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 364)) 0) = 2075 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a364_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 364))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 364) 305530) = 124566 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b364_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 364)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 364)) 305530) = 124566 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a364_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 364))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 364) 5604) = 215221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b364_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 364)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 364)) 5604) = 215221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a364_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 364))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 364) 221549) = 51629 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b364_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 364)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 364)) 221549) = 51629 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a364_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 364))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 364) 266275) = 293244 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b364_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 364)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 364)) 266275) = 293244 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a364_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 364))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 364) 186844) = 294238 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b364_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 364)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 364)) 186844) = 294238 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o364 : xone 364 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a364_0 b364_0 a364_1 b364_1 a364_2 b364_2
    a364_3 b364_3 a364_4 b364_4 a364_5 b364_5

theorem a365_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 365))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 365) 0) = 246705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b365_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 365)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 365)) 0) = 246705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a365_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 365))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 365) 305530) = 50683 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b365_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 365)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 365)) 305530) = 50683 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a365_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 365))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 365) 5604) = 252688 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b365_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 365)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 365)) 5604) = 252688 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a365_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 365))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 365) 221549) = 219023 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b365_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 365)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 365)) 221549) = 219023 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a365_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 365))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 365) 266275) = 225602 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b365_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 365)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 365)) 266275) = 225602 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a365_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 365))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 365) 186844) = 216646 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b365_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 365)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 365)) 186844) = 216646 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o365 : xone 365 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a365_0 b365_0 a365_1 b365_1 a365_2 b365_2
    a365_3 b365_3 a365_4 b365_4 a365_5 b365_5

theorem a366_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 366))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 366) 0) = 233257 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b366_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 366)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 366)) 0) = 233257 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a366_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 366))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 366) 305530) = 134022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b366_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 366)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 366)) 305530) = 134022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a366_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 366))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 366) 5604) = 78358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b366_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 366)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 366)) 5604) = 78358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a366_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 366))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 366) 221549) = 279196 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b366_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 366)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 366)) 221549) = 279196 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a366_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 366))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 366) 266275) = 173154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b366_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 366)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 366)) 266275) = 173154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a366_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 366))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 366) 186844) = 140970 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b366_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 366)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 366)) 186844) = 140970 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o366 : xone 366 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a366_0 b366_0 a366_1 b366_1 a366_2 b366_2
    a366_3 b366_3 a366_4 b366_4 a366_5 b366_5

theorem a367_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 367))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 367) 0) = 111967 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b367_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 367)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 367)) 0) = 111967 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a367_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 367))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 367) 305530) = 204244 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b367_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 367)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 367)) 305530) = 204244 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a367_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 367))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 367) 5604) = 4085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b367_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 367)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 367)) 5604) = 4085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a367_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 367))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 367) 221549) = 199110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b367_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 367)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 367)) 221549) = 199110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a367_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 367))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 367) 266275) = 123957 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b367_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 367)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 367)) 266275) = 123957 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a367_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 367))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 367) 186844) = 227741 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b367_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 367)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 367)) 186844) = 227741 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o367 : xone 367 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a367_0 b367_0 a367_1 b367_1 a367_2 b367_2
    a367_3 b367_3 a367_4 b367_4 a367_5 b367_5

theorem a368_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 368))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 368) 0) = 159390 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b368_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 368)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 368)) 0) = 159390 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a368_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 368))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 368) 305530) = 215688 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b368_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 368)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 368)) 305530) = 215688 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a368_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 368))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 368) 5604) = 148394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b368_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 368)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 368)) 5604) = 148394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a368_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 368))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 368) 221549) = 131672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b368_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 368)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 368)) 221549) = 131672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a368_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 368))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 368) 266275) = 159930 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b368_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 368)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 368)) 266275) = 159930 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a368_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 368))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 368) 186844) = 120860 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b368_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 368)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 368)) 186844) = 120860 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o368 : xone 368 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a368_0 b368_0 a368_1 b368_1 a368_2 b368_2
    a368_3 b368_3 a368_4 b368_4 a368_5 b368_5

theorem a369_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 369))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 369) 0) = 184498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b369_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 369)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 369)) 0) = 184498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a369_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 369))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 369) 305530) = 166085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b369_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 369)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 369)) 305530) = 166085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a369_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 369))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 369) 5604) = 272314 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b369_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 369)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 369)) 5604) = 272314 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a369_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 369))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 369) 221549) = 730 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b369_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 369)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 369)) 221549) = 730 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a369_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 369))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 369) 266275) = 9297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b369_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 369)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 369)) 266275) = 9297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a369_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 369))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 369) 186844) = 35609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b369_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 369)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 369)) 186844) = 35609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o369 : xone 369 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a369_0 b369_0 a369_1 b369_1 a369_2 b369_2
    a369_3 b369_3 a369_4 b369_4 a369_5 b369_5

theorem a370_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 370))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 370) 0) = 131337 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b370_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 370)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 370)) 0) = 131337 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a370_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 370))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 370) 305530) = 79365 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b370_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 370)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 370)) 305530) = 79365 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a370_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 370))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 370) 5604) = 211593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b370_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 370)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 370)) 5604) = 211593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a370_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 370))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 370) 221549) = 155670 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b370_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 370)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 370)) 221549) = 155670 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a370_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 370))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 370) 266275) = 152025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b370_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 370)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 370)) 266275) = 152025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a370_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 370))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 370) 186844) = 115499 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b370_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 370)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 370)) 186844) = 115499 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o370 : xone 370 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a370_0 b370_0 a370_1 b370_1 a370_2 b370_2
    a370_3 b370_3 a370_4 b370_4 a370_5 b370_5

theorem a371_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 371))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 371) 0) = 272762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b371_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 371)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 371)) 0) = 272762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a371_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 371))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 371) 305530) = 252488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b371_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 371)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 371)) 305530) = 252488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a371_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 371))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 371) 5604) = 39286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b371_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 371)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 371)) 5604) = 39286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a371_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 371))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 371) 221549) = 205062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b371_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 371)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 371)) 221549) = 205062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a371_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 371))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 371) 266275) = 142701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b371_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 371)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 371)) 266275) = 142701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a371_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 371))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 371) 186844) = 1308 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b371_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 371)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 371)) 186844) = 1308 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o371 : xone 371 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a371_0 b371_0 a371_1 b371_1 a371_2 b371_2
    a371_3 b371_3 a371_4 b371_4 a371_5 b371_5

theorem a372_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 372))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 372) 0) = 100818 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b372_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 372)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 372)) 0) = 100818 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a372_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 372))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 372) 305530) = 299833 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b372_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 372)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 372)) 305530) = 299833 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a372_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 372))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 372) 5604) = 94228 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b372_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 372)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 372)) 5604) = 94228 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a372_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 372))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 372) 221549) = 38147 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b372_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 372)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 372)) 221549) = 38147 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a372_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 372))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 372) 266275) = 149194 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b372_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 372)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 372)) 266275) = 149194 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a372_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 372))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 372) 186844) = 190927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b372_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 372)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 372)) 186844) = 190927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o372 : xone 372 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a372_0 b372_0 a372_1 b372_1 a372_2 b372_2
    a372_3 b372_3 a372_4 b372_4 a372_5 b372_5

theorem a373_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 373))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 373) 0) = 216458 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b373_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 373)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 373)) 0) = 216458 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a373_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 373))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 373) 305530) = 281134 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b373_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 373)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 373)) 305530) = 281134 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a373_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 373))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 373) 5604) = 240373 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b373_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 373)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 373)) 5604) = 240373 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a373_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 373))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 373) 221549) = 134089 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b373_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 373)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 373)) 221549) = 134089 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a373_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 373))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 373) 266275) = 175227 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b373_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 373)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 373)) 266275) = 175227 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a373_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 373))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 373) 186844) = 59638 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b373_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 373)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 373)) 186844) = 59638 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o373 : xone 373 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a373_0 b373_0 a373_1 b373_1 a373_2 b373_2
    a373_3 b373_3 a373_4 b373_4 a373_5 b373_5

theorem a374_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 374))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 374) 0) = 249518 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b374_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 374)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 374)) 0) = 249518 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a374_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 374))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 374) 305530) = 77922 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b374_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 374)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 374)) 305530) = 77922 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a374_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 374))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 374) 5604) = 2598 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b374_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 374)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 374)) 5604) = 2598 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a374_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 374))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 374) 221549) = 245331 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b374_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 374)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 374)) 221549) = 245331 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a374_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 374))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 374) 266275) = 102102 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b374_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 374)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 374)) 266275) = 102102 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a374_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 374))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 374) 186844) = 199252 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b374_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 374)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 374)) 186844) = 199252 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o374 : xone 374 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a374_0 b374_0 a374_1 b374_1 a374_2 b374_2
    a374_3 b374_3 a374_4 b374_4 a374_5 b374_5

theorem a375_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 375))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 375) 0) = 190763 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b375_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 375)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 375)) 0) = 190763 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a375_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 375))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 375) 305530) = 40182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b375_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 375)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 375)) 305530) = 40182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a375_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 375))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 375) 5604) = 275014 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b375_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 375)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 375)) 5604) = 275014 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a375_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 375))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 375) 221549) = 85218 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b375_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 375)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 375)) 221549) = 85218 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a375_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 375))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 375) 266275) = 24897 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b375_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 375)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 375)) 266275) = 24897 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a375_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 375))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 375) 186844) = 28963 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b375_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 375)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 375)) 186844) = 28963 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o375 : xone 375 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a375_0 b375_0 a375_1 b375_1 a375_2 b375_2
    a375_3 b375_3 a375_4 b375_4 a375_5 b375_5

theorem a376_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 376))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 376) 0) = 119469 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b376_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 376)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 376)) 0) = 119469 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a376_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 376))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 376) 305530) = 302524 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b376_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 376)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 376)) 305530) = 302524 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a376_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 376))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 376) 5604) = 8707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b376_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 376)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 376)) 5604) = 8707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a376_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 376))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 376) 221549) = 97567 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b376_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 376)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 376)) 221549) = 97567 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a376_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 376))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 376) 266275) = 163026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b376_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 376)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 376)) 266275) = 163026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a376_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 376))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 376) 186844) = 224843 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b376_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 376)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 376)) 186844) = 224843 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o376 : xone 376 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a376_0 b376_0 a376_1 b376_1 a376_2 b376_2
    a376_3 b376_3 a376_4 b376_4 a376_5 b376_5

theorem a377_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 377))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 377) 0) = 161025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b377_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 377)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 377)) 0) = 161025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a377_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 377))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 377) 305530) = 174496 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b377_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 377)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 377)) 305530) = 174496 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a377_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 377))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 377) 5604) = 28305 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b377_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 377)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 377)) 5604) = 28305 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a377_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 377))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 377) 221549) = 216514 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b377_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 377)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 377)) 221549) = 216514 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a377_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 377))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 377) 266275) = 98849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b377_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 377)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 377)) 266275) = 98849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a377_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 377))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 377) 186844) = 114177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b377_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 377)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 377)) 186844) = 114177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o377 : xone 377 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a377_0 b377_0 a377_1 b377_1 a377_2 b377_2
    a377_3 b377_3 a377_4 b377_4 a377_5 b377_5

theorem a378_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 378))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 378) 0) = 157807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b378_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 378)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 378)) 0) = 157807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a378_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 378))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 378) 305530) = 41657 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b378_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 378)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 378)) 305530) = 41657 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a378_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 378))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 378) 5604) = 280128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b378_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 378)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 378)) 5604) = 280128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a378_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 378))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 378) 221549) = 190532 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b378_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 378)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 378)) 221549) = 190532 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a378_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 378))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 378) 266275) = 78330 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b378_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 378)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 378)) 266275) = 78330 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a378_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 378))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 378) 186844) = 2210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b378_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 378)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 378)) 186844) = 2210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o378 : xone 378 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a378_0 b378_0 a378_1 b378_1 a378_2 b378_2
    a378_3 b378_3 a378_4 b378_4 a378_5 b378_5

theorem a379_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 379))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 379) 0) = 249853 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b379_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 379)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 379)) 0) = 249853 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a379_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 379))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 379) 305530) = 83283 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b379_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 379)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 379)) 305530) = 83283 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a379_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 379))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 379) 5604) = 244826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b379_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 379)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 379)) 5604) = 244826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a379_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 379))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 379) 221549) = 246009 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b379_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 379)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 379)) 221549) = 246009 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a379_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 379))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 379) 266275) = 178332 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b379_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 379)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 379)) 266275) = 178332 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a379_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 379))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 379) 186844) = 258648 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b379_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 379)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 379)) 186844) = 258648 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o379 : xone 379 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a379_0 b379_0 a379_1 b379_1 a379_2 b379_2
    a379_3 b379_3 a379_4 b379_4 a379_5 b379_5

theorem a380_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 380))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 380) 0) = 18241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b380_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 380)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 380)) 0) = 18241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a380_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 380))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 380) 305530) = 139082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b380_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 380)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 380)) 305530) = 139082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a380_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 380))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 380) 5604) = 62129 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b380_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 380)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 380)) 5604) = 62129 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a380_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 380))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 380) 221549) = 32985 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b380_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 380)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 380)) 221549) = 32985 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a380_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 380))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 380) 266275) = 220008 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b380_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 380)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 380)) 266275) = 220008 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a380_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 380))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 380) 186844) = 64329 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b380_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 380)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 380)) 186844) = 64329 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o380 : xone 380 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a380_0 b380_0 a380_1 b380_1 a380_2 b380_2
    a380_3 b380_3 a380_4 b380_4 a380_5 b380_5

theorem a381_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 381))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 381) 0) = 188923 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b381_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 381)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 381)) 0) = 188923 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a381_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 381))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 381) 305530) = 288768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b381_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 381)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 381)) 305530) = 288768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a381_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 381))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 381) 5604) = 255055 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b381_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 381)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 381)) 5604) = 255055 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a381_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 381))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 381) 221549) = 192245 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b381_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 381)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 381)) 221549) = 192245 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a381_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 381))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 381) 266275) = 300113 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b381_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 381)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 381)) 266275) = 300113 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a381_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 381))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 381) 186844) = 74863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b381_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 381)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 381)) 186844) = 74863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o381 : xone 381 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a381_0 b381_0 a381_1 b381_1 a381_2 b381_2
    a381_3 b381_3 a381_4 b381_4 a381_5 b381_5

theorem a382_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 382))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 382) 0) = 286234 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b382_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 382)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 382)) 0) = 286234 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a382_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 382))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 382) 305530) = 241237 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b382_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 382)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 382)) 305530) = 241237 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a382_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 382))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 382) 5604) = 197036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b382_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 382)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 382)) 5604) = 197036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a382_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 382))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 382) 221549) = 23528 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b382_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 382)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 382)) 221549) = 23528 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a382_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 382))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 382) 266275) = 79634 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b382_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 382)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 382)) 266275) = 79634 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a382_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 382))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 382) 186844) = 287369 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b382_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 382)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 382)) 186844) = 287369 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o382 : xone 382 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a382_0 b382_0 a382_1 b382_1 a382_2 b382_2
    a382_3 b382_3 a382_4 b382_4 a382_5 b382_5

theorem a383_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 383))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 383) 0) = 237551 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b383_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 383)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 383)) 0) = 237551 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a383_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 383))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 383) 305530) = 177136 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b383_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 383)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 383)) 305530) = 177136 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a383_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 383))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 383) 5604) = 138866 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b383_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 383)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 383)) 5604) = 138866 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a383_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 383))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 383) 221549) = 234826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b383_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 383)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 383)) 221549) = 234826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a383_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 383))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 383) 266275) = 77310 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b383_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 383)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 383)) 266275) = 77310 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a383_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 383))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 383) 186844) = 148100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b383_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 383)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 383)) 186844) = 148100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o383 : xone 383 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a383_0 b383_0 a383_1 b383_1 a383_2 b383_2
    a383_3 b383_3 a383_4 b383_4 a383_5 b383_5

theorem a384_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 384))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 384) 0) = 267161 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b384_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 384)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 384)) 0) = 267161 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a384_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 384))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 384) 305530) = 268710 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b384_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 384)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 384)) 305530) = 268710 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a384_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 384))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 384) 5604) = 270166 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b384_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 384)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 384)) 5604) = 270166 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a384_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 384))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 384) 221549) = 1623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b384_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 384)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 384)) 221549) = 1623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a384_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 384))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 384) 266275) = 223685 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b384_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 384)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 384)) 266275) = 223685 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a384_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 384))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 384) 186844) = 171522 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b384_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 384)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 384)) 186844) = 171522 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o384 : xone 384 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a384_0 b384_0 a384_1 b384_1 a384_2 b384_2
    a384_3 b384_3 a384_4 b384_4 a384_5 b384_5

theorem a385_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 385))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 385) 0) = 287160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b385_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 385)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 385)) 0) = 287160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a385_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 385))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 385) 305530) = 108673 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b385_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 385)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 385)) 305530) = 108673 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a385_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 385))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 385) 5604) = 231082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b385_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 385)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 385)) 5604) = 231082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a385_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 385))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 385) 221549) = 108807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b385_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 385)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 385)) 221549) = 108807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a385_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 385))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 385) 266275) = 220353 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b385_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 385)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 385)) 266275) = 220353 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a385_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 385))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 385) 186844) = 143698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b385_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 385)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 385)) 186844) = 143698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o385 : xone 385 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a385_0 b385_0 a385_1 b385_1 a385_2 b385_2
    a385_3 b385_3 a385_4 b385_4 a385_5 b385_5

theorem a386_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 386))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 386) 0) = 47970 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b386_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 386)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 386)) 0) = 47970 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a386_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 386))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 386) 305530) = 115972 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b386_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 386)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 386)) 305530) = 115972 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a386_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 386))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 386) 5604) = 120942 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b386_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 386)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 386)) 5604) = 120942 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a386_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 386))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 386) 221549) = 263766 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b386_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 386)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 386)) 221549) = 263766 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a386_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 386))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 386) 266275) = 273258 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b386_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 386)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 386)) 266275) = 273258 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a386_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 386))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 386) 186844) = 5573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b386_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 386)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 386)) 186844) = 5573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o386 : xone 386 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a386_0 b386_0 a386_1 b386_1 a386_2 b386_2
    a386_3 b386_3 a386_4 b386_4 a386_5 b386_5

theorem a387_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 387))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 387) 0) = 108324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b387_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 387)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 387)) 0) = 108324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a387_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 387))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 387) 305530) = 278651 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b387_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 387)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 387)) 305530) = 278651 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a387_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 387))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 387) 5604) = 178770 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b387_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 387)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 387)) 5604) = 178770 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a387_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 387))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 387) 221549) = 80243 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b387_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 387)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 387)) 221549) = 80243 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a387_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 387))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 387) 266275) = 256139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b387_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 387)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 387)) 266275) = 256139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a387_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 387))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 387) 186844) = 147002 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b387_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 387)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 387)) 186844) = 147002 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o387 : xone 387 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a387_0 b387_0 a387_1 b387_1 a387_2 b387_2
    a387_3 b387_3 a387_4 b387_4 a387_5 b387_5

theorem a388_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 388))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 388) 0) = 168900 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b388_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 388)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 388)) 0) = 168900 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a388_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 388))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 388) 305530) = 171971 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b388_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 388)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 388)) 305530) = 171971 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a388_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 388))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 388) 5604) = 185415 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b388_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 388)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 388)) 5604) = 185415 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a388_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 388))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 388) 221549) = 283491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b388_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 388)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 388)) 221549) = 283491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a388_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 388))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 388) 266275) = 165579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b388_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 388)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 388)) 266275) = 165579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a388_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 388))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 388) 186844) = 180960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b388_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 388)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 388)) 186844) = 180960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o388 : xone 388 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a388_0 b388_0 a388_1 b388_1 a388_2 b388_2
    a388_3 b388_3 a388_4 b388_4 a388_5 b388_5

theorem a389_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 389))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 389) 0) = 255342 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b389_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 389)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 389)) 0) = 255342 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a389_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 389))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 389) 305530) = 62295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b389_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 389)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 389)) 305530) = 62295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a389_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 389))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 389) 5604) = 92122 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b389_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 389)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 389)) 5604) = 92122 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a389_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 389))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 389) 221549) = 71127 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b389_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 389)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 389)) 221549) = 71127 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a389_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 389))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 389) 266275) = 102075 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b389_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 389)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 389)) 266275) = 102075 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a389_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 389))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 389) 186844) = 262063 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b389_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 389)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 389)) 186844) = 262063 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o389 : xone 389 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a389_0 b389_0 a389_1 b389_1 a389_2 b389_2
    a389_3 b389_3 a389_4 b389_4 a389_5 b389_5

theorem a390_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 390))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 390) 0) = 302392 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b390_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 390)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 390)) 0) = 302392 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a390_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 390))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 390) 305530) = 232245 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b390_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 390)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 390)) 305530) = 232245 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a390_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 390))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 390) 5604) = 61643 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b390_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 390)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 390)) 5604) = 61643 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a390_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 390))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 390) 221549) = 69410 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b390_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 390)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 390)) 221549) = 69410 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a390_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 390))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 390) 266275) = 164997 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b390_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 390)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 390)) 266275) = 164997 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a390_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 390))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 390) 186844) = 72353 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b390_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 390)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 390)) 186844) = 72353 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o390 : xone 390 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a390_0 b390_0 a390_1 b390_1 a390_2 b390_2
    a390_3 b390_3 a390_4 b390_4 a390_5 b390_5

theorem a391_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 391))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 391) 0) = 114579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b391_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 391)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 391)) 0) = 114579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a391_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 391))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 391) 305530) = 60230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b391_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 391)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 391)) 305530) = 60230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a391_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 391))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 391) 5604) = 222633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b391_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 391)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 391)) 5604) = 222633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a391_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 391))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 391) 221549) = 112573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b391_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 391)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 391)) 221549) = 112573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a391_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 391))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 391) 266275) = 29763 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b391_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 391)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 391)) 266275) = 29763 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a391_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 391))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 391) 186844) = 187057 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b391_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 391)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 391)) 186844) = 187057 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o391 : xone 391 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a391_0 b391_0 a391_1 b391_1 a391_2 b391_2
    a391_3 b391_3 a391_4 b391_4 a391_5 b391_5

theorem a392_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 392))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 392) 0) = 182326 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b392_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 392)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 392)) 0) = 182326 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a392_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 392))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 392) 305530) = 83022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b392_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 392)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 392)) 305530) = 83022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a392_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 392))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 392) 5604) = 222612 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b392_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 392)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 392)) 5604) = 222612 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a392_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 392))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 392) 221549) = 264884 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b392_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 392)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 392)) 221549) = 264884 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a392_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 392))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 392) 266275) = 242084 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b392_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 392)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 392)) 266275) = 242084 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a392_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 392))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 392) 186844) = 174466 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b392_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 392)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 392)) 186844) = 174466 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o392 : xone 392 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a392_0 b392_0 a392_1 b392_1 a392_2 b392_2
    a392_3 b392_3 a392_4 b392_4 a392_5 b392_5

theorem a393_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 393))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 393) 0) = 262455 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b393_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 393)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 393)) 0) = 262455 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a393_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 393))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 393) 305530) = 56460 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b393_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 393)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 393)) 305530) = 56460 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a393_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 393))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 393) 5604) = 218106 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b393_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 393)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 393)) 5604) = 218106 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a393_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 393))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 393) 221549) = 228429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b393_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 393)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 393)) 221549) = 228429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a393_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 393))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 393) 266275) = 267746 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b393_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 393)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 393)) 266275) = 267746 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a393_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 393))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 393) 186844) = 192878 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b393_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 393)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 393)) 186844) = 192878 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o393 : xone 393 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a393_0 b393_0 a393_1 b393_1 a393_2 b393_2
    a393_3 b393_3 a393_4 b393_4 a393_5 b393_5

theorem a394_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 394))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 394) 0) = 111178 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b394_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 394)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 394)) 0) = 111178 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a394_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 394))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 394) 305530) = 27096 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b394_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 394)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 394)) 305530) = 27096 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a394_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 394))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 394) 5604) = 157336 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b394_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 394)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 394)) 5604) = 157336 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a394_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 394))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 394) 221549) = 57744 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b394_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 394)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 394)) 221549) = 57744 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a394_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 394))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 394) 266275) = 41394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b394_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 394)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 394)) 266275) = 41394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a394_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 394))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 394) 186844) = 297176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b394_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 394)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 394)) 186844) = 297176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o394 : xone 394 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a394_0 b394_0 a394_1 b394_1 a394_2 b394_2
    a394_3 b394_3 a394_4 b394_4 a394_5 b394_5

theorem a395_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 395))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 395) 0) = 284694 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b395_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 395)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 395)) 0) = 284694 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a395_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 395))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 395) 305530) = 148992 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b395_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 395)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 395)) 305530) = 148992 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a395_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 395))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 395) 5604) = 261057 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b395_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 395)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 395)) 5604) = 261057 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a395_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 395))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 395) 221549) = 67715 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b395_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 395)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 395)) 221549) = 67715 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a395_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 395))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 395) 266275) = 244022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b395_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 395)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 395)) 266275) = 244022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a395_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 395))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 395) 186844) = 245867 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b395_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 395)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 395)) 186844) = 245867 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o395 : xone 395 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a395_0 b395_0 a395_1 b395_1 a395_2 b395_2
    a395_3 b395_3 a395_4 b395_4 a395_5 b395_5

theorem a396_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 396))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 396) 0) = 213012 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b396_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 396)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 396)) 0) = 213012 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a396_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 396))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 396) 305530) = 219652 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b396_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 396)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 396)) 305530) = 219652 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a396_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 396))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 396) 5604) = 292274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b396_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 396)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 396)) 5604) = 292274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a396_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 396))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 396) 221549) = 233759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b396_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 396)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 396)) 221549) = 233759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a396_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 396))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 396) 266275) = 9081 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b396_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 396)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 396)) 266275) = 9081 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a396_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 396))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 396) 186844) = 221163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b396_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 396)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 396)) 186844) = 221163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o396 : xone 396 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a396_0 b396_0 a396_1 b396_1 a396_2 b396_2
    a396_3 b396_3 a396_4 b396_4 a396_5 b396_5

theorem a397_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 397))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 397) 0) = 180137 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b397_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 397)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 397)) 0) = 180137 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a397_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 397))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 397) 305530) = 232616 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b397_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 397)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 397)) 305530) = 232616 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a397_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 397))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 397) 5604) = 96671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b397_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 397)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 397)) 5604) = 96671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a397_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 397))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 397) 221549) = 67254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b397_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 397)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 397)) 221549) = 67254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a397_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 397))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 397) 266275) = 108886 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b397_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 397)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 397)) 266275) = 108886 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a397_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 397))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 397) 186844) = 186542 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b397_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 397)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 397)) 186844) = 186542 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o397 : xone 397 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a397_0 b397_0 a397_1 b397_1 a397_2 b397_2
    a397_3 b397_3 a397_4 b397_4 a397_5 b397_5

theorem a398_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 398))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 398) 0) = 17007 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b398_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 398)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 398)) 0) = 17007 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a398_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 398))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 398) 305530) = 142944 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b398_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 398)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 398)) 305530) = 142944 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a398_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 398))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 398) 5604) = 3249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b398_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 398)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 398)) 5604) = 3249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a398_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 398))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 398) 221549) = 175199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b398_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 398)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 398)) 221549) = 175199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a398_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 398))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 398) 266275) = 268335 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b398_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 398)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 398)) 266275) = 268335 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a398_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 398))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 398) 186844) = 254076 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b398_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 398)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 398)) 186844) = 254076 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o398 : xone 398 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a398_0 b398_0 a398_1 b398_1 a398_2 b398_2
    a398_3 b398_3 a398_4 b398_4 a398_5 b398_5

theorem a399_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 399))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 399) 0) = 120812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b399_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 399)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 399)) 0) = 120812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a399_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 399))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 399) 305530) = 2951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b399_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 399)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 399)) 305530) = 2951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a399_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 399))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 399) 5604) = 104487 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b399_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 399)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 399)) 5604) = 104487 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a399_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 399))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 399) 221549) = 165730 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b399_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 399)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 399)) 221549) = 165730 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a399_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 399))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 399) 266275) = 132264 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b399_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 399)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 399)) 266275) = 132264 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a399_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 399))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 399) 186844) = 127014 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b399_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 399)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 399)) 186844) = 127014 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o399 : xone 399 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a399_0 b399_0 a399_1 b399_1 a399_2 b399_2
    a399_3 b399_3 a399_4 b399_4 a399_5 b399_5

theorem a400_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 400))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 400) 0) = 56254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b400_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 400)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 400)) 0) = 56254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a400_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 400))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 400) 305530) = 153111 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b400_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 400)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 400)) 305530) = 153111 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a400_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 400))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 400) 5604) = 137460 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b400_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 400)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 400)) 5604) = 137460 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a400_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 400))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 400) 221549) = 207454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b400_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 400)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 400)) 221549) = 207454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a400_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 400))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 400) 266275) = 28429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b400_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 400)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 400)) 266275) = 28429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a400_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 400))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 400) 186844) = 43226 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b400_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 400)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 400)) 186844) = 43226 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o400 : xone 400 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a400_0 b400_0 a400_1 b400_1 a400_2 b400_2
    a400_3 b400_3 a400_4 b400_4 a400_5 b400_5

theorem a401_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 401))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 401) 0) = 234383 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b401_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 401)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 401)) 0) = 234383 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a401_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 401))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 401) 305530) = 234099 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b401_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 401)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 401)) 305530) = 234099 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a401_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 401))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 401) 5604) = 55075 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b401_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 401)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 401)) 5604) = 55075 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a401_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 401))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 401) 221549) = 81217 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b401_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 401)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 401)) 221549) = 81217 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a401_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 401))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 401) 266275) = 240789 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b401_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 401)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 401)) 266275) = 240789 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a401_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 401))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 401) 186844) = 14262 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b401_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 401)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 401)) 186844) = 14262 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o401 : xone 401 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a401_0 b401_0 a401_1 b401_1 a401_2 b401_2
    a401_3 b401_3 a401_4 b401_4 a401_5 b401_5

theorem a402_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 402))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 402) 0) = 253442 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b402_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 402)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 402)) 0) = 253442 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a402_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 402))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 402) 305530) = 80888 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b402_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 402)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 402)) 305530) = 80888 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a402_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 402))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 402) 5604) = 61634 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b402_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 402)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 402)) 5604) = 61634 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a402_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 402))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 402) 221549) = 140501 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b402_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 402)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 402)) 221549) = 140501 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a402_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 402))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 402) 266275) = 181819 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b402_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 402)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 402)) 266275) = 181819 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a402_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 402))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 402) 186844) = 188912 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b402_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 402)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 402)) 186844) = 188912 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o402 : xone 402 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a402_0 b402_0 a402_1 b402_1 a402_2 b402_2
    a402_3 b402_3 a402_4 b402_4 a402_5 b402_5

theorem a403_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 403))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 403) 0) = 183101 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b403_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 403)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 403)) 0) = 183101 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a403_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 403))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 403) 305530) = 21671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b403_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 403)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 403)) 305530) = 21671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a403_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 403))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 403) 5604) = 194894 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b403_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 403)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 403)) 5604) = 194894 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a403_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 403))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 403) 221549) = 60653 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b403_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 403)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 403)) 221549) = 60653 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a403_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 403))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 403) 266275) = 217276 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b403_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 403)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 403)) 266275) = 217276 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a403_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 403))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 403) 186844) = 151344 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b403_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 403)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 403)) 186844) = 151344 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o403 : xone 403 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a403_0 b403_0 a403_1 b403_1 a403_2 b403_2
    a403_3 b403_3 a403_4 b403_4 a403_5 b403_5

theorem a404_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 404))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 404) 0) = 279458 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b404_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 404)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 404)) 0) = 279458 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a404_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 404))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 404) 305530) = 140167 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b404_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 404)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 404)) 305530) = 140167 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a404_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 404))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 404) 5604) = 30244 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b404_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 404)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 404)) 5604) = 30244 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a404_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 404))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 404) 221549) = 192003 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b404_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 404)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 404)) 221549) = 192003 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a404_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 404))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 404) 266275) = 68510 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b404_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 404)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 404)) 266275) = 68510 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a404_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 404))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 404) 186844) = 76436 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b404_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 404)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 404)) 186844) = 76436 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o404 : xone 404 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a404_0 b404_0 a404_1 b404_1 a404_2 b404_2
    a404_3 b404_3 a404_4 b404_4 a404_5 b404_5

theorem a405_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 405))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 405) 0) = 20961 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b405_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 405)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 405)) 0) = 20961 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a405_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 405))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 405) 305530) = 21732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b405_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 405)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 405)) 305530) = 21732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a405_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 405))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 405) 5604) = 44378 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b405_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 405)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 405)) 5604) = 44378 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a405_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 405))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 405) 221549) = 91283 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b405_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 405)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 405)) 221549) = 91283 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a405_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 405))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 405) 266275) = 110161 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b405_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 405)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 405)) 266275) = 110161 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a405_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 405))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 405) 186844) = 280698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b405_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 405)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 405)) 186844) = 280698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o405 : xone 405 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a405_0 b405_0 a405_1 b405_1 a405_2 b405_2
    a405_3 b405_3 a405_4 b405_4 a405_5 b405_5

theorem a406_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 406))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 406) 0) = 253189 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b406_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 406)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 406)) 0) = 253189 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a406_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 406))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 406) 305530) = 287381 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b406_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 406)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 406)) 305530) = 287381 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a406_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 406))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 406) 5604) = 88030 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b406_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 406)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 406)) 5604) = 88030 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a406_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 406))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 406) 221549) = 151348 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b406_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 406)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 406)) 221549) = 151348 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a406_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 406))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 406) 266275) = 184508 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b406_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 406)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 406)) 266275) = 184508 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a406_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 406))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 406) 186844) = 14780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b406_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 406)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 406)) 186844) = 14780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o406 : xone 406 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a406_0 b406_0 a406_1 b406_1 a406_2 b406_2
    a406_3 b406_3 a406_4 b406_4 a406_5 b406_5

theorem a407_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 407))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 407) 0) = 202829 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b407_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 407)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 407)) 0) = 202829 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a407_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 407))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 407) 305530) = 72620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b407_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 407)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 407)) 305530) = 72620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a407_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 407))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 407) 5604) = 185279 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b407_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 407)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 407)) 5604) = 185279 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a407_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 407))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 407) 221549) = 124871 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b407_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 407)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 407)) 221549) = 124871 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a407_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 407))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 407) 266275) = 200341 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b407_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 407)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 407)) 266275) = 200341 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a407_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 407))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 407) 186844) = 235768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b407_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 407)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 407)) 186844) = 235768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o407 : xone 407 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a407_0 b407_0 a407_1 b407_1 a407_2 b407_2
    a407_3 b407_3 a407_4 b407_4 a407_5 b407_5

theorem a408_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 408))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 408) 0) = 23678 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b408_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 408)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 408)) 0) = 23678 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a408_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 408))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 408) 305530) = 59267 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b408_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 408)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 408)) 305530) = 59267 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a408_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 408))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 408) 5604) = 169193 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b408_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 408)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 408)) 5604) = 169193 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a408_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 408))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 408) 221549) = 185047 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b408_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 408)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 408)) 221549) = 185047 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a408_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 408))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 408) 266275) = 203114 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b408_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 408)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 408)) 266275) = 203114 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a408_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 408))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 408) 186844) = 12121 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b408_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 408)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 408)) 186844) = 12121 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o408 : xone 408 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a408_0 b408_0 a408_1 b408_1 a408_2 b408_2
    a408_3 b408_3 a408_4 b408_4 a408_5 b408_5

theorem a409_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 409))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 409) 0) = 36813 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b409_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 409)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 409)) 0) = 36813 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a409_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 409))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 409) 305530) = 20601 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b409_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 409)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 409)) 305530) = 20601 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a409_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 409))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 409) 5604) = 74393 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b409_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 409)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 409)) 5604) = 74393 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a409_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 409))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 409) 221549) = 287451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b409_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 409)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 409)) 221549) = 287451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a409_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 409))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 409) 266275) = 293249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b409_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 409)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 409)) 266275) = 293249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a409_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 409))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 409) 186844) = 159920 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b409_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 409)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 409)) 186844) = 159920 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o409 : xone 409 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a409_0 b409_0 a409_1 b409_1 a409_2 b409_2
    a409_3 b409_3 a409_4 b409_4 a409_5 b409_5

theorem a410_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 410))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 410) 0) = 162693 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b410_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 410)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 410)) 0) = 162693 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a410_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 410))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 410) 305530) = 38799 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b410_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 410)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 410)) 305530) = 38799 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a410_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 410))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 410) 5604) = 205026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b410_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 410)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 410)) 5604) = 205026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a410_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 410))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 410) 221549) = 157159 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b410_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 410)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 410)) 221549) = 157159 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a410_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 410))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 410) 266275) = 5979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b410_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 410)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 410)) 266275) = 5979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a410_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 410))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 410) 186844) = 212432 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b410_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 410)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 410)) 186844) = 212432 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o410 : xone 410 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a410_0 b410_0 a410_1 b410_1 a410_2 b410_2
    a410_3 b410_3 a410_4 b410_4 a410_5 b410_5

theorem a411_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 411))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 411) 0) = 110333 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b411_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 411)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 411)) 0) = 110333 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a411_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 411))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 411) 305530) = 240402 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b411_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 411)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 411)) 305530) = 240402 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a411_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 411))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 411) 5604) = 140017 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b411_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 411)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 411)) 5604) = 140017 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a411_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 411))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 411) 221549) = 179375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b411_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 411)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 411)) 221549) = 179375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a411_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 411))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 411) 266275) = 34152 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b411_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 411)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 411)) 266275) = 34152 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a411_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 411))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 411) 186844) = 179407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b411_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 411)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 411)) 186844) = 179407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o411 : xone 411 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a411_0 b411_0 a411_1 b411_1 a411_2 b411_2
    a411_3 b411_3 a411_4 b411_4 a411_5 b411_5

theorem a412_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 412))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 412) 0) = 138488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b412_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 412)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 412)) 0) = 138488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a412_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 412))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 412) 305530) = 14465 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b412_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 412)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 412)) 305530) = 14465 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a412_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 412))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 412) 5604) = 18370 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b412_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 412)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 412)) 5604) = 18370 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a412_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 412))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 412) 221549) = 103193 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b412_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 412)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 412)) 221549) = 103193 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a412_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 412))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 412) 266275) = 23416 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b412_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 412)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 412)) 266275) = 23416 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a412_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 412))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 412) 186844) = 281979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b412_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 412)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 412)) 186844) = 281979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o412 : xone 412 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a412_0 b412_0 a412_1 b412_1 a412_2 b412_2
    a412_3 b412_3 a412_4 b412_4 a412_5 b412_5

theorem a413_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 413))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 413) 0) = 287418 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b413_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 413)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 413)) 0) = 287418 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a413_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 413))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 413) 305530) = 52327 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b413_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 413)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 413)) 305530) = 52327 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a413_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 413))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 413) 5604) = 200677 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b413_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 413)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 413)) 5604) = 200677 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a413_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 413))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 413) 221549) = 92319 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b413_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 413)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 413)) 221549) = 92319 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a413_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 413))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 413) 266275) = 154125 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b413_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 413)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 413)) 266275) = 154125 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a413_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 413))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 413) 186844) = 93796 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b413_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 413)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 413)) 186844) = 93796 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o413 : xone 413 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a413_0 b413_0 a413_1 b413_1 a413_2 b413_2
    a413_3 b413_3 a413_4 b413_4 a413_5 b413_5

theorem a414_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 414))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 414) 0) = 101568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b414_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 414)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 414)) 0) = 101568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a414_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 414))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 414) 305530) = 257306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b414_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 414)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 414)) 305530) = 257306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a414_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 414))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 414) 5604) = 133167 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b414_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 414)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 414)) 5604) = 133167 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a414_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 414))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 414) 221549) = 152058 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b414_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 414)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 414)) 221549) = 152058 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a414_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 414))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 414) 266275) = 57834 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b414_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 414)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 414)) 266275) = 57834 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a414_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 414))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 414) 186844) = 89404 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b414_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 414)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 414)) 186844) = 89404 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o414 : xone 414 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a414_0 b414_0 a414_1 b414_1 a414_2 b414_2
    a414_3 b414_3 a414_4 b414_4 a414_5 b414_5

theorem a415_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 415))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 415) 0) = 151424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b415_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 415)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 415)) 0) = 151424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a415_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 415))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 415) 305530) = 14780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b415_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 415)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 415)) 305530) = 14780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a415_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 415))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 415) 5604) = 145538 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b415_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 415)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 415)) 5604) = 145538 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a415_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 415))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 415) 221549) = 161361 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b415_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 415)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 415)) 221549) = 161361 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a415_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 415))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 415) 266275) = 265316 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b415_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 415)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 415)) 266275) = 265316 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a415_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 415))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 415) 186844) = 119316 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b415_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 415)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 415)) 186844) = 119316 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o415 : xone 415 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a415_0 b415_0 a415_1 b415_1 a415_2 b415_2
    a415_3 b415_3 a415_4 b415_4 a415_5 b415_5

end CFSG.KD.Fi24Pc.Ck

public section

namespace CFSG.KD.Fi24Pc.Ck

theorem x26 : CFSG.KD.Fi24Pc.xck (nat_lit 26) = true :=
  xck_of o208 (by quickRfl) o209 (by quickRfl) o210 (by quickRfl) o211 (by quickRfl)
    o212 (by quickRfl) o213 (by quickRfl) o214 (by quickRfl) o215 (by quickRfl)

theorem x27 : CFSG.KD.Fi24Pc.xck (nat_lit 27) = true :=
  xck_of o216 (by quickRfl) o217 (by quickRfl) o218 (by quickRfl) o219 (by quickRfl)
    o220 (by quickRfl) o221 (by quickRfl) o222 (by quickRfl) o223 (by quickRfl)

theorem x28 : CFSG.KD.Fi24Pc.xck (nat_lit 28) = true :=
  xck_of o224 (by quickRfl) o225 (by quickRfl) o226 (by quickRfl) o227 (by quickRfl)
    o228 (by quickRfl) o229 (by quickRfl) o230 (by quickRfl) o231 (by quickRfl)

theorem x29 : CFSG.KD.Fi24Pc.xck (nat_lit 29) = true :=
  xck_of o232 (by quickRfl) o233 (by quickRfl) o234 (by quickRfl) o235 (by quickRfl)
    o236 (by quickRfl) o237 (by quickRfl) o238 (by quickRfl) o239 (by quickRfl)

theorem x30 : CFSG.KD.Fi24Pc.xck (nat_lit 30) = true :=
  xck_of o240 (by quickRfl) o241 (by quickRfl) o242 (by quickRfl) o243 (by quickRfl)
    o244 (by quickRfl) o245 (by quickRfl) o246 (by quickRfl) o247 (by quickRfl)

theorem x31 : CFSG.KD.Fi24Pc.xck (nat_lit 31) = true :=
  xck_of o248 (by quickRfl) o249 (by quickRfl) o250 (by quickRfl) o251 (by quickRfl)
    o252 (by quickRfl) o253 (by quickRfl) o254 (by quickRfl) o255 (by quickRfl)

theorem x32 : CFSG.KD.Fi24Pc.xck (nat_lit 32) = true :=
  xck_of o256 (by quickRfl) o257 (by quickRfl) o258 (by quickRfl) o259 (by quickRfl)
    o260 (by quickRfl) o261 (by quickRfl) o262 (by quickRfl) o263 (by quickRfl)

theorem x33 : CFSG.KD.Fi24Pc.xck (nat_lit 33) = true :=
  xck_of o264 (by quickRfl) o265 (by quickRfl) o266 (by quickRfl) o267 (by quickRfl)
    o268 (by quickRfl) o269 (by quickRfl) o270 (by quickRfl) o271 (by quickRfl)

theorem x34 : CFSG.KD.Fi24Pc.xck (nat_lit 34) = true :=
  xck_of o272 (by quickRfl) o273 (by quickRfl) o274 (by quickRfl) o275 (by quickRfl)
    o276 (by quickRfl) o277 (by quickRfl) o278 (by quickRfl) o279 (by quickRfl)

theorem x35 : CFSG.KD.Fi24Pc.xck (nat_lit 35) = true :=
  xck_of o280 (by quickRfl) o281 (by quickRfl) o282 (by quickRfl) o283 (by quickRfl)
    o284 (by quickRfl) o285 (by quickRfl) o286 (by quickRfl) o287 (by quickRfl)

theorem x36 : CFSG.KD.Fi24Pc.xck (nat_lit 36) = true :=
  xck_of o288 (by quickRfl) o289 (by quickRfl) o290 (by quickRfl) o291 (by quickRfl)
    o292 (by quickRfl) o293 (by quickRfl) o294 (by quickRfl) o295 (by quickRfl)

theorem x37 : CFSG.KD.Fi24Pc.xck (nat_lit 37) = true :=
  xck_of o296 (by quickRfl) o297 (by quickRfl) o298 (by quickRfl) o299 (by quickRfl)
    o300 (by quickRfl) o301 (by quickRfl) o302 (by quickRfl) o303 (by quickRfl)

theorem x38 : CFSG.KD.Fi24Pc.xck (nat_lit 38) = true :=
  xck_of o304 (by quickRfl) o305 (by quickRfl) o306 (by quickRfl) o307 (by quickRfl)
    o308 (by quickRfl) o309 (by quickRfl) o310 (by quickRfl) o311 (by quickRfl)

theorem x39 : CFSG.KD.Fi24Pc.xck (nat_lit 39) = true :=
  xck_of o312 (by quickRfl) o313 (by quickRfl) o314 (by quickRfl) o315 (by quickRfl)
    o316 (by quickRfl) o317 (by quickRfl) o318 (by quickRfl) o319 (by quickRfl)

theorem x40 : CFSG.KD.Fi24Pc.xck (nat_lit 40) = true :=
  xck_of o320 (by quickRfl) o321 (by quickRfl) o322 (by quickRfl) o323 (by quickRfl)
    o324 (by quickRfl) o325 (by quickRfl) o326 (by quickRfl) o327 (by quickRfl)

theorem x41 : CFSG.KD.Fi24Pc.xck (nat_lit 41) = true :=
  xck_of o328 (by quickRfl) o329 (by quickRfl) o330 (by quickRfl) o331 (by quickRfl)
    o332 (by quickRfl) o333 (by quickRfl) o334 (by quickRfl) o335 (by quickRfl)

theorem x42 : CFSG.KD.Fi24Pc.xck (nat_lit 42) = true :=
  xck_of o336 (by quickRfl) o337 (by quickRfl) o338 (by quickRfl) o339 (by quickRfl)
    o340 (by quickRfl) o341 (by quickRfl) o342 (by quickRfl) o343 (by quickRfl)

theorem x43 : CFSG.KD.Fi24Pc.xck (nat_lit 43) = true :=
  xck_of o344 (by quickRfl) o345 (by quickRfl) o346 (by quickRfl) o347 (by quickRfl)
    o348 (by quickRfl) o349 (by quickRfl) o350 (by quickRfl) o351 (by quickRfl)

theorem x44 : CFSG.KD.Fi24Pc.xck (nat_lit 44) = true :=
  xck_of o352 (by quickRfl) o353 (by quickRfl) o354 (by quickRfl) o355 (by quickRfl)
    o356 (by quickRfl) o357 (by quickRfl) o358 (by quickRfl) o359 (by quickRfl)

theorem x45 : CFSG.KD.Fi24Pc.xck (nat_lit 45) = true :=
  xck_of o360 (by quickRfl) o361 (by quickRfl) o362 (by quickRfl) o363 (by quickRfl)
    o364 (by quickRfl) o365 (by quickRfl) o366 (by quickRfl) o367 (by quickRfl)

theorem x46 : CFSG.KD.Fi24Pc.xck (nat_lit 46) = true :=
  xck_of o368 (by quickRfl) o369 (by quickRfl) o370 (by quickRfl) o371 (by quickRfl)
    o372 (by quickRfl) o373 (by quickRfl) o374 (by quickRfl) o375 (by quickRfl)

theorem x47 : CFSG.KD.Fi24Pc.xck (nat_lit 47) = true :=
  xck_of o376 (by quickRfl) o377 (by quickRfl) o378 (by quickRfl) o379 (by quickRfl)
    o380 (by quickRfl) o381 (by quickRfl) o382 (by quickRfl) o383 (by quickRfl)

theorem x48 : CFSG.KD.Fi24Pc.xck (nat_lit 48) = true :=
  xck_of o384 (by quickRfl) o385 (by quickRfl) o386 (by quickRfl) o387 (by quickRfl)
    o388 (by quickRfl) o389 (by quickRfl) o390 (by quickRfl) o391 (by quickRfl)

theorem x49 : CFSG.KD.Fi24Pc.xck (nat_lit 49) = true :=
  xck_of o392 (by quickRfl) o393 (by quickRfl) o394 (by quickRfl) o395 (by quickRfl)
    o396 (by quickRfl) o397 (by quickRfl) o398 (by quickRfl) o399 (by quickRfl)

theorem x50 : CFSG.KD.Fi24Pc.xck (nat_lit 50) = true :=
  xck_of o400 (by quickRfl) o401 (by quickRfl) o402 (by quickRfl) o403 (by quickRfl)
    o404 (by quickRfl) o405 (by quickRfl) o406 (by quickRfl) o407 (by quickRfl)

theorem x51 : CFSG.KD.Fi24Pc.xck (nat_lit 51) = true :=
  xck_of o408 (by quickRfl) o409 (by quickRfl) o410 (by quickRfl) o411 (by quickRfl)
    o412 (by quickRfl) o413 (by quickRfl) o414 (by quickRfl) o415 (by quickRfl)

end CFSG.KD.Fi24Pc.Ck

end
