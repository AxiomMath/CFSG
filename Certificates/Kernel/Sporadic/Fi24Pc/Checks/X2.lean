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

theorem a416_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 416))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 416) 0) = 107359 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b416_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 416)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 416)) 0) = 107359 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a416_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 416))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 416) 305530) = 304236 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b416_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 416)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 416)) 305530) = 304236 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a416_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 416))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 416) 5604) = 7191 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b416_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 416)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 416)) 5604) = 7191 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a416_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 416))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 416) 221549) = 8984 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b416_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 416)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 416)) 221549) = 8984 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a416_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 416))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 416) 266275) = 79808 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b416_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 416)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 416)) 266275) = 79808 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a416_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 416))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 416) 186844) = 193063 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b416_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 416)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 416)) 186844) = 193063 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o416 : xone 416 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a416_0 b416_0 a416_1 b416_1 a416_2 b416_2
    a416_3 b416_3 a416_4 b416_4 a416_5 b416_5

theorem a417_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 417))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 417) 0) = 283504 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b417_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 417)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 417)) 0) = 283504 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a417_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 417))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 417) 305530) = 238581 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b417_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 417)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 417)) 305530) = 238581 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a417_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 417))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 417) 5604) = 5582 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b417_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 417)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 417)) 5604) = 5582 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a417_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 417))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 417) 221549) = 260989 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b417_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 417)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 417)) 221549) = 260989 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a417_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 417))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 417) 266275) = 235182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b417_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 417)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 417)) 266275) = 235182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a417_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 417))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 417) 186844) = 65707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b417_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 417)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 417)) 186844) = 65707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o417 : xone 417 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a417_0 b417_0 a417_1 b417_1 a417_2 b417_2
    a417_3 b417_3 a417_4 b417_4 a417_5 b417_5

theorem a418_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 418))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 418) 0) = 297717 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b418_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 418)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 418)) 0) = 297717 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a418_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 418))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 418) 305530) = 144720 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b418_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 418)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 418)) 305530) = 144720 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a418_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 418))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 418) 5604) = 256137 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b418_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 418)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 418)) 5604) = 256137 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a418_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 418))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 418) 221549) = 81352 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b418_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 418)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 418)) 221549) = 81352 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a418_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 418))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 418) 266275) = 42289 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b418_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 418)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 418)) 266275) = 42289 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a418_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 418))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 418) 186844) = 109301 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b418_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 418)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 418)) 186844) = 109301 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o418 : xone 418 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a418_0 b418_0 a418_1 b418_1 a418_2 b418_2
    a418_3 b418_3 a418_4 b418_4 a418_5 b418_5

theorem a419_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 419))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 419) 0) = 237647 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b419_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 419)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 419)) 0) = 237647 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a419_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 419))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 419) 305530) = 101824 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b419_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 419)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 419)) 305530) = 101824 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a419_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 419))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 419) 5604) = 92434 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b419_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 419)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 419)) 5604) = 92434 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a419_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 419))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 419) 221549) = 12359 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b419_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 419)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 419)) 221549) = 12359 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a419_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 419))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 419) 266275) = 160104 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b419_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 419)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 419)) 266275) = 160104 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a419_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 419))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 419) 186844) = 101063 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b419_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 419)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 419)) 186844) = 101063 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o419 : xone 419 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a419_0 b419_0 a419_1 b419_1 a419_2 b419_2
    a419_3 b419_3 a419_4 b419_4 a419_5 b419_5

theorem a420_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 420))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 420) 0) = 270440 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b420_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 420)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 420)) 0) = 270440 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a420_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 420))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 420) 305530) = 202855 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b420_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 420)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 420)) 305530) = 202855 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a420_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 420))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 420) 5604) = 191207 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b420_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 420)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 420)) 5604) = 191207 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a420_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 420))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 420) 221549) = 243452 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b420_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 420)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 420)) 221549) = 243452 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a420_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 420))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 420) 266275) = 213341 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b420_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 420)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 420)) 266275) = 213341 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a420_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 420))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 420) 186844) = 145723 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b420_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 420)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 420)) 186844) = 145723 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o420 : xone 420 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a420_0 b420_0 a420_1 b420_1 a420_2 b420_2
    a420_3 b420_3 a420_4 b420_4 a420_5 b420_5

theorem a421_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 421))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 421) 0) = 304255 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b421_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 421)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 421)) 0) = 304255 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a421_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 421))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 421) 305530) = 249252 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b421_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 421)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 421)) 305530) = 249252 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a421_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 421))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 421) 5604) = 281765 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b421_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 421)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 421)) 5604) = 281765 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a421_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 421))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 421) 221549) = 147829 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b421_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 421)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 421)) 221549) = 147829 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a421_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 421))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 421) 266275) = 130620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b421_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 421)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 421)) 266275) = 130620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a421_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 421))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 421) 186844) = 161697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b421_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 421)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 421)) 186844) = 161697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o421 : xone 421 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a421_0 b421_0 a421_1 b421_1 a421_2 b421_2
    a421_3 b421_3 a421_4 b421_4 a421_5 b421_5

theorem a422_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 422))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 422) 0) = 270066 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b422_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 422)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 422)) 0) = 270066 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a422_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 422))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 422) 305530) = 101660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b422_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 422)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 422)) 305530) = 101660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a422_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 422))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 422) 5604) = 288246 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b422_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 422)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 422)) 5604) = 288246 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a422_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 422))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 422) 221549) = 3335 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b422_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 422)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 422)) 221549) = 3335 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a422_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 422))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 422) 266275) = 18704 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b422_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 422)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 422)) 266275) = 18704 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a422_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 422))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 422) 186844) = 242699 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b422_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 422)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 422)) 186844) = 242699 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o422 : xone 422 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a422_0 b422_0 a422_1 b422_1 a422_2 b422_2
    a422_3 b422_3 a422_4 b422_4 a422_5 b422_5

theorem a423_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 423))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 423) 0) = 47793 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b423_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 423)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 423)) 0) = 47793 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a423_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 423))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 423) 305530) = 138433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b423_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 423)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 423)) 305530) = 138433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a423_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 423))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 423) 5604) = 304675 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b423_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 423)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 423)) 5604) = 304675 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a423_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 423))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 423) 221549) = 181478 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b423_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 423)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 423)) 221549) = 181478 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a423_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 423))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 423) 266275) = 157963 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b423_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 423)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 423)) 266275) = 157963 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a423_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 423))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 423) 186844) = 73609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b423_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 423)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 423)) 186844) = 73609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o423 : xone 423 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a423_0 b423_0 a423_1 b423_1 a423_2 b423_2
    a423_3 b423_3 a423_4 b423_4 a423_5 b423_5

theorem a424_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 424))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 424) 0) = 9067 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b424_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 424)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 424)) 0) = 9067 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a424_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 424))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 424) 305530) = 104538 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b424_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 424)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 424)) 305530) = 104538 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a424_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 424))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 424) 5604) = 26939 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b424_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 424)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 424)) 5604) = 26939 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a424_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 424))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 424) 221549) = 231662 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b424_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 424)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 424)) 221549) = 231662 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a424_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 424))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 424) 266275) = 6095 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b424_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 424)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 424)) 266275) = 6095 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a424_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 424))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 424) 186844) = 166624 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b424_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 424)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 424)) 186844) = 166624 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o424 : xone 424 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a424_0 b424_0 a424_1 b424_1 a424_2 b424_2
    a424_3 b424_3 a424_4 b424_4 a424_5 b424_5

theorem a425_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 425))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 425) 0) = 246588 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b425_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 425)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 425)) 0) = 246588 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a425_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 425))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 425) 305530) = 21001 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b425_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 425)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 425)) 305530) = 21001 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a425_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 425))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 425) 5604) = 187906 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b425_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 425)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 425)) 5604) = 187906 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a425_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 425))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 425) 221549) = 11756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b425_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 425)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 425)) 221549) = 11756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a425_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 425))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 425) 266275) = 230626 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b425_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 425)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 425)) 266275) = 230626 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a425_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 425))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 425) 186844) = 187056 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b425_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 425)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 425)) 186844) = 187056 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o425 : xone 425 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a425_0 b425_0 a425_1 b425_1 a425_2 b425_2
    a425_3 b425_3 a425_4 b425_4 a425_5 b425_5

theorem a426_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 426))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 426) 0) = 227568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b426_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 426)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 426)) 0) = 227568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a426_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 426))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 426) 305530) = 281263 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b426_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 426)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 426)) 305530) = 281263 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a426_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 426))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 426) 5604) = 173352 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b426_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 426)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 426)) 5604) = 173352 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a426_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 426))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 426) 221549) = 60304 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b426_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 426)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 426)) 221549) = 60304 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a426_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 426))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 426) 266275) = 147235 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b426_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 426)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 426)) 266275) = 147235 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a426_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 426))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 426) 186844) = 231278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b426_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 426)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 426)) 186844) = 231278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o426 : xone 426 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a426_0 b426_0 a426_1 b426_1 a426_2 b426_2
    a426_3 b426_3 a426_4 b426_4 a426_5 b426_5

theorem a427_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 427))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 427) 0) = 261221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b427_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 427)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 427)) 0) = 261221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a427_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 427))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 427) 305530) = 58426 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b427_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 427)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 427)) 305530) = 58426 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a427_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 427))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 427) 5604) = 54222 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b427_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 427)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 427)) 5604) = 54222 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a427_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 427))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 427) 221549) = 150934 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b427_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 427)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 427)) 221549) = 150934 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a427_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 427))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 427) 266275) = 212397 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b427_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 427)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 427)) 266275) = 212397 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a427_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 427))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 427) 186844) = 179139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b427_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 427)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 427)) 186844) = 179139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o427 : xone 427 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a427_0 b427_0 a427_1 b427_1 a427_2 b427_2
    a427_3 b427_3 a427_4 b427_4 a427_5 b427_5

theorem a428_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 428))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 428) 0) = 123124 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b428_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 428)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 428)) 0) = 123124 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a428_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 428))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 428) 305530) = 63328 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b428_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 428)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 428)) 305530) = 63328 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a428_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 428))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 428) 5604) = 37780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b428_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 428)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 428)) 5604) = 37780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a428_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 428))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 428) 221549) = 159128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b428_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 428)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 428)) 221549) = 159128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a428_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 428))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 428) 266275) = 119807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b428_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 428)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 428)) 266275) = 119807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a428_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 428))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 428) 186844) = 256732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b428_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 428)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 428)) 186844) = 256732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o428 : xone 428 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a428_0 b428_0 a428_1 b428_1 a428_2 b428_2
    a428_3 b428_3 a428_4 b428_4 a428_5 b428_5

theorem a429_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 429))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 429) 0) = 242179 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b429_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 429)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 429)) 0) = 242179 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a429_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 429))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 429) 305530) = 10959 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b429_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 429)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 429)) 305530) = 10959 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a429_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 429))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 429) 5604) = 144416 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b429_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 429)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 429)) 5604) = 144416 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a429_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 429))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 429) 221549) = 104627 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b429_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 429)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 429)) 221549) = 104627 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a429_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 429))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 429) 266275) = 33216 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b429_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 429)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 429)) 266275) = 33216 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a429_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 429))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 429) 186844) = 118997 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b429_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 429)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 429)) 186844) = 118997 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o429 : xone 429 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a429_0 b429_0 a429_1 b429_1 a429_2 b429_2
    a429_3 b429_3 a429_4 b429_4 a429_5 b429_5

theorem a430_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 430))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 430) 0) = 223312 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b430_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 430)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 430)) 0) = 223312 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a430_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 430))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 430) 305530) = 177691 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b430_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 430)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 430)) 305530) = 177691 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a430_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 430))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 430) 5604) = 93134 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b430_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 430)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 430)) 5604) = 93134 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a430_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 430))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 430) 221549) = 154012 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b430_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 430)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 430)) 221549) = 154012 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a430_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 430))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 430) 266275) = 168027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b430_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 430)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 430)) 266275) = 168027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a430_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 430))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 430) 186844) = 45335 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b430_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 430)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 430)) 186844) = 45335 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o430 : xone 430 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a430_0 b430_0 a430_1 b430_1 a430_2 b430_2
    a430_3 b430_3 a430_4 b430_4 a430_5 b430_5

theorem a431_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 431))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 431) 0) = 179005 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b431_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 431)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 431)) 0) = 179005 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a431_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 431))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 431) 305530) = 84709 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b431_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 431)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 431)) 305530) = 84709 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a431_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 431))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 431) 5604) = 114274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b431_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 431)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 431)) 5604) = 114274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a431_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 431))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 431) 221549) = 274881 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b431_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 431)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 431)) 221549) = 274881 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a431_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 431))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 431) 266275) = 155844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b431_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 431)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 431)) 266275) = 155844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a431_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 431))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 431) 186844) = 160460 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b431_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 431)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 431)) 186844) = 160460 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o431 : xone 431 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a431_0 b431_0 a431_1 b431_1 a431_2 b431_2
    a431_3 b431_3 a431_4 b431_4 a431_5 b431_5

theorem a432_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 432))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 432) 0) = 200861 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b432_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 432)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 432)) 0) = 200861 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a432_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 432))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 432) 305530) = 45858 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b432_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 432)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 432)) 305530) = 45858 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a432_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 432))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 432) 5604) = 70728 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b432_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 432)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 432)) 5604) = 70728 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a432_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 432))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 432) 221549) = 147516 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b432_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 432)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 432)) 221549) = 147516 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a432_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 432))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 432) 266275) = 303295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b432_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 432)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 432)) 266275) = 303295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a432_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 432))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 432) 186844) = 273666 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b432_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 432)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 432)) 186844) = 273666 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o432 : xone 432 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a432_0 b432_0 a432_1 b432_1 a432_2 b432_2
    a432_3 b432_3 a432_4 b432_4 a432_5 b432_5

theorem a433_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 433))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 433) 0) = 97234 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b433_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 433)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 433)) 0) = 97234 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a433_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 433))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 433) 305530) = 210789 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b433_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 433)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 433)) 305530) = 210789 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a433_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 433))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 433) 5604) = 223075 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b433_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 433)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 433)) 5604) = 223075 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a433_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 433))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 433) 221549) = 146940 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b433_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 433)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 433)) 221549) = 146940 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a433_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 433))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 433) 266275) = 224056 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b433_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 433)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 433)) 266275) = 224056 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a433_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 433))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 433) 186844) = 218019 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b433_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 433)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 433)) 186844) = 218019 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o433 : xone 433 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a433_0 b433_0 a433_1 b433_1 a433_2 b433_2
    a433_3 b433_3 a433_4 b433_4 a433_5 b433_5

theorem a434_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 434))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 434) 0) = 88581 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b434_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 434)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 434)) 0) = 88581 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a434_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 434))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 434) 305530) = 301882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b434_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 434)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 434)) 305530) = 301882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a434_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 434))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 434) 5604) = 117927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b434_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 434)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 434)) 5604) = 117927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a434_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 434))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 434) 221549) = 43959 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b434_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 434)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 434)) 221549) = 43959 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a434_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 434))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 434) 266275) = 184217 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b434_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 434)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 434)) 266275) = 184217 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a434_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 434))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 434) 186844) = 116763 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b434_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 434)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 434)) 186844) = 116763 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o434 : xone 434 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a434_0 b434_0 a434_1 b434_1 a434_2 b434_2
    a434_3 b434_3 a434_4 b434_4 a434_5 b434_5

theorem a435_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 435))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 435) 0) = 85010 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b435_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 435)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 435)) 0) = 85010 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a435_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 435))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 435) 305530) = 92811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b435_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 435)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 435)) 305530) = 92811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a435_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 435))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 435) 5604) = 97604 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b435_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 435)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 435)) 5604) = 97604 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a435_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 435))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 435) 221549) = 286306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b435_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 435)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 435)) 221549) = 286306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a435_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 435))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 435) 266275) = 210216 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b435_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 435)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 435)) 266275) = 210216 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a435_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 435))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 435) 186844) = 179610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b435_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 435)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 435)) 186844) = 179610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o435 : xone 435 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a435_0 b435_0 a435_1 b435_1 a435_2 b435_2
    a435_3 b435_3 a435_4 b435_4 a435_5 b435_5

theorem a436_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 436))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 436) 0) = 145384 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b436_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 436)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 436)) 0) = 145384 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a436_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 436))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 436) 305530) = 185990 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b436_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 436)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 436)) 305530) = 185990 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a436_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 436))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 436) 5604) = 169264 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b436_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 436)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 436)) 5604) = 169264 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a436_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 436))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 436) 221549) = 254061 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b436_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 436)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 436)) 221549) = 254061 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a436_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 436))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 436) 266275) = 262237 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b436_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 436)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 436)) 266275) = 262237 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a436_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 436))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 436) 186844) = 199215 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b436_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 436)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 436)) 186844) = 199215 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o436 : xone 436 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a436_0 b436_0 a436_1 b436_1 a436_2 b436_2
    a436_3 b436_3 a436_4 b436_4 a436_5 b436_5

theorem a437_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 437))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 437) 0) = 238136 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b437_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 437)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 437)) 0) = 238136 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a437_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 437))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 437) 305530) = 285768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b437_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 437)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 437)) 305530) = 285768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a437_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 437))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 437) 5604) = 256277 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b437_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 437)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 437)) 5604) = 256277 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a437_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 437))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 437) 221549) = 211927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b437_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 437)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 437)) 221549) = 211927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a437_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 437))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 437) 266275) = 280365 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b437_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 437)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 437)) 266275) = 280365 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a437_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 437))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 437) 186844) = 101534 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b437_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 437)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 437)) 186844) = 101534 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o437 : xone 437 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a437_0 b437_0 a437_1 b437_1 a437_2 b437_2
    a437_3 b437_3 a437_4 b437_4 a437_5 b437_5

theorem a438_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 438))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 438) 0) = 54055 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b438_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 438)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 438)) 0) = 54055 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a438_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 438))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 438) 305530) = 275107 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b438_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 438)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 438)) 305530) = 275107 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a438_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 438))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 438) 5604) = 55235 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b438_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 438)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 438)) 5604) = 55235 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a438_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 438))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 438) 221549) = 114941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b438_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 438)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 438)) 221549) = 114941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a438_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 438))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 438) 266275) = 305923 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b438_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 438)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 438)) 266275) = 305923 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a438_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 438))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 438) 186844) = 181646 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b438_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 438)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 438)) 186844) = 181646 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o438 : xone 438 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a438_0 b438_0 a438_1 b438_1 a438_2 b438_2
    a438_3 b438_3 a438_4 b438_4 a438_5 b438_5

theorem a439_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 439))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 439) 0) = 8663 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b439_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 439)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 439)) 0) = 8663 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a439_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 439))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 439) 305530) = 139239 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b439_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 439)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 439)) 305530) = 139239 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a439_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 439))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 439) 5604) = 88070 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b439_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 439)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 439)) 5604) = 88070 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a439_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 439))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 439) 221549) = 169040 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b439_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 439)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 439)) 221549) = 169040 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a439_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 439))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 439) 266275) = 68777 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b439_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 439)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 439)) 266275) = 68777 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a439_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 439))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 439) 186844) = 128016 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b439_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 439)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 439)) 186844) = 128016 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o439 : xone 439 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a439_0 b439_0 a439_1 b439_1 a439_2 b439_2
    a439_3 b439_3 a439_4 b439_4 a439_5 b439_5

theorem a440_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 440))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 440) 0) = 256877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b440_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 440)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 440)) 0) = 256877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a440_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 440))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 440) 305530) = 122445 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b440_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 440)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 440)) 305530) = 122445 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a440_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 440))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 440) 5604) = 251555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b440_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 440)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 440)) 5604) = 251555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a440_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 440))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 440) 221549) = 837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b440_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 440)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 440)) 221549) = 837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a440_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 440))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 440) 266275) = 3953 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b440_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 440)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 440)) 266275) = 3953 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a440_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 440))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 440) 186844) = 148597 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b440_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 440)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 440)) 186844) = 148597 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o440 : xone 440 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a440_0 b440_0 a440_1 b440_1 a440_2 b440_2
    a440_3 b440_3 a440_4 b440_4 a440_5 b440_5

theorem a441_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 441))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 441) 0) = 74368 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b441_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 441)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 441)) 0) = 74368 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a441_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 441))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 441) 305530) = 96212 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b441_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 441)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 441)) 305530) = 96212 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a441_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 441))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 441) 5604) = 111955 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b441_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 441)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 441)) 5604) = 111955 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a441_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 441))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 441) 221549) = 225679 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b441_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 441)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 441)) 221549) = 225679 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a441_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 441))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 441) 266275) = 281451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b441_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 441)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 441)) 266275) = 281451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a441_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 441))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 441) 186844) = 138780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b441_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 441)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 441)) 186844) = 138780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o441 : xone 441 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a441_0 b441_0 a441_1 b441_1 a441_2 b441_2
    a441_3 b441_3 a441_4 b441_4 a441_5 b441_5

theorem a442_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 442))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 442) 0) = 223087 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b442_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 442)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 442)) 0) = 223087 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a442_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 442))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 442) 305530) = 106841 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b442_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 442)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 442)) 305530) = 106841 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a442_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 442))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 442) 5604) = 213010 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b442_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 442)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 442)) 5604) = 213010 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a442_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 442))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 442) 221549) = 54705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b442_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 442)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 442)) 221549) = 54705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a442_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 442))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 442) 266275) = 198702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b442_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 442)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 442)) 266275) = 198702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a442_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 442))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 442) 186844) = 146338 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b442_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 442)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 442)) 186844) = 146338 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o442 : xone 442 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a442_0 b442_0 a442_1 b442_1 a442_2 b442_2
    a442_3 b442_3 a442_4 b442_4 a442_5 b442_5

theorem a443_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 443))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 443) 0) = 250137 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b443_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 443)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 443)) 0) = 250137 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a443_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 443))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 443) 305530) = 83852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b443_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 443)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 443)) 305530) = 83852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a443_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 443))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 443) 5604) = 196548 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b443_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 443)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 443)) 5604) = 196548 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a443_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 443))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 443) 221549) = 191317 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b443_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 443)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 443)) 221549) = 191317 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a443_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 443))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 443) 266275) = 230917 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b443_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 443)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 443)) 266275) = 230917 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a443_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 443))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 443) 186844) = 102771 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b443_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 443)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 443)) 186844) = 102771 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o443 : xone 443 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a443_0 b443_0 a443_1 b443_1 a443_2 b443_2
    a443_3 b443_3 a443_4 b443_4 a443_5 b443_5

theorem a444_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 444))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 444) 0) = 247338 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b444_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 444)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 444)) 0) = 247338 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a444_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 444))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 444) 305530) = 204508 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b444_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 444)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 444)) 305530) = 204508 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a444_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 444))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 444) 5604) = 274098 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b444_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 444)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 444)) 5604) = 274098 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a444_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 444))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 444) 221549) = 285535 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b444_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 444)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 444)) 221549) = 285535 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a444_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 444))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 444) 266275) = 139013 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b444_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 444)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 444)) 266275) = 139013 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a444_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 444))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 444) 186844) = 64577 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b444_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 444)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 444)) 186844) = 64577 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o444 : xone 444 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a444_0 b444_0 a444_1 b444_1 a444_2 b444_2
    a444_3 b444_3 a444_4 b444_4 a444_5 b444_5

theorem a445_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 445))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 445) 0) = 50160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b445_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 445)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 445)) 0) = 50160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a445_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 445))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 445) 305530) = 42964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b445_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 445)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 445)) 305530) = 42964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a445_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 445))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 445) 5604) = 254969 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b445_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 445)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 445)) 5604) = 254969 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a445_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 445))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 445) 221549) = 210045 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b445_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 445)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 445)) 221549) = 210045 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a445_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 445))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 445) 266275) = 289126 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b445_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 445)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 445)) 266275) = 289126 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a445_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 445))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 445) 186844) = 259081 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b445_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 445)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 445)) 186844) = 259081 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o445 : xone 445 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a445_0 b445_0 a445_1 b445_1 a445_2 b445_2
    a445_3 b445_3 a445_4 b445_4 a445_5 b445_5

theorem a446_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 446))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 446) 0) = 252731 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b446_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 446)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 446)) 0) = 252731 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a446_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 446))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 446) 305530) = 47633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b446_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 446)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 446)) 305530) = 47633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a446_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 446))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 446) 5604) = 237614 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b446_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 446)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 446)) 5604) = 237614 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a446_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 446))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 446) 221549) = 279356 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b446_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 446)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 446)) 221549) = 279356 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a446_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 446))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 446) 266275) = 97852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b446_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 446)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 446)) 266275) = 97852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a446_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 446))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 446) 186844) = 180750 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b446_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 446)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 446)) 186844) = 180750 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o446 : xone 446 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a446_0 b446_0 a446_1 b446_1 a446_2 b446_2
    a446_3 b446_3 a446_4 b446_4 a446_5 b446_5

theorem a447_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 447))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 447) 0) = 4092 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b447_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 447)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 447)) 0) = 4092 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a447_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 447))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 447) 305530) = 226787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b447_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 447)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 447)) 305530) = 226787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a447_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 447))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 447) 5604) = 134696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b447_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 447)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 447)) 5604) = 134696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a447_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 447))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 447) 221549) = 278155 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b447_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 447)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 447)) 221549) = 278155 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a447_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 447))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 447) 266275) = 237365 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b447_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 447)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 447)) 266275) = 237365 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a447_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 447))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 447) 186844) = 258307 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b447_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 447)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 447)) 186844) = 258307 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o447 : xone 447 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a447_0 b447_0 a447_1 b447_1 a447_2 b447_2
    a447_3 b447_3 a447_4 b447_4 a447_5 b447_5

theorem a448_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 448))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 448) 0) = 269212 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b448_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 448)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 448)) 0) = 269212 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a448_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 448))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 448) 305530) = 132029 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b448_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 448)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 448)) 305530) = 132029 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a448_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 448))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 448) 5604) = 200883 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b448_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 448)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 448)) 5604) = 200883 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a448_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 448))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 448) 221549) = 234767 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b448_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 448)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 448)) 221549) = 234767 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a448_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 448))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 448) 266275) = 178344 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b448_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 448)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 448)) 266275) = 178344 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a448_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 448))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 448) 186844) = 61017 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b448_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 448)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 448)) 186844) = 61017 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o448 : xone 448 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a448_0 b448_0 a448_1 b448_1 a448_2 b448_2
    a448_3 b448_3 a448_4 b448_4 a448_5 b448_5

theorem a449_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 449))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 449) 0) = 294559 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b449_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 449)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 449)) 0) = 294559 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a449_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 449))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 449) 305530) = 139868 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b449_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 449)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 449)) 305530) = 139868 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a449_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 449))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 449) 5604) = 193116 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b449_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 449)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 449)) 5604) = 193116 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a449_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 449))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 449) 221549) = 73366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b449_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 449)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 449)) 221549) = 73366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a449_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 449))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 449) 266275) = 273881 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b449_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 449)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 449)) 266275) = 273881 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a449_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 449))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 449) 186844) = 287084 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b449_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 449)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 449)) 186844) = 287084 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o449 : xone 449 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a449_0 b449_0 a449_1 b449_1 a449_2 b449_2
    a449_3 b449_3 a449_4 b449_4 a449_5 b449_5

theorem a450_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 450))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 450) 0) = 18751 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b450_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 450)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 450)) 0) = 18751 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a450_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 450))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 450) 305530) = 107613 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b450_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 450)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 450)) 305530) = 107613 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a450_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 450))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 450) 5604) = 217668 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b450_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 450)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 450)) 5604) = 217668 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a450_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 450))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 450) 221549) = 252015 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b450_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 450)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 450)) 221549) = 252015 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a450_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 450))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 450) 266275) = 288904 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b450_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 450)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 450)) 266275) = 288904 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a450_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 450))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 450) 186844) = 184852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b450_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 450)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 450)) 186844) = 184852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o450 : xone 450 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a450_0 b450_0 a450_1 b450_1 a450_2 b450_2
    a450_3 b450_3 a450_4 b450_4 a450_5 b450_5

theorem a451_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 451))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 451) 0) = 200563 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b451_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 451)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 451)) 0) = 200563 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a451_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 451))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 451) 305530) = 234022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b451_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 451)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 451)) 305530) = 234022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a451_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 451))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 451) 5604) = 268173 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b451_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 451)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 451)) 5604) = 268173 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a451_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 451))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 451) 221549) = 288527 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b451_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 451)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 451)) 221549) = 288527 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a451_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 451))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 451) 266275) = 39993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b451_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 451)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 451)) 266275) = 39993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a451_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 451))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 451) 186844) = 130865 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b451_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 451)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 451)) 186844) = 130865 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o451 : xone 451 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a451_0 b451_0 a451_1 b451_1 a451_2 b451_2
    a451_3 b451_3 a451_4 b451_4 a451_5 b451_5

theorem a452_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 452))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 452) 0) = 104307 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b452_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 452)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 452)) 0) = 104307 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a452_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 452))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 452) 305530) = 179567 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b452_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 452)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 452)) 305530) = 179567 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a452_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 452))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 452) 5604) = 186885 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b452_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 452)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 452)) 5604) = 186885 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a452_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 452))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 452) 221549) = 85072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b452_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 452)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 452)) 221549) = 85072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a452_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 452))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 452) 266275) = 255836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b452_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 452)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 452)) 266275) = 255836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a452_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 452))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 452) 186844) = 50409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b452_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 452)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 452)) 186844) = 50409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o452 : xone 452 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a452_0 b452_0 a452_1 b452_1 a452_2 b452_2
    a452_3 b452_3 a452_4 b452_4 a452_5 b452_5

theorem a453_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 453))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 453) 0) = 149684 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b453_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 453)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 453)) 0) = 149684 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a453_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 453))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 453) 305530) = 41610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b453_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 453)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 453)) 305530) = 41610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a453_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 453))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 453) 5604) = 136419 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b453_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 453)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 453)) 5604) = 136419 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a453_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 453))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 453) 221549) = 31442 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b453_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 453)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 453)) 221549) = 31442 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a453_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 453))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 453) 266275) = 270636 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b453_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 453)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 453)) 266275) = 270636 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a453_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 453))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 453) 186844) = 36643 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b453_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 453)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 453)) 186844) = 36643 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o453 : xone 453 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a453_0 b453_0 a453_1 b453_1 a453_2 b453_2
    a453_3 b453_3 a453_4 b453_4 a453_5 b453_5

theorem a454_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 454))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 454) 0) = 128081 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b454_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 454)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 454)) 0) = 128081 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a454_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 454))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 454) 305530) = 27697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b454_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 454)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 454)) 305530) = 27697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a454_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 454))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 454) 5604) = 253158 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b454_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 454)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 454)) 5604) = 253158 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a454_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 454))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 454) 221549) = 286443 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b454_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 454)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 454)) 221549) = 286443 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a454_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 454))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 454) 266275) = 84210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b454_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 454)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 454)) 266275) = 84210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a454_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 454))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 454) 186844) = 186923 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b454_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 454)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 454)) 186844) = 186923 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o454 : xone 454 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a454_0 b454_0 a454_1 b454_1 a454_2 b454_2
    a454_3 b454_3 a454_4 b454_4 a454_5 b454_5

theorem a455_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 455))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 455) 0) = 172294 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b455_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 455)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 455)) 0) = 172294 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a455_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 455))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 455) 305530) = 114846 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b455_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 455)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 455)) 305530) = 114846 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a455_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 455))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 455) 5604) = 290334 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b455_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 455)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 455)) 5604) = 290334 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a455_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 455))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 455) 221549) = 302994 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b455_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 455)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 455)) 221549) = 302994 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a455_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 455))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 455) 266275) = 246585 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b455_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 455)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 455)) 266275) = 246585 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a455_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 455))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 455) 186844) = 2756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b455_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 455)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 455)) 186844) = 2756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o455 : xone 455 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a455_0 b455_0 a455_1 b455_1 a455_2 b455_2
    a455_3 b455_3 a455_4 b455_4 a455_5 b455_5

theorem a456_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 456))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 456) 0) = 53000 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b456_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 456)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 456)) 0) = 53000 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a456_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 456))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 456) 305530) = 140284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b456_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 456)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 456)) 305530) = 140284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a456_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 456))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 456) 5604) = 45375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b456_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 456)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 456)) 5604) = 45375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a456_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 456))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 456) 221549) = 69085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b456_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 456)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 456)) 221549) = 69085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a456_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 456))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 456) 266275) = 114940 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b456_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 456)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 456)) 266275) = 114940 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a456_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 456))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 456) 186844) = 290776 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b456_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 456)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 456)) 186844) = 290776 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o456 : xone 456 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a456_0 b456_0 a456_1 b456_1 a456_2 b456_2
    a456_3 b456_3 a456_4 b456_4 a456_5 b456_5

theorem a457_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 457))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 457) 0) = 255600 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b457_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 457)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 457)) 0) = 255600 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a457_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 457))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 457) 305530) = 163869 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b457_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 457)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 457)) 305530) = 163869 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a457_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 457))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 457) 5604) = 161221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b457_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 457)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 457)) 5604) = 161221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a457_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 457))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 457) 221549) = 193320 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b457_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 457)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 457)) 221549) = 193320 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a457_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 457))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 457) 266275) = 64784 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b457_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 457)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 457)) 266275) = 64784 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a457_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 457))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 457) 186844) = 91104 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b457_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 457)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 457)) 186844) = 91104 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o457 : xone 457 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a457_0 b457_0 a457_1 b457_1 a457_2 b457_2
    a457_3 b457_3 a457_4 b457_4 a457_5 b457_5

theorem a458_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 458))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 458) 0) = 176496 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b458_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 458)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 458)) 0) = 176496 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a458_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 458))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 458) 305530) = 233948 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b458_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 458)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 458)) 305530) = 233948 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a458_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 458))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 458) 5604) = 100040 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b458_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 458)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 458)) 5604) = 100040 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a458_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 458))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 458) 221549) = 73112 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b458_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 458)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 458)) 221549) = 73112 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a458_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 458))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 458) 266275) = 165138 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b458_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 458)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 458)) 266275) = 165138 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a458_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 458))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 458) 186844) = 256626 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b458_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 458)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 458)) 186844) = 256626 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o458 : xone 458 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a458_0 b458_0 a458_1 b458_1 a458_2 b458_2
    a458_3 b458_3 a458_4 b458_4 a458_5 b458_5

theorem a459_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 459))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 459) 0) = 44498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b459_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 459)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 459)) 0) = 44498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a459_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 459))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 459) 305530) = 230704 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b459_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 459)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 459)) 305530) = 230704 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a459_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 459))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 459) 5604) = 2541 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b459_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 459)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 459)) 5604) = 2541 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a459_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 459))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 459) 221549) = 7076 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b459_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 459)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 459)) 221549) = 7076 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a459_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 459))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 459) 266275) = 143091 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b459_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 459)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 459)) 266275) = 143091 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a459_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 459))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 459) 186844) = 284198 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b459_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 459)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 459)) 186844) = 284198 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o459 : xone 459 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a459_0 b459_0 a459_1 b459_1 a459_2 b459_2
    a459_3 b459_3 a459_4 b459_4 a459_5 b459_5

theorem a460_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 460))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 460) 0) = 80875 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b460_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 460)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 460)) 0) = 80875 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a460_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 460))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 460) 305530) = 303565 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b460_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 460)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 460)) 305530) = 303565 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a460_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 460))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 460) 5604) = 259420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b460_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 460)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 460)) 5604) = 259420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a460_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 460))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 460) 221549) = 100393 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b460_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 460)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 460)) 221549) = 100393 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a460_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 460))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 460) 266275) = 232611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b460_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 460)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 460)) 266275) = 232611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a460_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 460))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 460) 186844) = 42946 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b460_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 460)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 460)) 186844) = 42946 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o460 : xone 460 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a460_0 b460_0 a460_1 b460_1 a460_2 b460_2
    a460_3 b460_3 a460_4 b460_4 a460_5 b460_5

theorem a461_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 461))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 461) 0) = 39570 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b461_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 461)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 461)) 0) = 39570 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a461_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 461))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 461) 305530) = 140669 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b461_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 461)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 461)) 305530) = 140669 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a461_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 461))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 461) 5604) = 22588 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b461_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 461)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 461)) 5604) = 22588 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a461_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 461))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 461) 221549) = 292201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b461_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 461)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 461)) 221549) = 292201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a461_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 461))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 461) 266275) = 181790 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b461_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 461)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 461)) 266275) = 181790 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a461_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 461))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 461) 186844) = 63660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b461_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 461)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 461)) 186844) = 63660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o461 : xone 461 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a461_0 b461_0 a461_1 b461_1 a461_2 b461_2
    a461_3 b461_3 a461_4 b461_4 a461_5 b461_5

theorem a462_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 462))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 462) 0) = 156560 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b462_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 462)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 462)) 0) = 156560 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a462_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 462))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 462) 305530) = 1468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b462_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 462)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 462)) 305530) = 1468 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a462_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 462))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 462) 5604) = 39718 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b462_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 462)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 462)) 5604) = 39718 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a462_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 462))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 462) 221549) = 293086 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b462_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 462)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 462)) 221549) = 293086 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a462_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 462))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 462) 266275) = 28180 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b462_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 462)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 462)) 266275) = 28180 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a462_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 462))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 462) 186844) = 157420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b462_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 462)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 462)) 186844) = 157420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o462 : xone 462 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a462_0 b462_0 a462_1 b462_1 a462_2 b462_2
    a462_3 b462_3 a462_4 b462_4 a462_5 b462_5

theorem a463_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 463))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 463) 0) = 33249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b463_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 463)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 463)) 0) = 33249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a463_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 463))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 463) 305530) = 94280 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b463_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 463)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 463)) 305530) = 94280 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a463_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 463))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 463) 5604) = 190137 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b463_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 463)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 463)) 5604) = 190137 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a463_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 463))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 463) 221549) = 216961 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b463_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 463)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 463)) 221549) = 216961 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a463_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 463))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 463) 266275) = 33519 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b463_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 463)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 463)) 266275) = 33519 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a463_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 463))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 463) 186844) = 130317 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b463_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 463)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 463)) 186844) = 130317 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o463 : xone 463 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a463_0 b463_0 a463_1 b463_1 a463_2 b463_2
    a463_3 b463_3 a463_4 b463_4 a463_5 b463_5

theorem a464_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 464))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 464) 0) = 301748 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b464_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 464)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 464)) 0) = 301748 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a464_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 464))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 464) 305530) = 259106 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b464_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 464)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 464)) 305530) = 259106 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a464_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 464))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 464) 5604) = 200844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b464_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 464)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 464)) 5604) = 200844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a464_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 464))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 464) 221549) = 142434 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b464_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 464)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 464)) 221549) = 142434 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a464_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 464))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 464) 266275) = 16746 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b464_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 464)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 464)) 266275) = 16746 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a464_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 464))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 464) 186844) = 199423 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b464_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 464)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 464)) 186844) = 199423 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o464 : xone 464 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a464_0 b464_0 a464_1 b464_1 a464_2 b464_2
    a464_3 b464_3 a464_4 b464_4 a464_5 b464_5

theorem a465_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 465))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 465) 0) = 4410 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b465_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 465)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 465)) 0) = 4410 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a465_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 465))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 465) 305530) = 147265 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b465_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 465)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 465)) 305530) = 147265 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a465_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 465))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 465) 5604) = 219951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b465_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 465)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 465)) 5604) = 219951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a465_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 465))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 465) 221549) = 236825 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b465_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 465)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 465)) 221549) = 236825 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a465_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 465))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 465) 266275) = 118928 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b465_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 465)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 465)) 266275) = 118928 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a465_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 465))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 465) 186844) = 10315 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b465_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 465)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 465)) 186844) = 10315 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o465 : xone 465 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a465_0 b465_0 a465_1 b465_1 a465_2 b465_2
    a465_3 b465_3 a465_4 b465_4 a465_5 b465_5

theorem a466_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 466))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 466) 0) = 256899 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b466_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 466)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 466)) 0) = 256899 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a466_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 466))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 466) 305530) = 134096 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b466_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 466)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 466)) 305530) = 134096 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a466_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 466))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 466) 5604) = 91573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b466_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 466)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 466)) 5604) = 91573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a466_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 466))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 466) 221549) = 3841 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b466_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 466)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 466)) 221549) = 3841 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a466_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 466))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 466) 266275) = 188789 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b466_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 466)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 466)) 266275) = 188789 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a466_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 466))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 466) 186844) = 228666 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b466_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 466)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 466)) 186844) = 228666 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o466 : xone 466 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a466_0 b466_0 a466_1 b466_1 a466_2 b466_2
    a466_3 b466_3 a466_4 b466_4 a466_5 b466_5

theorem a467_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 467))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 467) 0) = 301922 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b467_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 467)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 467)) 0) = 301922 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a467_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 467))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 467) 305530) = 189133 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b467_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 467)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 467)) 305530) = 189133 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a467_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 467))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 467) 5604) = 215361 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b467_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 467)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 467)) 5604) = 215361 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a467_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 467))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 467) 221549) = 205935 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b467_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 467)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 467)) 221549) = 205935 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a467_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 467))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 467) 266275) = 108413 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b467_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 467)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 467)) 266275) = 108413 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a467_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 467))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 467) 186844) = 191403 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b467_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 467)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 467)) 186844) = 191403 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o467 : xone 467 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a467_0 b467_0 a467_1 b467_1 a467_2 b467_2
    a467_3 b467_3 a467_4 b467_4 a467_5 b467_5

theorem a468_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 468))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 468) 0) = 275654 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b468_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 468)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 468)) 0) = 275654 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a468_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 468))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 468) 305530) = 81134 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b468_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 468)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 468)) 305530) = 81134 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a468_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 468))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 468) 5604) = 105470 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b468_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 468)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 468)) 5604) = 105470 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a468_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 468))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 468) 221549) = 98460 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b468_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 468)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 468)) 221549) = 98460 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a468_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 468))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 468) 266275) = 185086 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b468_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 468)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 468)) 266275) = 185086 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a468_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 468))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 468) 186844) = 305024 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b468_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 468)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 468)) 186844) = 305024 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o468 : xone 468 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a468_0 b468_0 a468_1 b468_1 a468_2 b468_2
    a468_3 b468_3 a468_4 b468_4 a468_5 b468_5

theorem a469_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 469))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 469) 0) = 201500 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b469_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 469)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 469)) 0) = 201500 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a469_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 469))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 469) 305530) = 237406 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b469_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 469)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 469)) 305530) = 237406 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a469_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 469))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 469) 5604) = 128053 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b469_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 469)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 469)) 5604) = 128053 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a469_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 469))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 469) 221549) = 228188 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b469_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 469)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 469)) 221549) = 228188 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a469_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 469))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 469) 266275) = 52352 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b469_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 469)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 469)) 266275) = 52352 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a469_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 469))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 469) 186844) = 82002 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b469_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 469)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 469)) 186844) = 82002 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o469 : xone 469 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a469_0 b469_0 a469_1 b469_1 a469_2 b469_2
    a469_3 b469_3 a469_4 b469_4 a469_5 b469_5

theorem a470_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 470))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 470) 0) = 160594 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b470_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 470)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 470)) 0) = 160594 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a470_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 470))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 470) 305530) = 63549 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b470_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 470)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 470)) 305530) = 63549 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a470_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 470))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 470) 5604) = 205976 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b470_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 470)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 470)) 5604) = 205976 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a470_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 470))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 470) 221549) = 49093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b470_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 470)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 470)) 221549) = 49093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a470_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 470))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 470) 266275) = 254599 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b470_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 470)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 470)) 266275) = 254599 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a470_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 470))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 470) 186844) = 89996 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b470_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 470)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 470)) 186844) = 89996 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o470 : xone 470 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a470_0 b470_0 a470_1 b470_1 a470_2 b470_2
    a470_3 b470_3 a470_4 b470_4 a470_5 b470_5

theorem a471_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 471))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 471) 0) = 244565 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b471_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 471)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 471)) 0) = 244565 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a471_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 471))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 471) 305530) = 169489 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b471_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 471)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 471)) 305530) = 169489 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a471_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 471))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 471) 5604) = 237120 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b471_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 471)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 471)) 5604) = 237120 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a471_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 471))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 471) 221549) = 141481 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b471_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 471)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 471)) 221549) = 141481 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a471_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 471))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 471) 266275) = 222681 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b471_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 471)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 471)) 266275) = 222681 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a471_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 471))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 471) 186844) = 95316 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b471_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 471)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 471)) 186844) = 95316 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o471 : xone 471 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a471_0 b471_0 a471_1 b471_1 a471_2 b471_2
    a471_3 b471_3 a471_4 b471_4 a471_5 b471_5

theorem a472_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 472))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 472) 0) = 52240 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b472_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 472)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 472)) 0) = 52240 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a472_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 472))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 472) 305530) = 37026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b472_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 472)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 472)) 305530) = 37026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a472_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 472))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 472) 5604) = 185451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b472_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 472)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 472)) 5604) = 185451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a472_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 472))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 472) 221549) = 105893 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b472_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 472)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 472)) 221549) = 105893 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a472_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 472))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 472) 266275) = 44638 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b472_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 472)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 472)) 266275) = 44638 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a472_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 472))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 472) 186844) = 258488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b472_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 472)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 472)) 186844) = 258488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o472 : xone 472 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a472_0 b472_0 a472_1 b472_1 a472_2 b472_2
    a472_3 b472_3 a472_4 b472_4 a472_5 b472_5

theorem a473_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 473))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 473) 0) = 103747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b473_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 473)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 473)) 0) = 103747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a473_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 473))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 473) 305530) = 208335 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b473_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 473)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 473)) 305530) = 208335 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a473_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 473))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 473) 5604) = 4875 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b473_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 473)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 473)) 5604) = 4875 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a473_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 473))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 473) 221549) = 276579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b473_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 473)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 473)) 221549) = 276579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a473_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 473))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 473) 266275) = 128290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b473_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 473)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 473)) 266275) = 128290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a473_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 473))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 473) 186844) = 282836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b473_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 473)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 473)) 186844) = 282836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o473 : xone 473 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a473_0 b473_0 a473_1 b473_1 a473_2 b473_2
    a473_3 b473_3 a473_4 b473_4 a473_5 b473_5

theorem a474_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 474))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 474) 0) = 94394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b474_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 474)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 474)) 0) = 94394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a474_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 474))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 474) 305530) = 263759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b474_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 474)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 474)) 305530) = 263759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a474_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 474))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 474) 5604) = 137431 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b474_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 474)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 474)) 5604) = 137431 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a474_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 474))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 474) 221549) = 97837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b474_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 474)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 474)) 221549) = 97837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a474_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 474))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 474) 266275) = 152653 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b474_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 474)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 474)) 266275) = 152653 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a474_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 474))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 474) 186844) = 195197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b474_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 474)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 474)) 186844) = 195197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o474 : xone 474 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a474_0 b474_0 a474_1 b474_1 a474_2 b474_2
    a474_3 b474_3 a474_4 b474_4 a474_5 b474_5

theorem a475_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 475))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 475) 0) = 270424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b475_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 475)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 475)) 0) = 270424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a475_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 475))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 475) 305530) = 257290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b475_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 475)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 475)) 305530) = 257290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a475_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 475))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 475) 5604) = 2205 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b475_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 475)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 475)) 5604) = 2205 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a475_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 475))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 475) 221549) = 78494 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b475_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 475)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 475)) 221549) = 78494 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a475_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 475))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 475) 266275) = 147603 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b475_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 475)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 475)) 266275) = 147603 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a475_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 475))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 475) 186844) = 93851 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b475_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 475)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 475)) 186844) = 93851 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o475 : xone 475 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a475_0 b475_0 a475_1 b475_1 a475_2 b475_2
    a475_3 b475_3 a475_4 b475_4 a475_5 b475_5

theorem a476_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 476))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 476) 0) = 293114 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b476_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 476)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 476)) 0) = 293114 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a476_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 476))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 476) 305530) = 123177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b476_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 476)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 476)) 305530) = 123177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a476_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 476))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 476) 5604) = 24071 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b476_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 476)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 476)) 5604) = 24071 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a476_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 476))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 476) 221549) = 132720 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b476_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 476)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 476)) 221549) = 132720 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a476_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 476))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 476) 266275) = 35926 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b476_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 476)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 476)) 266275) = 35926 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a476_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 476))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 476) 186844) = 47395 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b476_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 476)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 476)) 186844) = 47395 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o476 : xone 476 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a476_0 b476_0 a476_1 b476_1 a476_2 b476_2
    a476_3 b476_3 a476_4 b476_4 a476_5 b476_5

theorem a477_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 477))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 477) 0) = 19116 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b477_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 477)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 477)) 0) = 19116 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a477_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 477))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 477) 305530) = 297374 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b477_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 477)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 477)) 305530) = 297374 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a477_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 477))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 477) 5604) = 247887 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b477_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 477)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 477)) 5604) = 247887 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a477_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 477))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 477) 221549) = 14433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b477_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 477)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 477)) 221549) = 14433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a477_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 477))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 477) 266275) = 250681 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b477_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 477)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 477)) 266275) = 250681 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a477_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 477))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 477) 186844) = 50771 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b477_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 477)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 477)) 186844) = 50771 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o477 : xone 477 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a477_0 b477_0 a477_1 b477_1 a477_2 b477_2
    a477_3 b477_3 a477_4 b477_4 a477_5 b477_5

theorem a478_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 478))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 478) 0) = 157122 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b478_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 478)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 478)) 0) = 157122 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a478_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 478))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 478) 305530) = 293466 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b478_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 478)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 478)) 305530) = 293466 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a478_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 478))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 478) 5604) = 61528 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b478_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 478)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 478)) 5604) = 61528 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a478_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 478))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 478) 221549) = 57243 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b478_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 478)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 478)) 221549) = 57243 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a478_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 478))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 478) 266275) = 27984 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b478_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 478)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 478)) 266275) = 27984 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a478_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 478))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 478) 186844) = 62779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b478_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 478)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 478)) 186844) = 62779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o478 : xone 478 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a478_0 b478_0 a478_1 b478_1 a478_2 b478_2
    a478_3 b478_3 a478_4 b478_4 a478_5 b478_5

theorem a479_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 479))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 479) 0) = 40756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b479_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 479)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 479)) 0) = 40756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a479_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 479))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 479) 305530) = 189960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b479_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 479)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 479)) 305530) = 189960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a479_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 479))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 479) 5604) = 102223 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b479_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 479)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 479)) 5604) = 102223 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a479_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 479))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 479) 221549) = 98785 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b479_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 479)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 479)) 221549) = 98785 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a479_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 479))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 479) 266275) = 254145 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b479_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 479)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 479)) 266275) = 254145 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a479_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 479))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 479) 186844) = 282395 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b479_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 479)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 479)) 186844) = 282395 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o479 : xone 479 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a479_0 b479_0 a479_1 b479_1 a479_2 b479_2
    a479_3 b479_3 a479_4 b479_4 a479_5 b479_5

theorem a480_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 480))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 480) 0) = 70873 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b480_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 480)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 480)) 0) = 70873 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a480_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 480))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 480) 305530) = 143630 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b480_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 480)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 480)) 305530) = 143630 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a480_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 480))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 480) 5604) = 173782 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b480_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 480)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 480)) 5604) = 173782 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a480_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 480))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 480) 221549) = 190744 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b480_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 480)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 480)) 221549) = 190744 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a480_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 480))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 480) 266275) = 248848 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b480_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 480)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 480)) 266275) = 248848 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a480_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 480))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 480) 186844) = 273550 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b480_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 480)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 480)) 186844) = 273550 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o480 : xone 480 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a480_0 b480_0 a480_1 b480_1 a480_2 b480_2
    a480_3 b480_3 a480_4 b480_4 a480_5 b480_5

theorem a481_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 481))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 481) 0) = 187162 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b481_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 481)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 481)) 0) = 187162 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a481_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 481))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 481) 305530) = 276169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b481_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 481)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 481)) 305530) = 276169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a481_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 481))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 481) 5604) = 116836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b481_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 481)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 481)) 5604) = 116836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a481_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 481))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 481) 221549) = 135301 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b481_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 481)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 481)) 221549) = 135301 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a481_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 481))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 481) 266275) = 195817 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b481_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 481)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 481)) 266275) = 195817 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a481_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 481))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 481) 186844) = 38074 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b481_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 481)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 481)) 186844) = 38074 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o481 : xone 481 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a481_0 b481_0 a481_1 b481_1 a481_2 b481_2
    a481_3 b481_3 a481_4 b481_4 a481_5 b481_5

theorem a482_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 482))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 482) 0) = 40795 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b482_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 482)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 482)) 0) = 40795 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a482_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 482))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 482) 305530) = 169864 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b482_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 482)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 482)) 305530) = 169864 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a482_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 482))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 482) 5604) = 277089 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b482_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 482)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 482)) 5604) = 277089 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a482_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 482))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 482) 221549) = 150690 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b482_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 482)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 482)) 221549) = 150690 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a482_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 482))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 482) 266275) = 68187 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b482_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 482)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 482)) 266275) = 68187 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a482_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 482))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 482) 186844) = 160542 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b482_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 482)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 482)) 186844) = 160542 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o482 : xone 482 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a482_0 b482_0 a482_1 b482_1 a482_2 b482_2
    a482_3 b482_3 a482_4 b482_4 a482_5 b482_5

theorem a483_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 483))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 483) 0) = 218213 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b483_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 483)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 483)) 0) = 218213 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a483_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 483))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 483) 305530) = 14423 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b483_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 483)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 483)) 305530) = 14423 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a483_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 483))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 483) 5604) = 69430 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b483_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 483)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 483)) 5604) = 69430 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a483_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 483))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 483) 221549) = 39785 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b483_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 483)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 483)) 221549) = 39785 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a483_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 483))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 483) 266275) = 23287 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b483_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 483)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 483)) 266275) = 23287 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a483_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 483))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 483) 186844) = 264498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b483_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 483)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 483)) 186844) = 264498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o483 : xone 483 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a483_0 b483_0 a483_1 b483_1 a483_2 b483_2
    a483_3 b483_3 a483_4 b483_4 a483_5 b483_5

theorem a484_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 484))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 484) 0) = 97128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b484_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 484)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 484)) 0) = 97128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a484_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 484))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 484) 305530) = 82757 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b484_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 484)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 484)) 305530) = 82757 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a484_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 484))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 484) 5604) = 39516 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b484_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 484)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 484)) 5604) = 39516 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a484_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 484))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 484) 221549) = 265767 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b484_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 484)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 484)) 221549) = 265767 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a484_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 484))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 484) 266275) = 25059 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b484_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 484)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 484)) 266275) = 25059 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a484_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 484))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 484) 186844) = 224474 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b484_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 484)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 484)) 186844) = 224474 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o484 : xone 484 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a484_0 b484_0 a484_1 b484_1 a484_2 b484_2
    a484_3 b484_3 a484_4 b484_4 a484_5 b484_5

theorem a485_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 485))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 485) 0) = 212838 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b485_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 485)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 485)) 0) = 212838 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a485_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 485))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 485) 305530) = 218997 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b485_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 485)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 485)) 305530) = 218997 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a485_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 485))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 485) 5604) = 237982 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b485_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 485)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 485)) 5604) = 237982 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a485_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 485))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 485) 221549) = 254715 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b485_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 485)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 485)) 221549) = 254715 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a485_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 485))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 485) 266275) = 248027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b485_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 485)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 485)) 266275) = 248027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a485_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 485))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 485) 186844) = 164414 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b485_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 485)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 485)) 186844) = 164414 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o485 : xone 485 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a485_0 b485_0 a485_1 b485_1 a485_2 b485_2
    a485_3 b485_3 a485_4 b485_4 a485_5 b485_5

theorem a486_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 486))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 486) 0) = 66908 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b486_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 486)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 486)) 0) = 66908 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a486_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 486))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 486) 305530) = 103469 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b486_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 486)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 486)) 305530) = 103469 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a486_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 486))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 486) 5604) = 51960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b486_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 486)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 486)) 5604) = 51960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a486_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 486))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 486) 221549) = 183804 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b486_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 486)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 486)) 221549) = 183804 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a486_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 486))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 486) 266275) = 58933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b486_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 486)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 486)) 266275) = 58933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a486_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 486))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 486) 186844) = 241070 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b486_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 486)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 486)) 186844) = 241070 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o486 : xone 486 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a486_0 b486_0 a486_1 b486_1 a486_2 b486_2
    a486_3 b486_3 a486_4 b486_4 a486_5 b486_5

theorem a487_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 487))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 487) 0) = 39878 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b487_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 487)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 487)) 0) = 39878 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a487_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 487))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 487) 305530) = 190067 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b487_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 487)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 487)) 305530) = 190067 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a487_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 487))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 487) 5604) = 140149 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b487_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 487)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 487)) 5604) = 140149 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a487_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 487))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 487) 221549) = 163151 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b487_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 487)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 487)) 221549) = 163151 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a487_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 487))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 487) 266275) = 200177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b487_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 487)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 487)) 266275) = 200177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a487_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 487))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 487) 186844) = 275446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b487_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 487)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 487)) 186844) = 275446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o487 : xone 487 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a487_0 b487_0 a487_1 b487_1 a487_2 b487_2
    a487_3 b487_3 a487_4 b487_4 a487_5 b487_5

theorem a488_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 488))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 488) 0) = 21525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b488_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 488)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 488)) 0) = 21525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a488_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 488))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 488) 305530) = 7074 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b488_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 488)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 488)) 305530) = 7074 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a488_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 488))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 488) 5604) = 152166 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b488_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 488)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 488)) 5604) = 152166 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a488_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 488))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 488) 221549) = 105390 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b488_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 488)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 488)) 221549) = 105390 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a488_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 488))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 488) 266275) = 97743 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b488_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 488)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 488)) 266275) = 97743 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a488_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 488))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 488) 186844) = 186466 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b488_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 488)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 488)) 186844) = 186466 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o488 : xone 488 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a488_0 b488_0 a488_1 b488_1 a488_2 b488_2
    a488_3 b488_3 a488_4 b488_4 a488_5 b488_5

theorem a489_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 489))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 489) 0) = 272602 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b489_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 489)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 489)) 0) = 272602 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a489_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 489))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 489) 305530) = 275418 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b489_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 489)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 489)) 305530) = 275418 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a489_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 489))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 489) 5604) = 56534 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b489_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 489)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 489)) 5604) = 56534 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a489_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 489))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 489) 221549) = 264521 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b489_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 489)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 489)) 221549) = 264521 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a489_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 489))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 489) 266275) = 278458 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b489_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 489)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 489)) 266275) = 278458 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a489_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 489))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 489) 186844) = 283968 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b489_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 489)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 489)) 186844) = 283968 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o489 : xone 489 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a489_0 b489_0 a489_1 b489_1 a489_2 b489_2
    a489_3 b489_3 a489_4 b489_4 a489_5 b489_5

theorem a490_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 490))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 490) 0) = 209672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b490_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 490)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 490)) 0) = 209672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a490_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 490))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 490) 305530) = 19118 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b490_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 490)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 490)) 305530) = 19118 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a490_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 490))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 490) 5604) = 120715 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b490_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 490)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 490)) 5604) = 120715 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a490_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 490))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 490) 221549) = 53571 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b490_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 490)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 490)) 221549) = 53571 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a490_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 490))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 490) 266275) = 35505 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b490_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 490)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 490)) 266275) = 35505 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a490_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 490))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 490) 186844) = 194322 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b490_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 490)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 490)) 186844) = 194322 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o490 : xone 490 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a490_0 b490_0 a490_1 b490_1 a490_2 b490_2
    a490_3 b490_3 a490_4 b490_4 a490_5 b490_5

theorem a491_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 491))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 491) 0) = 53803 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b491_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 491)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 491)) 0) = 53803 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a491_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 491))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 491) 305530) = 62185 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b491_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 491)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 491)) 305530) = 62185 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a491_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 491))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 491) 5604) = 147232 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b491_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 491)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 491)) 5604) = 147232 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a491_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 491))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 491) 221549) = 252594 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b491_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 491)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 491)) 221549) = 252594 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a491_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 491))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 491) 266275) = 108855 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b491_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 491)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 491)) 266275) = 108855 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a491_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 491))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 491) 186844) = 2856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b491_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 491)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 491)) 186844) = 2856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o491 : xone 491 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a491_0 b491_0 a491_1 b491_1 a491_2 b491_2
    a491_3 b491_3 a491_4 b491_4 a491_5 b491_5

theorem a492_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 492))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 492) 0) = 159922 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b492_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 492)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 492)) 0) = 159922 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a492_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 492))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 492) 305530) = 262451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b492_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 492)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 492)) 305530) = 262451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a492_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 492))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 492) 5604) = 299821 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b492_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 492)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 492)) 5604) = 299821 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a492_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 492))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 492) 221549) = 255402 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b492_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 492)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 492)) 221549) = 255402 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a492_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 492))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 492) 266275) = 44762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b492_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 492)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 492)) 266275) = 44762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a492_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 492))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 492) 186844) = 50290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b492_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 492)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 492)) 186844) = 50290 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o492 : xone 492 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a492_0 b492_0 a492_1 b492_1 a492_2 b492_2
    a492_3 b492_3 a492_4 b492_4 a492_5 b492_5

theorem a493_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 493))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 493) 0) = 65884 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b493_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 493)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 493)) 0) = 65884 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a493_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 493))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 493) 305530) = 133759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b493_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 493)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 493)) 305530) = 133759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a493_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 493))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 493) 5604) = 8479 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b493_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 493)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 493)) 5604) = 8479 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a493_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 493))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 493) 221549) = 735 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b493_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 493)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 493)) 221549) = 735 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a493_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 493))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 493) 266275) = 147762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b493_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 493)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 493)) 266275) = 147762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a493_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 493))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 493) 186844) = 182781 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b493_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 493)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 493)) 186844) = 182781 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o493 : xone 493 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a493_0 b493_0 a493_1 b493_1 a493_2 b493_2
    a493_3 b493_3 a493_4 b493_4 a493_5 b493_5

theorem a494_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 494))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 494) 0) = 68533 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b494_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 494)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 494)) 0) = 68533 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a494_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 494))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 494) 305530) = 96937 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b494_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 494)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 494)) 305530) = 96937 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a494_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 494))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 494) 5604) = 277608 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b494_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 494)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 494)) 5604) = 277608 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a494_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 494))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 494) 221549) = 31567 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b494_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 494)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 494)) 221549) = 31567 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a494_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 494))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 494) 266275) = 75077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b494_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 494)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 494)) 266275) = 75077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a494_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 494))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 494) 186844) = 85882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b494_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 494)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 494)) 186844) = 85882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o494 : xone 494 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a494_0 b494_0 a494_1 b494_1 a494_2 b494_2
    a494_3 b494_3 a494_4 b494_4 a494_5 b494_5

theorem a495_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 495))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 495) 0) = 232278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b495_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 495)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 495)) 0) = 232278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a495_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 495))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 495) 305530) = 25729 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b495_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 495)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 495)) 305530) = 25729 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a495_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 495))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 495) 5604) = 52950 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b495_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 495)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 495)) 5604) = 52950 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a495_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 495))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 495) 221549) = 197031 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b495_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 495)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 495)) 221549) = 197031 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a495_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 495))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 495) 266275) = 153427 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b495_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 495)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 495)) 266275) = 153427 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a495_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 495))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 495) 186844) = 190519 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b495_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 495)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 495)) 186844) = 190519 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o495 : xone 495 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a495_0 b495_0 a495_1 b495_1 a495_2 b495_2
    a495_3 b495_3 a495_4 b495_4 a495_5 b495_5

theorem a496_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 496))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 496) 0) = 32086 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b496_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 496)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 496)) 0) = 32086 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a496_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 496))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 496) 305530) = 282164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b496_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 496)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 496)) 305530) = 282164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a496_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 496))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 496) 5604) = 72022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b496_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 496)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 496)) 5604) = 72022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a496_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 496))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 496) 221549) = 9558 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b496_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 496)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 496)) 221549) = 9558 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a496_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 496))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 496) 266275) = 241692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b496_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 496)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 496)) 266275) = 241692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a496_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 496))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 496) 186844) = 212967 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b496_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 496)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 496)) 186844) = 212967 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o496 : xone 496 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a496_0 b496_0 a496_1 b496_1 a496_2 b496_2
    a496_3 b496_3 a496_4 b496_4 a496_5 b496_5

theorem a497_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 497))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 497) 0) = 4484 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b497_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 497)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 497)) 0) = 4484 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a497_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 497))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 497) 305530) = 109987 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b497_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 497)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 497)) 305530) = 109987 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a497_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 497))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 497) 5604) = 254820 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b497_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 497)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 497)) 5604) = 254820 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a497_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 497))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 497) 221549) = 201510 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b497_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 497)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 497)) 221549) = 201510 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a497_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 497))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 497) 266275) = 133219 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b497_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 497)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 497)) 266275) = 133219 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a497_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 497))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 497) 186844) = 202864 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b497_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 497)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 497)) 186844) = 202864 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o497 : xone 497 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a497_0 b497_0 a497_1 b497_1 a497_2 b497_2
    a497_3 b497_3 a497_4 b497_4 a497_5 b497_5

theorem a498_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 498))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 498) 0) = 42840 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b498_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 498)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 498)) 0) = 42840 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a498_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 498))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 498) 305530) = 143783 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b498_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 498)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 498)) 305530) = 143783 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a498_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 498))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 498) 5604) = 301524 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b498_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 498)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 498)) 5604) = 301524 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a498_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 498))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 498) 221549) = 54001 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b498_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 498)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 498)) 221549) = 54001 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a498_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 498))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 498) 266275) = 220194 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b498_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 498)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 498)) 266275) = 220194 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a498_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 498))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 498) 186844) = 153680 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b498_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 498)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 498)) 186844) = 153680 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o498 : xone 498 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a498_0 b498_0 a498_1 b498_1 a498_2 b498_2
    a498_3 b498_3 a498_4 b498_4 a498_5 b498_5

theorem a499_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 499))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 499) 0) = 167792 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b499_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 499)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 499)) 0) = 167792 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a499_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 499))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 499) 305530) = 238771 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b499_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 499)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 499)) 305530) = 238771 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a499_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 499))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 499) 5604) = 91262 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b499_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 499)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 499)) 5604) = 91262 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a499_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 499))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 499) 221549) = 173984 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b499_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 499)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 499)) 221549) = 173984 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a499_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 499))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 499) 266275) = 296772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b499_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 499)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 499)) 266275) = 296772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a499_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 499))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 499) 186844) = 22398 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b499_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 499)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 499)) 186844) = 22398 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o499 : xone 499 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a499_0 b499_0 a499_1 b499_1 a499_2 b499_2
    a499_3 b499_3 a499_4 b499_4 a499_5 b499_5

theorem a500_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 500))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 500) 0) = 82369 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b500_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 500)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 500)) 0) = 82369 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a500_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 500))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 500) 305530) = 296818 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b500_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 500)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 500)) 305530) = 296818 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a500_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 500))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 500) 5604) = 258823 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b500_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 500)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 500)) 5604) = 258823 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a500_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 500))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 500) 221549) = 39284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b500_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 500)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 500)) 221549) = 39284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a500_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 500))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 500) 266275) = 278714 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b500_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 500)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 500)) 266275) = 278714 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a500_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 500))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 500) 186844) = 19633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b500_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 500)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 500)) 186844) = 19633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o500 : xone 500 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a500_0 b500_0 a500_1 b500_1 a500_2 b500_2
    a500_3 b500_3 a500_4 b500_4 a500_5 b500_5

theorem a501_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 501))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 501) 0) = 156836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b501_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 501)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 501)) 0) = 156836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a501_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 501))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 501) 305530) = 164404 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b501_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 501)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 501)) 305530) = 164404 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a501_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 501))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 501) 5604) = 104183 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b501_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 501)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 501)) 5604) = 104183 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a501_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 501))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 501) 221549) = 299163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b501_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 501)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 501)) 221549) = 299163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a501_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 501))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 501) 266275) = 174980 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b501_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 501)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 501)) 266275) = 174980 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a501_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 501))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 501) 186844) = 29857 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b501_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 501)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 501)) 186844) = 29857 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o501 : xone 501 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a501_0 b501_0 a501_1 b501_1 a501_2 b501_2
    a501_3 b501_3 a501_4 b501_4 a501_5 b501_5

theorem a502_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 502))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 502) 0) = 41085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b502_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 502)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 502)) 0) = 41085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a502_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 502))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 502) 305530) = 63853 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b502_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 502)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 502)) 305530) = 63853 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a502_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 502))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 502) 5604) = 293755 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b502_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 502)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 502)) 5604) = 293755 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a502_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 502))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 502) 221549) = 22322 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b502_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 502)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 502)) 221549) = 22322 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a502_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 502))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 502) 266275) = 172857 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b502_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 502)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 502)) 266275) = 172857 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a502_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 502))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 502) 186844) = 265901 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b502_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 502)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 502)) 186844) = 265901 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o502 : xone 502 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a502_0 b502_0 a502_1 b502_1 a502_2 b502_2
    a502_3 b502_3 a502_4 b502_4 a502_5 b502_5

theorem a503_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 503))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 503) 0) = 266412 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b503_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 503)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 503)) 0) = 266412 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a503_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 503))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 503) 305530) = 41696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b503_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 503)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 503)) 305530) = 41696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a503_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 503))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 503) 5604) = 93332 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b503_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 503)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 503)) 5604) = 93332 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a503_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 503))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 503) 221549) = 98859 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b503_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 503)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 503)) 221549) = 98859 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a503_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 503))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 503) 266275) = 55606 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b503_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 503)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 503)) 266275) = 55606 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a503_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 503))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 503) 186844) = 174824 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b503_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 503)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 503)) 186844) = 174824 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o503 : xone 503 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a503_0 b503_0 a503_1 b503_1 a503_2 b503_2
    a503_3 b503_3 a503_4 b503_4 a503_5 b503_5

theorem a504_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 504))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 504) 0) = 115759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b504_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 504)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 504)) 0) = 115759 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a504_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 504))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 504) 305530) = 200356 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b504_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 504)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 504)) 305530) = 200356 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a504_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 504))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 504) 5604) = 282947 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b504_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 504)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 504)) 5604) = 282947 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a504_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 504))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 504) 221549) = 266787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b504_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 504)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 504)) 221549) = 266787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a504_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 504))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 504) 266275) = 231331 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b504_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 504)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 504)) 266275) = 231331 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a504_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 504))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 504) 186844) = 303768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b504_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 504)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 504)) 186844) = 303768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o504 : xone 504 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a504_0 b504_0 a504_1 b504_1 a504_2 b504_2
    a504_3 b504_3 a504_4 b504_4 a504_5 b504_5

theorem a505_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 505))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 505) 0) = 55357 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b505_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 505)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 505)) 0) = 55357 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a505_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 505))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 505) 305530) = 56142 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b505_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 505)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 505)) 305530) = 56142 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a505_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 505))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 505) 5604) = 111018 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b505_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 505)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 505)) 5604) = 111018 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a505_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 505))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 505) 221549) = 283471 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b505_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 505)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 505)) 221549) = 283471 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a505_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 505))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 505) 266275) = 111863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b505_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 505)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 505)) 266275) = 111863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a505_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 505))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 505) 186844) = 182716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b505_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 505)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 505)) 186844) = 182716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o505 : xone 505 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a505_0 b505_0 a505_1 b505_1 a505_2 b505_2
    a505_3 b505_3 a505_4 b505_4 a505_5 b505_5

theorem a506_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 506))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 506) 0) = 147822 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b506_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 506)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 506)) 0) = 147822 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a506_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 506))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 506) 305530) = 63655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b506_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 506)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 506)) 305530) = 63655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a506_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 506))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 506) 5604) = 126798 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b506_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 506)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 506)) 5604) = 126798 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a506_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 506))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 506) 221549) = 291985 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b506_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 506)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 506)) 221549) = 291985 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a506_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 506))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 506) 266275) = 66581 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b506_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 506)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 506)) 266275) = 66581 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a506_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 506))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 506) 186844) = 3065 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b506_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 506)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 506)) 186844) = 3065 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o506 : xone 506 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a506_0 b506_0 a506_1 b506_1 a506_2 b506_2
    a506_3 b506_3 a506_4 b506_4 a506_5 b506_5

theorem a507_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 507))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 507) 0) = 24032 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b507_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 507)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 507)) 0) = 24032 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a507_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 507))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 507) 305530) = 235230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b507_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 507)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 507)) 305530) = 235230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a507_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 507))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 507) 5604) = 143021 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b507_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 507)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 507)) 5604) = 143021 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a507_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 507))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 507) 221549) = 89098 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b507_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 507)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 507)) 221549) = 89098 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a507_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 507))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 507) 266275) = 268435 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b507_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 507)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 507)) 266275) = 268435 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a507_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 507))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 507) 186844) = 290089 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b507_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 507)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 507)) 186844) = 290089 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o507 : xone 507 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a507_0 b507_0 a507_1 b507_1 a507_2 b507_2
    a507_3 b507_3 a507_4 b507_4 a507_5 b507_5

theorem a508_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 508))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 508) 0) = 97842 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b508_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 508)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 508)) 0) = 97842 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a508_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 508))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 508) 305530) = 131294 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b508_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 508)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 508)) 305530) = 131294 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a508_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 508))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 508) 5604) = 141573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b508_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 508)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 508)) 5604) = 141573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a508_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 508))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 508) 221549) = 247823 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b508_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 508)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 508)) 221549) = 247823 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a508_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 508))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 508) 266275) = 52306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b508_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 508)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 508)) 266275) = 52306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a508_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 508))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 508) 186844) = 33454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b508_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 508)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 508)) 186844) = 33454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o508 : xone 508 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a508_0 b508_0 a508_1 b508_1 a508_2 b508_2
    a508_3 b508_3 a508_4 b508_4 a508_5 b508_5

theorem a509_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 509))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 509) 0) = 294362 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b509_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 509)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 509)) 0) = 294362 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a509_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 509))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 509) 305530) = 237750 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b509_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 509)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 509)) 305530) = 237750 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a509_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 509))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 509) 5604) = 143159 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b509_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 509)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 509)) 5604) = 143159 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a509_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 509))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 509) 221549) = 279511 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b509_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 509)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 509)) 221549) = 279511 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a509_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 509))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 509) 266275) = 18573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b509_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 509)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 509)) 266275) = 18573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a509_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 509))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 509) 186844) = 49734 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b509_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 509)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 509)) 186844) = 49734 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o509 : xone 509 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a509_0 b509_0 a509_1 b509_1 a509_2 b509_2
    a509_3 b509_3 a509_4 b509_4 a509_5 b509_5

theorem a510_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 510))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 510) 0) = 26361 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b510_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 510)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 510)) 0) = 26361 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a510_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 510))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 510) 305530) = 151578 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b510_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 510)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 510)) 305530) = 151578 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a510_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 510))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 510) 5604) = 107277 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b510_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 510)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 510)) 5604) = 107277 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a510_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 510))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 510) 221549) = 130089 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b510_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 510)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 510)) 221549) = 130089 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a510_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 510))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 510) 266275) = 206688 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b510_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 510)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 510)) 266275) = 206688 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a510_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 510))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 510) 186844) = 204818 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b510_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 510)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 510)) 186844) = 204818 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o510 : xone 510 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a510_0 b510_0 a510_1 b510_1 a510_2 b510_2
    a510_3 b510_3 a510_4 b510_4 a510_5 b510_5

theorem a511_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 511))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 511) 0) = 269926 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b511_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 511)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 511)) 0) = 269926 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a511_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 511))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 511) 305530) = 258574 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b511_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 511)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 511)) 305530) = 258574 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a511_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 511))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 511) 5604) = 182746 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b511_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 511)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 511)) 5604) = 182746 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a511_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 511))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 511) 221549) = 60217 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b511_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 511)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 511)) 221549) = 60217 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a511_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 511))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 511) 266275) = 264239 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b511_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 511)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 511)) 266275) = 264239 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a511_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 511))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 511) 186844) = 47764 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b511_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 511)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 511)) 186844) = 47764 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o511 : xone 511 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a511_0 b511_0 a511_1 b511_1 a511_2 b511_2
    a511_3 b511_3 a511_4 b511_4 a511_5 b511_5

theorem a512_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 512))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 512) 0) = 156326 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b512_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 512)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 512)) 0) = 156326 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a512_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 512))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 512) 305530) = 44005 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b512_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 512)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 512)) 305530) = 44005 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a512_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 512))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 512) 5604) = 66234 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b512_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 512)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 512)) 5604) = 66234 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a512_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 512))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 512) 221549) = 27784 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b512_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 512)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 512)) 221549) = 27784 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a512_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 512))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 512) 266275) = 15923 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b512_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 512)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 512)) 266275) = 15923 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a512_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 512))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 512) 186844) = 215102 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b512_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 512)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 512)) 186844) = 215102 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o512 : xone 512 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a512_0 b512_0 a512_1 b512_1 a512_2 b512_2
    a512_3 b512_3 a512_4 b512_4 a512_5 b512_5

theorem a513_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 513))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 513) 0) = 135259 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b513_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 513)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 513)) 0) = 135259 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a513_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 513))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 513) 305530) = 58464 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b513_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 513)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 513)) 305530) = 58464 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a513_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 513))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 513) 5604) = 124845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b513_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 513)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 513)) 5604) = 124845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a513_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 513))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 513) 221549) = 65951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b513_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 513)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 513)) 221549) = 65951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a513_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 513))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 513) 266275) = 61169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b513_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 513)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 513)) 266275) = 61169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a513_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 513))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 513) 186844) = 221163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b513_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 513)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 513)) 186844) = 221163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o513 : xone 513 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a513_0 b513_0 a513_1 b513_1 a513_2 b513_2
    a513_3 b513_3 a513_4 b513_4 a513_5 b513_5

theorem a514_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 514))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 514) 0) = 150091 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b514_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 514)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 514)) 0) = 150091 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a514_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 514))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 514) 305530) = 212343 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b514_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 514)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 514)) 305530) = 212343 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a514_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 514))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 514) 5604) = 187375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b514_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 514)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 514)) 5604) = 187375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a514_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 514))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 514) 221549) = 256947 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b514_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 514)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 514)) 221549) = 256947 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a514_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 514))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 514) 266275) = 221267 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b514_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 514)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 514)) 266275) = 221267 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a514_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 514))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 514) 186844) = 118062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b514_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 514)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 514)) 186844) = 118062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o514 : xone 514 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a514_0 b514_0 a514_1 b514_1 a514_2 b514_2
    a514_3 b514_3 a514_4 b514_4 a514_5 b514_5

theorem a515_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 515))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 515) 0) = 211102 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b515_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 515)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 515)) 0) = 211102 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a515_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 515))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 515) 305530) = 127220 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b515_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 515)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 515)) 305530) = 127220 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a515_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 515))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 515) 5604) = 215427 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b515_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 515)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 515)) 5604) = 215427 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a515_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 515))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 515) 221549) = 237051 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b515_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 515)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 515)) 221549) = 237051 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a515_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 515))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 515) 266275) = 195933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b515_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 515)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 515)) 266275) = 195933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a515_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 515))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 515) 186844) = 71173 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b515_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 515)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 515)) 186844) = 71173 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o515 : xone 515 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a515_0 b515_0 a515_1 b515_1 a515_2 b515_2
    a515_3 b515_3 a515_4 b515_4 a515_5 b515_5

theorem a516_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 516))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 516) 0) = 275894 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b516_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 516)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 516)) 0) = 275894 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a516_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 516))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 516) 305530) = 101509 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b516_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 516)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 516)) 305530) = 101509 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a516_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 516))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 516) 5604) = 216406 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b516_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 516)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 516)) 5604) = 216406 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a516_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 516))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 516) 221549) = 106265 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b516_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 516)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 516)) 221549) = 106265 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a516_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 516))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 516) 266275) = 31187 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b516_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 516)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 516)) 266275) = 31187 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a516_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 516))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 516) 186844) = 260636 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b516_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 516)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 516)) 186844) = 260636 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o516 : xone 516 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a516_0 b516_0 a516_1 b516_1 a516_2 b516_2
    a516_3 b516_3 a516_4 b516_4 a516_5 b516_5

theorem a517_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 517))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 517) 0) = 282787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b517_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 517)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 517)) 0) = 282787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a517_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 517))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 517) 305530) = 277295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b517_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 517)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 517)) 305530) = 277295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a517_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 517))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 517) 5604) = 268834 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b517_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 517)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 517)) 5604) = 268834 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a517_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 517))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 517) 221549) = 299576 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b517_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 517)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 517)) 221549) = 299576 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a517_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 517))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 517) 266275) = 84682 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b517_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 517)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 517)) 266275) = 84682 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a517_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 517))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 517) 186844) = 214350 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b517_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 517)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 517)) 186844) = 214350 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o517 : xone 517 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a517_0 b517_0 a517_1 b517_1 a517_2 b517_2
    a517_3 b517_3 a517_4 b517_4 a517_5 b517_5

theorem a518_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 518))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 518) 0) = 12604 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b518_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 518)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 518)) 0) = 12604 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a518_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 518))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 518) 305530) = 92998 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b518_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 518)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 518)) 305530) = 92998 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a518_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 518))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 518) 5604) = 233828 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b518_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 518)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 518)) 5604) = 233828 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a518_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 518))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 518) 221549) = 273837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b518_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 518)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 518)) 221549) = 273837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a518_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 518))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 518) 266275) = 59850 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b518_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 518)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 518)) 266275) = 59850 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a518_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 518))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 518) 186844) = 193085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b518_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 518)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 518)) 186844) = 193085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o518 : xone 518 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a518_0 b518_0 a518_1 b518_1 a518_2 b518_2
    a518_3 b518_3 a518_4 b518_4 a518_5 b518_5

theorem a519_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 519))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 519) 0) = 40129 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b519_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 519)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 519)) 0) = 40129 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a519_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 519))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 519) 305530) = 118826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b519_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 519)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 519)) 305530) = 118826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a519_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 519))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 519) 5604) = 100019 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b519_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 519)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 519)) 5604) = 100019 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a519_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 519))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 519) 221549) = 87236 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b519_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 519)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 519)) 221549) = 87236 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a519_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 519))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 519) 266275) = 69634 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b519_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 519)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 519)) 266275) = 69634 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a519_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 519))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 519) 186844) = 103292 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b519_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 519)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 519)) 186844) = 103292 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o519 : xone 519 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a519_0 b519_0 a519_1 b519_1 a519_2 b519_2
    a519_3 b519_3 a519_4 b519_4 a519_5 b519_5

theorem a520_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 520))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 520) 0) = 185091 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b520_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 520)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 520)) 0) = 185091 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a520_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 520))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 520) 305530) = 215633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b520_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 520)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 520)) 305530) = 215633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a520_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 520))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 520) 5604) = 56299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b520_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 520)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 520)) 5604) = 56299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a520_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 520))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 520) 221549) = 201738 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b520_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 520)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 520)) 221549) = 201738 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a520_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 520))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 520) 266275) = 210208 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b520_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 520)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 520)) 266275) = 210208 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a520_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 520))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 520) 186844) = 190282 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b520_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 520)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 520)) 186844) = 190282 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o520 : xone 520 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a520_0 b520_0 a520_1 b520_1 a520_2 b520_2
    a520_3 b520_3 a520_4 b520_4 a520_5 b520_5

theorem a521_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 521))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 521) 0) = 83411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b521_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 521)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 521)) 0) = 83411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a521_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 521))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 521) 305530) = 166532 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b521_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 521)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 521)) 305530) = 166532 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a521_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 521))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 521) 5604) = 227689 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b521_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 521)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 521)) 5604) = 227689 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a521_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 521))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 521) 221549) = 39331 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b521_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 521)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 521)) 221549) = 39331 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a521_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 521))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 521) 266275) = 293089 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b521_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 521)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 521)) 266275) = 293089 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a521_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 521))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 521) 186844) = 244603 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b521_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 521)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 521)) 186844) = 244603 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o521 : xone 521 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a521_0 b521_0 a521_1 b521_1 a521_2 b521_2
    a521_3 b521_3 a521_4 b521_4 a521_5 b521_5

theorem a522_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 522))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 522) 0) = 58353 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b522_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 522)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 522)) 0) = 58353 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a522_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 522))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 522) 305530) = 305406 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b522_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 522)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 522)) 305530) = 305406 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a522_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 522))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 522) 5604) = 126057 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b522_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 522)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 522)) 5604) = 126057 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a522_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 522))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 522) 221549) = 304551 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b522_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 522)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 522)) 221549) = 304551 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a522_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 522))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 522) 266275) = 202112 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b522_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 522)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 522)) 266275) = 202112 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a522_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 522))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 522) 186844) = 232761 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b522_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 522)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 522)) 186844) = 232761 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o522 : xone 522 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a522_0 b522_0 a522_1 b522_1 a522_2 b522_2
    a522_3 b522_3 a522_4 b522_4 a522_5 b522_5

theorem a523_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 523))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 523) 0) = 133448 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b523_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 523)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 523)) 0) = 133448 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a523_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 523))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 523) 305530) = 293022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b523_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 523)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 523)) 305530) = 293022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a523_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 523))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 523) 5604) = 156246 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b523_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 523)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 523)) 5604) = 156246 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a523_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 523))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 523) 221549) = 239170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b523_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 523)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 523)) 221549) = 239170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a523_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 523))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 523) 266275) = 259437 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b523_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 523)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 523)) 266275) = 259437 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a523_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 523))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 523) 186844) = 213460 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b523_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 523)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 523)) 186844) = 213460 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o523 : xone 523 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a523_0 b523_0 a523_1 b523_1 a523_2 b523_2
    a523_3 b523_3 a523_4 b523_4 a523_5 b523_5

theorem a524_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 524))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 524) 0) = 497 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b524_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 524)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 524)) 0) = 497 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a524_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 524))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 524) 305530) = 36795 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b524_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 524)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 524)) 305530) = 36795 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a524_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 524))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 524) 5604) = 147984 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b524_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 524)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 524)) 5604) = 147984 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a524_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 524))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 524) 221549) = 301882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b524_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 524)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 524)) 221549) = 301882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a524_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 524))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 524) 266275) = 204202 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b524_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 524)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 524)) 266275) = 204202 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a524_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 524))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 524) 186844) = 300826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b524_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 524)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 524)) 186844) = 300826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o524 : xone 524 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a524_0 b524_0 a524_1 b524_1 a524_2 b524_2
    a524_3 b524_3 a524_4 b524_4 a524_5 b524_5

theorem a525_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 525))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 525) 0) = 186278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b525_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 525)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 525)) 0) = 186278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a525_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 525))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 525) 305530) = 10329 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b525_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 525)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 525)) 305530) = 10329 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a525_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 525))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 525) 5604) = 294078 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b525_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 525)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 525)) 5604) = 294078 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a525_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 525))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 525) 221549) = 112731 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b525_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 525)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 525)) 221549) = 112731 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a525_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 525))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 525) 266275) = 24817 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b525_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 525)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 525)) 266275) = 24817 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a525_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 525))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 525) 186844) = 182094 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b525_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 525)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 525)) 186844) = 182094 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o525 : xone 525 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a525_0 b525_0 a525_1 b525_1 a525_2 b525_2
    a525_3 b525_3 a525_4 b525_4 a525_5 b525_5

theorem a526_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 526))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 526) 0) = 196463 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b526_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 526)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 526)) 0) = 196463 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a526_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 526))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 526) 305530) = 137360 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b526_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 526)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 526)) 305530) = 137360 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a526_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 526))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 526) 5604) = 246059 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b526_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 526)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 526)) 5604) = 246059 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a526_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 526))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 526) 221549) = 73173 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b526_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 526)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 526)) 221549) = 73173 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a526_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 526))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 526) 266275) = 11321 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b526_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 526)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 526)) 266275) = 11321 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a526_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 526))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 526) 186844) = 256621 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b526_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 526)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 526)) 186844) = 256621 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o526 : xone 526 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a526_0 b526_0 a526_1 b526_1 a526_2 b526_2
    a526_3 b526_3 a526_4 b526_4 a526_5 b526_5

theorem a527_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 527))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 527) 0) = 212667 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b527_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 527)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 527)) 0) = 212667 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a527_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 527))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 527) 305530) = 240222 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b527_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 527)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 527)) 305530) = 240222 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a527_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 527))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 527) 5604) = 218471 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b527_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 527)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 527)) 5604) = 218471 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a527_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 527))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 527) 221549) = 195945 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b527_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 527)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 527)) 221549) = 195945 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a527_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 527))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 527) 266275) = 54969 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b527_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 527)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 527)) 266275) = 54969 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a527_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 527))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 527) 186844) = 119353 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b527_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 527)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 527)) 186844) = 119353 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o527 : xone 527 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a527_0 b527_0 a527_1 b527_1 a527_2 b527_2
    a527_3 b527_3 a527_4 b527_4 a527_5 b527_5

theorem a528_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 528))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 528) 0) = 194686 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b528_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 528)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 528)) 0) = 194686 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a528_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 528))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 528) 305530) = 271829 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b528_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 528)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 528)) 305530) = 271829 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a528_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 528))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 528) 5604) = 268942 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b528_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 528)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 528)) 5604) = 268942 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a528_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 528))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 528) 221549) = 20411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b528_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 528)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 528)) 221549) = 20411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a528_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 528))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 528) 266275) = 166999 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b528_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 528)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 528)) 266275) = 166999 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a528_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 528))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 528) 186844) = 18487 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b528_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 528)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 528)) 186844) = 18487 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o528 : xone 528 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a528_0 b528_0 a528_1 b528_1 a528_2 b528_2
    a528_3 b528_3 a528_4 b528_4 a528_5 b528_5

theorem a529_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 529))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 529) 0) = 232297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b529_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 529)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 529)) 0) = 232297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a529_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 529))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 529) 305530) = 136859 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b529_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 529)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 529)) 305530) = 136859 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a529_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 529))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 529) 5604) = 8346 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b529_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 529)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 529)) 5604) = 8346 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a529_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 529))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 529) 221549) = 50412 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b529_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 529)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 529)) 221549) = 50412 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a529_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 529))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 529) 266275) = 142692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b529_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 529)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 529)) 266275) = 142692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a529_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 529))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 529) 186844) = 288935 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b529_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 529)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 529)) 186844) = 288935 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o529 : xone 529 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a529_0 b529_0 a529_1 b529_1 a529_2 b529_2
    a529_3 b529_3 a529_4 b529_4 a529_5 b529_5

theorem a530_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 530))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 530) 0) = 119299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b530_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 530)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 530)) 0) = 119299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a530_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 530))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 530) 305530) = 140938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b530_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 530)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 530)) 305530) = 140938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a530_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 530))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 530) 5604) = 46706 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b530_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 530)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 530)) 5604) = 46706 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a530_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 530))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 530) 221549) = 168309 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b530_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 530)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 530)) 221549) = 168309 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a530_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 530))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 530) 266275) = 80511 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b530_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 530)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 530)) 266275) = 80511 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a530_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 530))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 530) 186844) = 170495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b530_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 530)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 530)) 186844) = 170495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o530 : xone 530 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a530_0 b530_0 a530_1 b530_1 a530_2 b530_2
    a530_3 b530_3 a530_4 b530_4 a530_5 b530_5

theorem a531_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 531))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 531) 0) = 117024 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b531_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 531)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 531)) 0) = 117024 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a531_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 531))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 531) 305530) = 252048 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b531_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 531)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 531)) 305530) = 252048 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a531_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 531))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 531) 5604) = 121217 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b531_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 531)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 531)) 5604) = 121217 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a531_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 531))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 531) 221549) = 48918 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b531_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 531)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 531)) 221549) = 48918 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a531_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 531))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 531) 266275) = 23489 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b531_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 531)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 531)) 266275) = 23489 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a531_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 531))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 531) 186844) = 136753 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b531_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 531)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 531)) 186844) = 136753 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o531 : xone 531 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a531_0 b531_0 a531_1 b531_1 a531_2 b531_2
    a531_3 b531_3 a531_4 b531_4 a531_5 b531_5

theorem a532_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 532))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 532) 0) = 141900 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b532_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 532)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 532)) 0) = 141900 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a532_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 532))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 532) 305530) = 16974 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b532_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 532)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 532)) 305530) = 16974 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a532_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 532))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 532) 5604) = 215597 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b532_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 532)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 532)) 5604) = 215597 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a532_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 532))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 532) 221549) = 262856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b532_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 532)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 532)) 221549) = 262856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a532_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 532))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 532) 266275) = 183434 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b532_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 532)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 532)) 266275) = 183434 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a532_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 532))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 532) 186844) = 73045 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b532_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 532)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 532)) 186844) = 73045 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o532 : xone 532 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a532_0 b532_0 a532_1 b532_1 a532_2 b532_2
    a532_3 b532_3 a532_4 b532_4 a532_5 b532_5

theorem a533_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 533))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 533) 0) = 5256 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b533_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 533)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 533)) 0) = 5256 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a533_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 533))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 533) 305530) = 38174 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b533_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 533)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 533)) 305530) = 38174 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a533_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 533))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 533) 5604) = 291090 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b533_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 533)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 533)) 5604) = 291090 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a533_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 533))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 533) 221549) = 239446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b533_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 533)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 533)) 221549) = 239446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a533_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 533))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 533) 266275) = 165176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b533_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 533)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 533)) 266275) = 165176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a533_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 533))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 533) 186844) = 31752 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b533_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 533)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 533)) 186844) = 31752 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o533 : xone 533 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a533_0 b533_0 a533_1 b533_1 a533_2 b533_2
    a533_3 b533_3 a533_4 b533_4 a533_5 b533_5

theorem a534_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 534))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 534) 0) = 220558 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b534_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 534)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 534)) 0) = 220558 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a534_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 534))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 534) 305530) = 29667 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b534_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 534)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 534)) 305530) = 29667 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a534_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 534))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 534) 5604) = 192342 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b534_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 534)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 534)) 5604) = 192342 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a534_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 534))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 534) 221549) = 56306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b534_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 534)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 534)) 221549) = 56306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a534_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 534))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 534) 266275) = 64779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b534_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 534)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 534)) 266275) = 64779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a534_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 534))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 534) 186844) = 291734 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b534_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 534)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 534)) 186844) = 291734 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o534 : xone 534 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a534_0 b534_0 a534_1 b534_1 a534_2 b534_2
    a534_3 b534_3 a534_4 b534_4 a534_5 b534_5

theorem a535_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 535))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 535) 0) = 33856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b535_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 535)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 535)) 0) = 33856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a535_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 535))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 535) 305530) = 185169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b535_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 535)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 535)) 305530) = 185169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a535_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 535))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 535) 5604) = 219946 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b535_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 535)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 535)) 5604) = 219946 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a535_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 535))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 535) 221549) = 298227 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b535_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 535)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 535)) 221549) = 298227 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a535_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 535))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 535) 266275) = 33270 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b535_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 535)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 535)) 266275) = 33270 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a535_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 535))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 535) 186844) = 295054 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b535_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 535)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 535)) 186844) = 295054 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o535 : xone 535 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a535_0 b535_0 a535_1 b535_1 a535_2 b535_2
    a535_3 b535_3 a535_4 b535_4 a535_5 b535_5

theorem a536_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 536))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 536) 0) = 210201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b536_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 536)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 536)) 0) = 210201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a536_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 536))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 536) 305530) = 279655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b536_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 536)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 536)) 305530) = 279655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a536_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 536))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 536) 5604) = 212553 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b536_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 536)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 536)) 5604) = 212553 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a536_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 536))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 536) 221549) = 95622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b536_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 536)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 536)) 221549) = 95622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a536_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 536))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 536) 266275) = 272787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b536_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 536)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 536)) 266275) = 272787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a536_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 536))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 536) 186844) = 198006 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b536_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 536)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 536)) 186844) = 198006 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o536 : xone 536 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a536_0 b536_0 a536_1 b536_1 a536_2 b536_2
    a536_3 b536_3 a536_4 b536_4 a536_5 b536_5

theorem a537_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 537))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 537) 0) = 200434 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b537_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 537)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 537)) 0) = 200434 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a537_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 537))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 537) 305530) = 189775 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b537_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 537)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 537)) 305530) = 189775 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a537_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 537))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 537) 5604) = 94070 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b537_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 537)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 537)) 5604) = 94070 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a537_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 537))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 537) 221549) = 197300 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b537_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 537)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 537)) 221549) = 197300 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a537_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 537))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 537) 266275) = 232555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b537_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 537)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 537)) 266275) = 232555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a537_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 537))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 537) 186844) = 236053 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b537_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 537)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 537)) 186844) = 236053 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o537 : xone 537 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a537_0 b537_0 a537_1 b537_1 a537_2 b537_2
    a537_3 b537_3 a537_4 b537_4 a537_5 b537_5

theorem a538_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 538))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 538) 0) = 43414 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b538_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 538)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 538)) 0) = 43414 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a538_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 538))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 538) 305530) = 155076 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b538_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 538)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 538)) 305530) = 155076 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a538_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 538))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 538) 5604) = 4949 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b538_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 538)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 538)) 5604) = 4949 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a538_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 538))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 538) 221549) = 281579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b538_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 538)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 538)) 221549) = 281579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a538_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 538))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 538) 266275) = 133293 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b538_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 538)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 538)) 266275) = 133293 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a538_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 538))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 538) 186844) = 268221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b538_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 538)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 538)) 186844) = 268221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o538 : xone 538 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a538_0 b538_0 a538_1 b538_1 a538_2 b538_2
    a538_3 b538_3 a538_4 b538_4 a538_5 b538_5

theorem a539_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 539))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 539) 0) = 172467 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b539_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 539)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 539)) 0) = 172467 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a539_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 539))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 539) 305530) = 269552 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b539_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 539)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 539)) 305530) = 269552 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a539_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 539))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 539) 5604) = 105522 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b539_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 539)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 539)) 5604) = 105522 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a539_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 539))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 539) 221549) = 213986 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b539_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 539)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 539)) 221549) = 213986 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a539_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 539))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 539) 266275) = 235529 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b539_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 539)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 539)) 266275) = 235529 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a539_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 539))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 539) 186844) = 88274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b539_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 539)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 539)) 186844) = 88274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o539 : xone 539 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a539_0 b539_0 a539_1 b539_1 a539_2 b539_2
    a539_3 b539_3 a539_4 b539_4 a539_5 b539_5

theorem a540_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 540))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 540) 0) = 139553 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b540_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 540)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 540)) 0) = 139553 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a540_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 540))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 540) 305530) = 87003 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b540_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 540)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 540)) 305530) = 87003 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a540_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 540))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 540) 5604) = 279735 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b540_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 540)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 540)) 5604) = 279735 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a540_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 540))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 540) 221549) = 14899 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b540_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 540)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 540)) 221549) = 14899 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a540_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 540))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 540) 266275) = 241853 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b540_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 540)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 540)) 266275) = 241853 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a540_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 540))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 540) 186844) = 203339 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b540_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 540)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 540)) 186844) = 203339 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o540 : xone 540 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a540_0 b540_0 a540_1 b540_1 a540_2 b540_2
    a540_3 b540_3 a540_4 b540_4 a540_5 b540_5

theorem a541_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 541))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 541) 0) = 77726 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b541_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 541)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 541)) 0) = 77726 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a541_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 541))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 541) 305530) = 89415 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b541_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 541)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 541)) 305530) = 89415 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a541_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 541))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 541) 5604) = 112067 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b541_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 541)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 541)) 5604) = 112067 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a541_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 541))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 541) 221549) = 147770 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b541_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 541)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 541)) 221549) = 147770 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a541_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 541))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 541) 266275) = 29648 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b541_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 541)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 541)) 266275) = 29648 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a541_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 541))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 541) 186844) = 211793 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b541_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 541)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 541)) 186844) = 211793 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o541 : xone 541 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a541_0 b541_0 a541_1 b541_1 a541_2 b541_2
    a541_3 b541_3 a541_4 b541_4 a541_5 b541_5

theorem a542_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 542))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 542) 0) = 281638 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b542_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 542)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 542)) 0) = 281638 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a542_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 542))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 542) 305530) = 3922 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b542_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 542)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 542)) 305530) = 3922 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a542_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 542))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 542) 5604) = 17021 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b542_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 542)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 542)) 5604) = 17021 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a542_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 542))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 542) 221549) = 171358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b542_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 542)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 542)) 221549) = 171358 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a542_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 542))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 542) 266275) = 50921 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b542_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 542)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 542)) 266275) = 50921 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a542_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 542))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 542) 186844) = 70705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b542_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 542)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 542)) 186844) = 70705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o542 : xone 542 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a542_0 b542_0 a542_1 b542_1 a542_2 b542_2
    a542_3 b542_3 a542_4 b542_4 a542_5 b542_5

theorem a543_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 543))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 543) 0) = 228255 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b543_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 543)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 543)) 0) = 228255 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a543_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 543))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 543) 305530) = 261570 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b543_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 543)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 543)) 305530) = 261570 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a543_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 543))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 543) 5604) = 164686 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b543_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 543)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 543)) 5604) = 164686 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a543_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 543))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 543) 221549) = 49703 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b543_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 543)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 543)) 221549) = 49703 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a543_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 543))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 543) 266275) = 45829 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b543_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 543)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 543)) 266275) = 45829 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a543_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 543))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 543) 186844) = 254829 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b543_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 543)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 543)) 186844) = 254829 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o543 : xone 543 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a543_0 b543_0 a543_1 b543_1 a543_2 b543_2
    a543_3 b543_3 a543_4 b543_4 a543_5 b543_5

theorem a544_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 544))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 544) 0) = 248546 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b544_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 544)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 544)) 0) = 248546 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a544_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 544))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 544) 305530) = 154148 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b544_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 544)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 544)) 305530) = 154148 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a544_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 544))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 544) 5604) = 279595 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b544_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 544)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 544)) 5604) = 279595 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a544_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 544))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 544) 221549) = 242722 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b544_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 544)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 544)) 221549) = 242722 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a544_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 544))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 544) 266275) = 203577 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b544_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 544)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 544)) 266275) = 203577 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a544_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 544))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 544) 186844) = 287551 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b544_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 544)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 544)) 186844) = 287551 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o544 : xone 544 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a544_0 b544_0 a544_1 b544_1 a544_2 b544_2
    a544_3 b544_3 a544_4 b544_4 a544_5 b544_5

theorem a545_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 545))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 545) 0) = 147898 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b545_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 545)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 545)) 0) = 147898 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a545_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 545))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 545) 305530) = 6307 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b545_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 545)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 545)) 305530) = 6307 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a545_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 545))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 545) 5604) = 105651 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b545_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 545)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 545)) 5604) = 105651 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a545_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 545))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 545) 221549) = 37495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b545_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 545)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 545)) 221549) = 37495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a545_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 545))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 545) 266275) = 89812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b545_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 545)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 545)) 266275) = 89812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a545_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 545))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 545) 186844) = 266352 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b545_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 545)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 545)) 186844) = 266352 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o545 : xone 545 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a545_0 b545_0 a545_1 b545_1 a545_2 b545_2
    a545_3 b545_3 a545_4 b545_4 a545_5 b545_5

theorem a546_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 546))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 546) 0) = 184030 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b546_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 546)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 546)) 0) = 184030 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a546_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 546))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 546) 305530) = 242553 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b546_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 546)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 546)) 305530) = 242553 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a546_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 546))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 546) 5604) = 187504 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b546_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 546)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 546)) 5604) = 187504 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a546_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 546))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 546) 221549) = 227579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b546_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 546)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 546)) 221549) = 227579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a546_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 546))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 546) 266275) = 293662 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b546_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 546)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 546)) 266275) = 293662 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a546_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 546))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 546) 186844) = 105774 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b546_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 546)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 546)) 186844) = 105774 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o546 : xone 546 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a546_0 b546_0 a546_1 b546_1 a546_2 b546_2
    a546_3 b546_3 a546_4 b546_4 a546_5 b546_5

theorem a547_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 547))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 547) 0) = 123742 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b547_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 547)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 547)) 0) = 123742 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a547_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 547))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 547) 305530) = 148557 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b547_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 547)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 547)) 305530) = 148557 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a547_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 547))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 547) 5604) = 151673 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b547_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 547)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 547)) 5604) = 151673 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a547_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 547))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 547) 221549) = 301177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b547_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 547)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 547)) 221549) = 301177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a547_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 547))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 547) 266275) = 117436 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b547_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 547)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 547)) 266275) = 117436 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a547_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 547))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 547) 186844) = 116331 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b547_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 547)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 547)) 186844) = 116331 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o547 : xone 547 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a547_0 b547_0 a547_1 b547_1 a547_2 b547_2
    a547_3 b547_3 a547_4 b547_4 a547_5 b547_5

theorem a548_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 548))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 548) 0) = 262683 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b548_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 548)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 548)) 0) = 262683 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a548_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 548))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 548) 305530) = 34857 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b548_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 548)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 548)) 305530) = 34857 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a548_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 548))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 548) 5604) = 217602 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b548_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 548)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 548)) 5604) = 217602 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a548_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 548))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 548) 221549) = 163442 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b548_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 548)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 548)) 221549) = 163442 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a548_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 548))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 548) 266275) = 23462 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b548_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 548)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 548)) 266275) = 23462 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a548_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 548))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 548) 186844) = 233572 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b548_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 548)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 548)) 186844) = 233572 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o548 : xone 548 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a548_0 b548_0 a548_1 b548_1 a548_2 b548_2
    a548_3 b548_3 a548_4 b548_4 a548_5 b548_5

theorem a549_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 549))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 549) 0) = 106438 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b549_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 549)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 549)) 0) = 106438 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a549_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 549))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 549) 305530) = 92807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b549_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 549)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 549)) 305530) = 92807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a549_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 549))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 549) 5604) = 75157 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b549_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 549)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 549)) 5604) = 75157 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a549_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 549))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 549) 221549) = 230979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b549_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 549)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 549)) 221549) = 230979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a549_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 549))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 549) 266275) = 299182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b549_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 549)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 549)) 266275) = 299182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a549_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 549))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 549) 186844) = 142728 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b549_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 549)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 549)) 186844) = 142728 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o549 : xone 549 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a549_0 b549_0 a549_1 b549_1 a549_2 b549_2
    a549_3 b549_3 a549_4 b549_4 a549_5 b549_5

theorem a550_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 550))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 550) 0) = 78472 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b550_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 550)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 550)) 0) = 78472 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a550_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 550))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 550) 305530) = 102419 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b550_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 550)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 550)) 305530) = 102419 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a550_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 550))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 550) 5604) = 217475 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b550_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 550)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 550)) 5604) = 217475 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a550_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 550))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 550) 221549) = 92289 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b550_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 550)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 550)) 221549) = 92289 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a550_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 550))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 550) 266275) = 235779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b550_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 550)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 550)) 266275) = 235779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a550_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 550))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 550) 186844) = 149432 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b550_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 550)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 550)) 186844) = 149432 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o550 : xone 550 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a550_0 b550_0 a550_1 b550_1 a550_2 b550_2
    a550_3 b550_3 a550_4 b550_4 a550_5 b550_5

theorem a551_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 551))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 551) 0) = 285792 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b551_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 551)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 551)) 0) = 285792 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a551_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 551))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 551) 305530) = 301227 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b551_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 551)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 551)) 305530) = 301227 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a551_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 551))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 551) 5604) = 147938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b551_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 551)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 551)) 5604) = 147938 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a551_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 551))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 551) 221549) = 276908 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b551_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 551)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 551)) 221549) = 276908 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a551_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 551))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 551) 266275) = 168845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b551_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 551)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 551)) 266275) = 168845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a551_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 551))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 551) 186844) = 9495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b551_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 551)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 551)) 186844) = 9495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o551 : xone 551 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a551_0 b551_0 a551_1 b551_1 a551_2 b551_2
    a551_3 b551_3 a551_4 b551_4 a551_5 b551_5

theorem a552_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 552))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 552) 0) = 2657 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b552_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 552)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 552)) 0) = 2657 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a552_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 552))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 552) 305530) = 269816 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b552_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 552)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 552)) 305530) = 269816 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a552_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 552))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 552) 5604) = 80943 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b552_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 552)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 552)) 5604) = 80943 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a552_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 552))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 552) 221549) = 51415 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b552_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 552)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 552)) 221549) = 51415 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a552_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 552))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 552) 266275) = 253818 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b552_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 552)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 552)) 266275) = 253818 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a552_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 552))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 552) 186844) = 214149 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b552_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 552)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 552)) 186844) = 214149 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o552 : xone 552 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a552_0 b552_0 a552_1 b552_1 a552_2 b552_2
    a552_3 b552_3 a552_4 b552_4 a552_5 b552_5

theorem a553_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 553))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 553) 0) = 40722 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b553_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 553)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 553)) 0) = 40722 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a553_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 553))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 553) 305530) = 161428 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b553_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 553)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 553)) 305530) = 161428 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a553_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 553))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 553) 5604) = 256053 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b553_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 553)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 553)) 5604) = 256053 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a553_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 553))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 553) 221549) = 72195 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b553_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 553)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 553)) 221549) = 72195 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a553_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 553))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 553) 266275) = 285186 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b553_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 553)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 553)) 266275) = 285186 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a553_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 553))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 553) 186844) = 300785 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b553_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 553)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 553)) 186844) = 300785 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o553 : xone 553 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a553_0 b553_0 a553_1 b553_1 a553_2 b553_2
    a553_3 b553_3 a553_4 b553_4 a553_5 b553_5

theorem a554_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 554))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 554) 0) = 149271 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b554_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 554)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 554)) 0) = 149271 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a554_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 554))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 554) 305530) = 175074 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b554_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 554)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 554)) 305530) = 175074 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a554_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 554))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 554) 5604) = 28835 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b554_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 554)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 554)) 5604) = 28835 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a554_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 554))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 554) 221549) = 12196 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b554_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 554)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 554)) 221549) = 12196 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a554_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 554))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 554) 266275) = 44690 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b554_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 554)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 554)) 266275) = 44690 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a554_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 554))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 554) 186844) = 32917 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b554_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 554)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 554)) 186844) = 32917 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o554 : xone 554 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a554_0 b554_0 a554_1 b554_1 a554_2 b554_2
    a554_3 b554_3 a554_4 b554_4 a554_5 b554_5

theorem a555_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 555))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 555) 0) = 21257 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b555_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 555)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 555)) 0) = 21257 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a555_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 555))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 555) 305530) = 9976 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b555_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 555)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 555)) 305530) = 9976 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a555_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 555))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 555) 5604) = 64097 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b555_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 555)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 555)) 5604) = 64097 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a555_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 555))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 555) 221549) = 267956 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b555_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 555)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 555)) 221549) = 267956 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a555_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 555))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 555) 266275) = 230257 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b555_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 555)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 555)) 266275) = 230257 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a555_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 555))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 555) 186844) = 155173 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b555_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 555)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 555)) 186844) = 155173 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o555 : xone 555 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a555_0 b555_0 a555_1 b555_1 a555_2 b555_2
    a555_3 b555_3 a555_4 b555_4 a555_5 b555_5

theorem a556_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 556))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 556) 0) = 270173 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b556_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 556)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 556)) 0) = 270173 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a556_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 556))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 556) 305530) = 178981 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b556_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 556)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 556)) 305530) = 178981 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a556_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 556))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 556) 5604) = 177418 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b556_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 556)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 556)) 5604) = 177418 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a556_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 556))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 556) 221549) = 170927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b556_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 556)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 556)) 221549) = 170927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a556_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 556))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 556) 266275) = 306897 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b556_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 556)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 556)) 266275) = 306897 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a556_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 556))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 556) 186844) = 279451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b556_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 556)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 556)) 186844) = 279451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o556 : xone 556 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a556_0 b556_0 a556_1 b556_1 a556_2 b556_2
    a556_3 b556_3 a556_4 b556_4 a556_5 b556_5

theorem a557_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 557))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 557) 0) = 80263 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b557_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 557)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 557)) 0) = 80263 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a557_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 557))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 557) 305530) = 222373 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b557_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 557)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 557)) 305530) = 222373 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a557_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 557))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 557) 5604) = 160034 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b557_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 557)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 557)) 5604) = 160034 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a557_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 557))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 557) 221549) = 274402 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b557_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 557)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 557)) 221549) = 274402 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a557_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 557))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 557) 266275) = 197685 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b557_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 557)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 557)) 266275) = 197685 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a557_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 557))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 557) 186844) = 239840 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b557_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 557)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 557)) 186844) = 239840 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o557 : xone 557 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a557_0 b557_0 a557_1 b557_1 a557_2 b557_2
    a557_3 b557_3 a557_4 b557_4 a557_5 b557_5

theorem a558_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 558))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 558) 0) = 35525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b558_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 558)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 558)) 0) = 35525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a558_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 558))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 558) 305530) = 292221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b558_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 558)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 558)) 305530) = 292221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a558_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 558))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 558) 5604) = 147244 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b558_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 558)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 558)) 5604) = 147244 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a558_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 558))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 558) 221549) = 4798 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b558_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 558)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 558)) 221549) = 4798 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a558_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 558))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 558) 266275) = 38077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b558_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 558)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 558)) 266275) = 38077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a558_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 558))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 558) 186844) = 14606 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b558_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 558)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 558)) 186844) = 14606 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o558 : xone 558 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a558_0 b558_0 a558_1 b558_1 a558_2 b558_2
    a558_3 b558_3 a558_4 b558_4 a558_5 b558_5

theorem a559_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 559))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 559) 0) = 107818 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b559_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 559)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 559)) 0) = 107818 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a559_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 559))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 559) 305530) = 269882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b559_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 559)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 559)) 305530) = 269882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a559_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 559))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 559) 5604) = 9194 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b559_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 559)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 559)) 5604) = 9194 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a559_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 559))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 559) 221549) = 155728 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b559_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 559)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 559)) 221549) = 155728 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a559_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 559))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 559) 266275) = 59655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b559_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 559)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 559)) 266275) = 59655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a559_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 559))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 559) 186844) = 128230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b559_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 559)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 559)) 186844) = 128230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o559 : xone 559 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a559_0 b559_0 a559_1 b559_1 a559_2 b559_2
    a559_3 b559_3 a559_4 b559_4 a559_5 b559_5

theorem a560_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 560))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 560) 0) = 215043 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b560_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 560)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 560)) 0) = 215043 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a560_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 560))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 560) 305530) = 302445 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b560_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 560)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 560)) 305530) = 302445 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a560_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 560))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 560) 5604) = 43018 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b560_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 560)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 560)) 5604) = 43018 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a560_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 560))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 560) 221549) = 19030 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b560_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 560)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 560)) 221549) = 19030 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a560_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 560))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 560) 266275) = 164701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b560_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 560)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 560)) 266275) = 164701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a560_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 560))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 560) 186844) = 2880 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b560_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 560)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 560)) 186844) = 2880 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o560 : xone 560 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a560_0 b560_0 a560_1 b560_1 a560_2 b560_2
    a560_3 b560_3 a560_4 b560_4 a560_5 b560_5

theorem a561_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 561))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 561) 0) = 19353 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b561_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 561)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 561)) 0) = 19353 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a561_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 561))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 561) 305530) = 44242 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b561_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 561)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 561)) 305530) = 44242 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a561_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 561))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 561) 5604) = 39411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b561_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 561)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 561)) 5604) = 39411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a561_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 561))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 561) 221549) = 65752 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b561_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 561)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 561)) 221549) = 65752 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a561_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 561))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 561) 266275) = 261866 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b561_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 561)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 561)) 266275) = 261866 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a561_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 561))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 561) 186844) = 14415 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b561_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 561)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 561)) 186844) = 14415 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o561 : xone 561 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a561_0 b561_0 a561_1 b561_1 a561_2 b561_2
    a561_3 b561_3 a561_4 b561_4 a561_5 b561_5

theorem a562_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 562))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 562) 0) = 20214 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b562_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 562)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 562)) 0) = 20214 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a562_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 562))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 562) 305530) = 18596 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b562_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 562)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 562)) 305530) = 18596 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a562_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 562))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 562) 5604) = 50115 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b562_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 562)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 562)) 5604) = 50115 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a562_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 562))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 562) 221549) = 275407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b562_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 562)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 562)) 221549) = 275407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a562_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 562))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 562) 266275) = 298269 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b562_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 562)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 562)) 266275) = 298269 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a562_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 562))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 562) 186844) = 200880 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b562_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 562)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 562)) 186844) = 200880 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o562 : xone 562 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a562_0 b562_0 a562_1 b562_1 a562_2 b562_2
    a562_3 b562_3 a562_4 b562_4 a562_5 b562_5

theorem a563_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 563))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 563) 0) = 116697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b563_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 563)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 563)) 0) = 116697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a563_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 563))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 563) 305530) = 241257 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b563_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 563)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 563)) 305530) = 241257 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a563_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 563))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 563) 5604) = 199278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b563_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 563)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 563)) 5604) = 199278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a563_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 563))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 563) 221549) = 11252 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b563_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 563)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 563)) 221549) = 11252 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a563_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 563))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 563) 266275) = 204602 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b563_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 563)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 563)) 266275) = 204602 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a563_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 563))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 563) 186844) = 185587 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b563_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 563)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 563)) 186844) = 185587 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o563 : xone 563 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a563_0 b563_0 a563_1 b563_1 a563_2 b563_2
    a563_3 b563_3 a563_4 b563_4 a563_5 b563_5

theorem a564_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 564))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 564) 0) = 175773 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b564_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 564)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 564)) 0) = 175773 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a564_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 564))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 564) 305530) = 175915 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b564_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 564)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 564)) 305530) = 175915 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a564_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 564))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 564) 5604) = 263811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b564_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 564)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 564)) 5604) = 263811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a564_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 564))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 564) 221549) = 39952 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b564_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 564)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 564)) 221549) = 39952 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a564_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 564))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 564) 266275) = 79108 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b564_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 564)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 564)) 266275) = 79108 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a564_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 564))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 564) 186844) = 163199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b564_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 564)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 564)) 186844) = 163199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o564 : xone 564 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a564_0 b564_0 a564_1 b564_1 a564_2 b564_2
    a564_3 b564_3 a564_4 b564_4 a564_5 b564_5

theorem a565_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 565))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 565) 0) = 292435 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b565_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 565)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 565)) 0) = 292435 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a565_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 565))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 565) 305530) = 11103 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b565_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 565)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 565)) 305530) = 11103 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a565_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 565))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 565) 5604) = 246974 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b565_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 565)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 565)) 5604) = 246974 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a565_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 565))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 565) 221549) = 250198 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b565_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 565)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 565)) 221549) = 250198 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a565_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 565))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 565) 266275) = 177888 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b565_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 565)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 565)) 266275) = 177888 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a565_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 565))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 565) 186844) = 100178 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b565_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 565)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 565)) 186844) = 100178 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o565 : xone 565 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a565_0 b565_0 a565_1 b565_1 a565_2 b565_2
    a565_3 b565_3 a565_4 b565_4 a565_5 b565_5

theorem a566_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 566))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 566) 0) = 282188 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b566_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 566)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 566)) 0) = 282188 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a566_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 566))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 566) 305530) = 91366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b566_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 566)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 566)) 305530) = 91366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a566_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 566))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 566) 5604) = 193386 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b566_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 566)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 566)) 5604) = 193386 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a566_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 566))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 566) 221549) = 114911 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b566_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 566)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 566)) 221549) = 114911 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a566_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 566))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 566) 266275) = 164270 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b566_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 566)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 566)) 266275) = 164270 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a566_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 566))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 566) 186844) = 16381 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b566_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 566)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 566)) 186844) = 16381 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o566 : xone 566 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a566_0 b566_0 a566_1 b566_1 a566_2 b566_2
    a566_3 b566_3 a566_4 b566_4 a566_5 b566_5

theorem a567_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 567))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 567) 0) = 195519 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b567_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 567)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 567)) 0) = 195519 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a567_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 567))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 567) 305530) = 179498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b567_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 567)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 567)) 305530) = 179498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a567_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 567))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 567) 5604) = 303537 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b567_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 567)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 567)) 5604) = 303537 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a567_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 567))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 567) 221549) = 53841 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b567_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 567)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 567)) 221549) = 53841 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a567_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 567))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 567) 266275) = 38804 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b567_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 567)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 567)) 266275) = 38804 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a567_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 567))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 567) 186844) = 290338 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b567_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 567)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 567)) 186844) = 290338 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o567 : xone 567 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a567_0 b567_0 a567_1 b567_1 a567_2 b567_2
    a567_3 b567_3 a567_4 b567_4 a567_5 b567_5

theorem a568_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 568))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 568) 0) = 235425 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b568_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 568)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 568)) 0) = 235425 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a568_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 568))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 568) 305530) = 192395 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b568_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 568)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 568)) 305530) = 192395 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a568_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 568))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 568) 5604) = 78616 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b568_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 568)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 568)) 5604) = 78616 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a568_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 568))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 568) 221549) = 258654 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b568_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 568)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 568)) 221549) = 258654 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a568_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 568))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 568) 266275) = 143078 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b568_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 568)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 568)) 266275) = 143078 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a568_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 568))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 568) 186844) = 180878 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b568_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 568)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 568)) 186844) = 180878 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o568 : xone 568 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a568_0 b568_0 a568_1 b568_1 a568_2 b568_2
    a568_3 b568_3 a568_4 b568_4 a568_5 b568_5

theorem a569_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 569))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 569) 0) = 303255 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b569_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 569)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 569)) 0) = 303255 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a569_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 569))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 569) 305530) = 144349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b569_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 569)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 569)) 305530) = 144349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a569_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 569))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 569) 5604) = 202245 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b569_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 569)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 569)) 5604) = 202245 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a569_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 569))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 569) 221549) = 195983 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b569_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 569)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 569)) 221549) = 195983 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a569_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 569))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 569) 266275) = 42666 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b569_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 569)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 569)) 266275) = 42666 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a569_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 569))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 569) 186844) = 263703 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b569_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 569)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 569)) 186844) = 263703 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o569 : xone 569 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a569_0 b569_0 a569_1 b569_1 a569_2 b569_2
    a569_3 b569_3 a569_4 b569_4 a569_5 b569_5

theorem a570_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 570))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 570) 0) = 161226 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b570_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 570)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 570)) 0) = 161226 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a570_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 570))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 570) 305530) = 76698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b570_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 570)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 570)) 305530) = 76698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a570_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 570))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 570) 5604) = 296827 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b570_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 570)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 570)) 5604) = 296827 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a570_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 570))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 570) 221549) = 91459 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b570_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 570)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 570)) 221549) = 91459 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a570_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 570))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 570) 266275) = 184881 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b570_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 570)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 570)) 266275) = 184881 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a570_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 570))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 570) 186844) = 11278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b570_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 570)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 570)) 186844) = 11278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o570 : xone 570 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a570_0 b570_0 a570_1 b570_1 a570_2 b570_2
    a570_3 b570_3 a570_4 b570_4 a570_5 b570_5

theorem a571_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 571))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 571) 0) = 83178 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b571_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 571)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 571)) 0) = 83178 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a571_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 571))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 571) 305530) = 135283 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b571_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 571)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 571)) 305530) = 135283 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a571_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 571))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 571) 5604) = 19337 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b571_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 571)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 571)) 5604) = 19337 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a571_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 571))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 571) 221549) = 222933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b571_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 571)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 571)) 221549) = 222933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a571_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 571))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 571) 266275) = 116383 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b571_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 571)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 571)) 266275) = 116383 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a571_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 571))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 571) 186844) = 299274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b571_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 571)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 571)) 186844) = 299274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o571 : xone 571 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a571_0 b571_0 a571_1 b571_1 a571_2 b571_2
    a571_3 b571_3 a571_4 b571_4 a571_5 b571_5

theorem a572_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 572))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 572) 0) = 63493 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b572_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 572)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 572)) 0) = 63493 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a572_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 572))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 572) 305530) = 270022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b572_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 572)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 572)) 305530) = 270022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a572_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 572))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 572) 5604) = 20808 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b572_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 572)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 572)) 5604) = 20808 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a572_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 572))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 572) 221549) = 64950 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b572_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 572)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 572)) 221549) = 64950 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a572_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 572))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 572) 266275) = 215191 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b572_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 572)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 572)) 266275) = 215191 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a572_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 572))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 572) 186844) = 191930 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b572_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 572)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 572)) 186844) = 191930 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o572 : xone 572 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a572_0 b572_0 a572_1 b572_1 a572_2 b572_2
    a572_3 b572_3 a572_4 b572_4 a572_5 b572_5

theorem a573_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 573))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 573) 0) = 4596 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b573_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 573)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 573)) 0) = 4596 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a573_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 573))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 573) 305530) = 230157 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b573_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 573)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 573)) 305530) = 230157 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a573_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 573))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 573) 5604) = 250486 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b573_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 573)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 573)) 5604) = 250486 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a573_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 573))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 573) 221549) = 81160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b573_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 573)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 573)) 221549) = 81160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a573_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 573))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 573) 266275) = 229122 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b573_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 573)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 573)) 266275) = 229122 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a573_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 573))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 573) 186844) = 111261 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b573_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 573)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 573)) 186844) = 111261 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o573 : xone 573 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a573_0 b573_0 a573_1 b573_1 a573_2 b573_2
    a573_3 b573_3 a573_4 b573_4 a573_5 b573_5

theorem a574_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 574))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 574) 0) = 211160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b574_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 574)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 574)) 0) = 211160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a574_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 574))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 574) 305530) = 198592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b574_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 574)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 574)) 305530) = 198592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a574_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 574))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 574) 5604) = 78472 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b574_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 574)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 574)) 5604) = 78472 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a574_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 574))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 574) 221549) = 142155 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b574_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 574)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 574)) 221549) = 142155 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a574_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 574))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 574) 266275) = 217886 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b574_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 574)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 574)) 266275) = 217886 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a574_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 574))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 574) 186844) = 288986 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b574_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 574)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 574)) 186844) = 288986 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o574 : xone 574 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a574_0 b574_0 a574_1 b574_1 a574_2 b574_2
    a574_3 b574_3 a574_4 b574_4 a574_5 b574_5

theorem a575_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 575))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 575) 0) = 237545 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b575_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 575)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 575)) 0) = 237545 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a575_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 575))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 575) 305530) = 152496 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b575_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 575)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 575)) 305530) = 152496 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a575_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 575))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 575) 5604) = 46282 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b575_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 575)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 575)) 5604) = 46282 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a575_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 575))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 575) 221549) = 243690 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b575_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 575)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 575)) 221549) = 243690 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a575_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 575))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 575) 266275) = 244492 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b575_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 575)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 575)) 266275) = 244492 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a575_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 575))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 575) 186844) = 210964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b575_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 575)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 575)) 186844) = 210964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o575 : xone 575 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a575_0 b575_0 a575_1 b575_1 a575_2 b575_2
    a575_3 b575_3 a575_4 b575_4 a575_5 b575_5

theorem a576_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 576))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 576) 0) = 166751 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b576_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 576)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 576)) 0) = 166751 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a576_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 576))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 576) 305530) = 68287 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b576_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 576)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 576)) 305530) = 68287 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a576_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 576))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 576) 5604) = 84061 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b576_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 576)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 576)) 5604) = 84061 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a576_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 576))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 576) 221549) = 200910 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b576_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 576)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 576)) 221549) = 200910 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a576_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 576))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 576) 266275) = 108287 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b576_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 576)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 576)) 266275) = 108287 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a576_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 576))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 576) 186844) = 184511 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b576_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 576)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 576)) 186844) = 184511 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o576 : xone 576 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a576_0 b576_0 a576_1 b576_1 a576_2 b576_2
    a576_3 b576_3 a576_4 b576_4 a576_5 b576_5

theorem a577_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 577))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 577) 0) = 46605 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b577_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 577)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 577)) 0) = 46605 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a577_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 577))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 577) 305530) = 114620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b577_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 577)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 577)) 305530) = 114620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a577_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 577))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 577) 5604) = 9987 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b577_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 577)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 577)) 5604) = 9987 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a577_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 577))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 577) 221549) = 293024 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b577_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 577)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 577)) 221549) = 293024 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a577_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 577))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 577) 266275) = 233077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b577_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 577)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 577)) 266275) = 233077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a577_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 577))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 577) 186844) = 135770 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b577_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 577)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 577)) 186844) = 135770 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o577 : xone 577 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a577_0 b577_0 a577_1 b577_1 a577_2 b577_2
    a577_3 b577_3 a577_4 b577_4 a577_5 b577_5

theorem a578_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 578))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 578) 0) = 64925 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b578_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 578)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 578)) 0) = 64925 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a578_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 578))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 578) 305530) = 140144 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b578_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 578)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 578)) 305530) = 140144 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a578_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 578))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 578) 5604) = 76702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b578_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 578)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 578)) 5604) = 76702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a578_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 578))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 578) 221549) = 198573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b578_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 578)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 578)) 221549) = 198573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a578_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 578))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 578) 266275) = 75436 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b578_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 578)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 578)) 266275) = 75436 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a578_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 578))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 578) 186844) = 59399 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b578_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 578)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 578)) 186844) = 59399 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o578 : xone 578 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a578_0 b578_0 a578_1 b578_1 a578_2 b578_2
    a578_3 b578_3 a578_4 b578_4 a578_5 b578_5

theorem a579_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 579))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 579) 0) = 223415 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b579_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 579)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 579)) 0) = 223415 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a579_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 579))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 579) 305530) = 151579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b579_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 579)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 579)) 305530) = 151579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a579_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 579))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 579) 5604) = 94668 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b579_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 579)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 579)) 5604) = 94668 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a579_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 579))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 579) 221549) = 218569 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b579_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 579)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 579)) 221549) = 218569 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a579_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 579))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 579) 266275) = 72055 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b579_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 579)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 579)) 266275) = 72055 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a579_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 579))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 579) 186844) = 231554 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b579_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 579)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 579)) 186844) = 231554 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o579 : xone 579 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a579_0 b579_0 a579_1 b579_1 a579_2 b579_2
    a579_3 b579_3 a579_4 b579_4 a579_5 b579_5

theorem a580_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 580))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 580) 0) = 292839 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b580_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 580)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 580)) 0) = 292839 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a580_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 580))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 580) 305530) = 172200 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b580_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 580)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 580)) 305530) = 172200 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a580_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 580))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 580) 5604) = 109159 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b580_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 580)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 580)) 5604) = 109159 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a580_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 580))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 580) 221549) = 298989 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b580_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 580)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 580)) 221549) = 298989 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a580_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 580))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 580) 266275) = 35844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b580_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 580)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 580)) 266275) = 35844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a580_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 580))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 580) 186844) = 206335 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b580_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 580)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 580)) 186844) = 206335 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o580 : xone 580 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a580_0 b580_0 a580_1 b580_1 a580_2 b580_2
    a580_3 b580_3 a580_4 b580_4 a580_5 b580_5

theorem a581_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 581))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 581) 0) = 29762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b581_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 581)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 581)) 0) = 29762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a581_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 581))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 581) 305530) = 99287 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b581_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 581)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 581)) 305530) = 99287 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a581_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 581))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 581) 5604) = 280348 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b581_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 581)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 581)) 5604) = 280348 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a581_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 581))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 581) 221549) = 27391 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b581_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 581)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 581)) 221549) = 27391 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a581_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 581))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 581) 266275) = 72221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b581_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 581)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 581)) 266275) = 72221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a581_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 581))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 581) 186844) = 257924 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b581_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 581)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 581)) 186844) = 257924 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o581 : xone 581 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a581_0 b581_0 a581_1 b581_1 a581_2 b581_2
    a581_3 b581_3 a581_4 b581_4 a581_5 b581_5

theorem a582_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 582))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 582) 0) = 106892 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b582_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 582)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 582)) 0) = 106892 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a582_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 582))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 582) 305530) = 69200 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b582_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 582)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 582)) 305530) = 69200 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a582_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 582))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 582) 5604) = 73577 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b582_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 582)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 582)) 5604) = 73577 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a582_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 582))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 582) 221549) = 154870 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b582_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 582)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 582)) 221549) = 154870 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a582_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 582))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 582) 266275) = 282539 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b582_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 582)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 582)) 266275) = 282539 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a582_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 582))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 582) 186844) = 269551 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b582_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 582)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 582)) 186844) = 269551 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o582 : xone 582 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a582_0 b582_0 a582_1 b582_1 a582_2 b582_2
    a582_3 b582_3 a582_4 b582_4 a582_5 b582_5

theorem a583_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 583))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 583) 0) = 125253 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b583_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 583)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 583)) 0) = 125253 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a583_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 583))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 583) 305530) = 275566 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b583_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 583)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 583)) 305530) = 275566 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a583_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 583))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 583) 5604) = 245013 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b583_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 583)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 583)) 5604) = 245013 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a583_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 583))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 583) 221549) = 158602 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b583_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 583)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 583)) 221549) = 158602 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a583_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 583))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 583) 266275) = 240375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b583_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 583)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 583)) 266275) = 240375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a583_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 583))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 583) 186844) = 176702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b583_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 583)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 583)) 186844) = 176702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o583 : xone 583 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a583_0 b583_0 a583_1 b583_1 a583_2 b583_2
    a583_3 b583_3 a583_4 b583_4 a583_5 b583_5

theorem a584_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 584))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 584) 0) = 214525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b584_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 584)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 584)) 0) = 214525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a584_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 584))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 584) 305530) = 168964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b584_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 584)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 584)) 305530) = 168964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a584_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 584))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 584) 5604) = 155768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b584_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 584)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 584)) 5604) = 155768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a584_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 584))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 584) 221549) = 42336 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b584_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 584)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 584)) 221549) = 42336 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a584_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 584))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 584) 266275) = 169163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b584_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 584)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 584)) 266275) = 169163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a584_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 584))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 584) 186844) = 63096 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b584_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 584)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 584)) 186844) = 63096 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o584 : xone 584 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a584_0 b584_0 a584_1 b584_1 a584_2 b584_2
    a584_3 b584_3 a584_4 b584_4 a584_5 b584_5

theorem a585_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 585))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 585) 0) = 165336 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b585_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 585)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 585)) 0) = 165336 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a585_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 585))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 585) 305530) = 19141 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b585_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 585)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 585)) 305530) = 19141 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a585_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 585))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 585) 5604) = 68700 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b585_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 585)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 585)) 5604) = 68700 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a585_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 585))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 585) 221549) = 122022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b585_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 585)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 585)) 221549) = 122022 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a585_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 585))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 585) 266275) = 162449 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b585_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 585)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 585)) 266275) = 162449 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a585_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 585))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 585) 186844) = 47038 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b585_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 585)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 585)) 186844) = 47038 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o585 : xone 585 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a585_0 b585_0 a585_1 b585_1 a585_2 b585_2
    a585_3 b585_3 a585_4 b585_4 a585_5 b585_5

theorem a586_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 586))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 586) 0) = 181784 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b586_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 586)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 586)) 0) = 181784 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a586_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 586))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 586) 305530) = 251304 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b586_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 586)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 586)) 305530) = 251304 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a586_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 586))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 586) 5604) = 241898 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b586_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 586)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 586)) 5604) = 241898 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a586_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 586))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 586) 221549) = 295711 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b586_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 586)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 586)) 221549) = 295711 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a586_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 586))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 586) 266275) = 33456 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b586_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 586)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 586)) 266275) = 33456 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a586_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 586))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 586) 186844) = 34849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b586_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 586)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 586)) 186844) = 34849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o586 : xone 586 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a586_0 b586_0 a586_1 b586_1 a586_2 b586_2
    a586_3 b586_3 a586_4 b586_4 a586_5 b586_5

theorem a587_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 587))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 587) 0) = 120889 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b587_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 587)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 587)) 0) = 120889 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a587_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 587))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 587) 305530) = 198462 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b587_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 587)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 587)) 305530) = 198462 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a587_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 587))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 587) 5604) = 58306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b587_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 587)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 587)) 5604) = 58306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a587_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 587))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 587) 221549) = 115651 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b587_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 587)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 587)) 221549) = 115651 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a587_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 587))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 587) 266275) = 19143 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b587_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 587)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 587)) 266275) = 19143 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a587_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 587))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 587) 186844) = 133799 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b587_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 587)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 587)) 186844) = 133799 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o587 : xone 587 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a587_0 b587_0 a587_1 b587_1 a587_2 b587_2
    a587_3 b587_3 a587_4 b587_4 a587_5 b587_5

theorem a588_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 588))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 588) 0) = 156424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b588_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 588)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 588)) 0) = 156424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a588_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 588))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 588) 305530) = 98610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b588_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 588)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 588)) 305530) = 98610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a588_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 588))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 588) 5604) = 69314 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b588_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 588)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 588)) 5604) = 69314 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a588_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 588))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 588) 221549) = 131563 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b588_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 588)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 588)) 221549) = 131563 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a588_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 588))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 588) 266275) = 171324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b588_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 588)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 588)) 266275) = 171324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a588_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 588))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 588) 186844) = 97240 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b588_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 588)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 588)) 186844) = 97240 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o588 : xone 588 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a588_0 b588_0 a588_1 b588_1 a588_2 b588_2
    a588_3 b588_3 a588_4 b588_4 a588_5 b588_5

theorem a589_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 589))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 589) 0) = 168768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b589_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 589)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 589)) 0) = 168768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a589_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 589))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 589) 305530) = 252417 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b589_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 589)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 589)) 305530) = 252417 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a589_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 589))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 589) 5604) = 297669 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b589_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 589)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 589)) 5604) = 297669 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a589_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 589))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 589) 221549) = 285229 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b589_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 589)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 589)) 221549) = 285229 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a589_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 589))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 589) 266275) = 114876 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b589_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 589)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 589)) 266275) = 114876 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a589_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 589))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 589) 186844) = 32051 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b589_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 589)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 589)) 186844) = 32051 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o589 : xone 589 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a589_0 b589_0 a589_1 b589_1 a589_2 b589_2
    a589_3 b589_3 a589_4 b589_4 a589_5 b589_5

theorem a590_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 590))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 590) 0) = 5386 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b590_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 590)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 590)) 0) = 5386 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a590_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 590))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 590) 305530) = 142619 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b590_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 590)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 590)) 305530) = 142619 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a590_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 590))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 590) 5604) = 248688 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b590_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 590)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 590)) 5604) = 248688 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a590_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 590))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 590) 221549) = 53636 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b590_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 590)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 590)) 221549) = 53636 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a590_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 590))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 590) 266275) = 229841 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b590_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 590)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 590)) 266275) = 229841 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a590_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 590))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 590) 186844) = 263803 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b590_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 590)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 590)) 186844) = 263803 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o590 : xone 590 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a590_0 b590_0 a590_1 b590_1 a590_2 b590_2
    a590_3 b590_3 a590_4 b590_4 a590_5 b590_5

theorem a591_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 591))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 591) 0) = 184672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b591_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 591)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 591)) 0) = 184672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a591_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 591))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 591) 305530) = 111682 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b591_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 591)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 591)) 305530) = 111682 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a591_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 591))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 591) 5604) = 270522 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b591_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 591)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 591)) 5604) = 270522 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a591_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 591))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 591) 221549) = 214721 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b591_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 591)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 591)) 221549) = 214721 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a591_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 591))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 591) 266275) = 70812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b591_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 591)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 591)) 266275) = 70812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a591_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 591))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 591) 186844) = 275888 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b591_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 591)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 591)) 186844) = 275888 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o591 : xone 591 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a591_0 b591_0 a591_1 b591_1 a591_2 b591_2
    a591_3 b591_3 a591_4 b591_4 a591_5 b591_5

theorem a592_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 592))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 592) 0) = 239891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b592_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 592)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 592)) 0) = 239891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a592_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 592))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 592) 305530) = 294673 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b592_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 592)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 592)) 305530) = 294673 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a592_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 592))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 592) 5604) = 207710 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b592_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 592)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 592)) 5604) = 207710 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a592_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 592))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 592) 221549) = 274199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b592_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 592)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 592)) 221549) = 274199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a592_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 592))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 592) 266275) = 297277 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b592_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 592)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 592)) 266275) = 297277 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a592_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 592))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 592) 186844) = 234811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b592_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 592)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 592)) 186844) = 234811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o592 : xone 592 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a592_0 b592_0 a592_1 b592_1 a592_2 b592_2
    a592_3 b592_3 a592_4 b592_4 a592_5 b592_5

theorem a593_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 593))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 593) 0) = 305530 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b593_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 593)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 593)) 0) = 305530 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a593_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 593))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 593) 305530) = 233144 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b593_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 593)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 593)) 305530) = 233144 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a593_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 593))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 593) 5604) = 10668 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b593_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 593)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 593)) 5604) = 10668 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a593_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 593))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 593) 221549) = 294240 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b593_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 593)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 593)) 221549) = 294240 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a593_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 593))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 593) 266275) = 59409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b593_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 593)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 593)) 266275) = 59409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a593_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 593))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 593) 186844) = 13592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b593_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 593)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 593)) 186844) = 13592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o593 : xone 593 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a593_0 b593_0 a593_1 b593_1 a593_2 b593_2
    a593_3 b593_3 a593_4 b593_4 a593_5 b593_5

theorem a594_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 594))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 594) 0) = 271393 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b594_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 594)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 594)) 0) = 271393 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a594_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 594))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 594) 305530) = 33979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b594_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 594)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 594)) 305530) = 33979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a594_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 594))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 594) 5604) = 208662 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b594_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 594)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 594)) 5604) = 208662 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a594_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 594))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 594) 221549) = 202491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b594_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 594)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 594)) 221549) = 202491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a594_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 594))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 594) 266275) = 200386 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b594_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 594)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 594)) 266275) = 200386 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a594_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 594))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 594) 186844) = 246244 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b594_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 594)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 594)) 186844) = 246244 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o594 : xone 594 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a594_0 b594_0 a594_1 b594_1 a594_2 b594_2
    a594_3 b594_3 a594_4 b594_4 a594_5 b594_5

theorem a595_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 595))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 595) 0) = 235961 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b595_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 595)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 595)) 0) = 235961 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a595_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 595))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 595) 305530) = 41132 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b595_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 595)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 595)) 305530) = 41132 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a595_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 595))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 595) 5604) = 185951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b595_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 595)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 595)) 5604) = 185951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a595_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 595))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 595) 221549) = 156007 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b595_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 595)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 595)) 221549) = 156007 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a595_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 595))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 595) 266275) = 300459 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b595_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 595)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 595)) 266275) = 300459 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a595_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 595))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 595) 186844) = 256315 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b595_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 595)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 595)) 186844) = 256315 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o595 : xone 595 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a595_0 b595_0 a595_1 b595_1 a595_2 b595_2
    a595_3 b595_3 a595_4 b595_4 a595_5 b595_5

theorem a596_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 596))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 596) 0) = 63825 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b596_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 596)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 596)) 0) = 63825 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a596_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 596))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 596) 305530) = 137623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b596_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 596)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 596)) 305530) = 137623 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a596_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 596))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 596) 5604) = 167636 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b596_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 596)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 596)) 5604) = 167636 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a596_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 596))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 596) 221549) = 241495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b596_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 596)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 596)) 221549) = 241495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a596_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 596))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 596) 266275) = 218622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b596_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 596)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 596)) 266275) = 218622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a596_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 596))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 596) 186844) = 286795 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b596_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 596)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 596)) 186844) = 286795 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o596 : xone 596 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a596_0 b596_0 a596_1 b596_1 a596_2 b596_2
    a596_3 b596_3 a596_4 b596_4 a596_5 b596_5

theorem a597_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 597))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 597) 0) = 156724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b597_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 597)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 597)) 0) = 156724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a597_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 597))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 597) 305530) = 277043 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b597_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 597)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 597)) 305530) = 277043 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a597_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 597))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 597) 5604) = 177978 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b597_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 597)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 597)) 5604) = 177978 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a597_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 597))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 597) 221549) = 24754 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b597_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 597)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 597)) 221549) = 24754 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a597_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 597))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 597) 266275) = 230265 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b597_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 597)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 597)) 266275) = 230265 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a597_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 597))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 597) 186844) = 306160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b597_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 597)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 597)) 186844) = 306160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o597 : xone 597 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a597_0 b597_0 a597_1 b597_1 a597_2 b597_2
    a597_3 b597_3 a597_4 b597_4 a597_5 b597_5

theorem a598_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 598))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 598) 0) = 5209 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b598_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 598)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 598)) 0) = 5209 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a598_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 598))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 598) 305530) = 227081 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b598_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 598)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 598)) 305530) = 227081 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a598_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 598))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 598) 5604) = 109426 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b598_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 598)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 598)) 5604) = 109426 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a598_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 598))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 598) 221549) = 82371 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b598_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 598)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 598)) 221549) = 82371 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a598_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 598))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 598) 266275) = 27279 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b598_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 598)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 598)) 266275) = 27279 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a598_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 598))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 598) 186844) = 113847 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b598_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 598)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 598)) 186844) = 113847 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o598 : xone 598 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a598_0 b598_0 a598_1 b598_1 a598_2 b598_2
    a598_3 b598_3 a598_4 b598_4 a598_5 b598_5

theorem a599_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 599))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 599) 0) = 11542 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b599_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 599)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 599)) 0) = 11542 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a599_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 599))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 599) 305530) = 91042 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b599_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 599)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 599)) 305530) = 91042 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a599_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 599))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 599) 5604) = 157425 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b599_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 599)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 599)) 5604) = 157425 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a599_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 599))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 599) 221549) = 9411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b599_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 599)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 599)) 221549) = 9411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a599_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 599))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 599) 266275) = 171693 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b599_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 599)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 599)) 266275) = 171693 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a599_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 599))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 599) 186844) = 268618 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b599_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 599)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 599)) 186844) = 268618 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o599 : xone 599 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a599_0 b599_0 a599_1 b599_1 a599_2 b599_2
    a599_3 b599_3 a599_4 b599_4 a599_5 b599_5

theorem a600_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 600))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 600) 0) = 156844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b600_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 600)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 600)) 0) = 156844 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a600_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 600))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 600) 305530) = 150349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b600_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 600)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 600)) 305530) = 150349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a600_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 600))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 600) 5604) = 46141 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b600_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 600)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 600)) 5604) = 46141 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a600_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 600))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 600) 221549) = 229669 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b600_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 600)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 600)) 221549) = 229669 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a600_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 600))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 600) 266275) = 178546 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b600_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 600)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 600)) 266275) = 178546 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a600_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 600))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 600) 186844) = 190168 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b600_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 600)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 600)) 186844) = 190168 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o600 : xone 600 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a600_0 b600_0 a600_1 b600_1 a600_2 b600_2
    a600_3 b600_3 a600_4 b600_4 a600_5 b600_5

theorem a601_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 601))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 601) 0) = 113072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b601_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 601)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 601)) 0) = 113072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a601_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 601))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 601) 305530) = 20971 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b601_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 601)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 601)) 305530) = 20971 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a601_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 601))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 601) 5604) = 23990 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b601_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 601)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 601)) 5604) = 23990 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a601_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 601))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 601) 221549) = 100362 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b601_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 601)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 601)) 221549) = 100362 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a601_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 601))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 601) 266275) = 195105 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b601_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 601)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 601)) 266275) = 195105 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a601_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 601))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 601) 186844) = 85285 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b601_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 601)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 601)) 186844) = 85285 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o601 : xone 601 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a601_0 b601_0 a601_1 b601_1 a601_2 b601_2
    a601_3 b601_3 a601_4 b601_4 a601_5 b601_5

theorem a602_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 602))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 602) 0) = 191333 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b602_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 602)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 602)) 0) = 191333 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a602_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 602))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 602) 305530) = 66149 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b602_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 602)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 602)) 305530) = 66149 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a602_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 602))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 602) 5604) = 14497 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b602_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 602)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 602)) 5604) = 14497 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a602_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 602))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 602) 221549) = 265674 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b602_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 602)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 602)) 221549) = 265674 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a602_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 602))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 602) 266275) = 248953 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b602_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 602)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 602)) 266275) = 248953 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a602_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 602))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 602) 186844) = 119981 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b602_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 602)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 602)) 186844) = 119981 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o602 : xone 602 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a602_0 b602_0 a602_1 b602_1 a602_2 b602_2
    a602_3 b602_3 a602_4 b602_4 a602_5 b602_5

theorem a603_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 603))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 603) 0) = 65540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b603_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 603)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 603)) 0) = 65540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a603_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 603))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 603) 305530) = 195498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b603_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 603)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 603)) 305530) = 195498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a603_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 603))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 603) 5604) = 207243 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b603_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 603)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 603)) 5604) = 207243 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a603_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 603))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 603) 221549) = 295229 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b603_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 603)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 603)) 221549) = 295229 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a603_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 603))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 603) 266275) = 173135 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b603_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 603)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 603)) 266275) = 173135 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a603_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 603))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 603) 186844) = 16451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b603_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 603)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 603)) 186844) = 16451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o603 : xone 603 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a603_0 b603_0 a603_1 b603_1 a603_2 b603_2
    a603_3 b603_3 a603_4 b603_4 a603_5 b603_5

theorem a604_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 604))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 604) 0) = 29454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b604_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 604)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 604)) 0) = 29454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a604_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 604))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 604) 305530) = 126863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b604_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 604)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 604)) 305530) = 126863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a604_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 604))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 604) 5604) = 85461 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b604_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 604)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 604)) 5604) = 85461 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a604_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 604))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 604) 221549) = 266087 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b604_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 604)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 604)) 221549) = 266087 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a604_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 604))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 604) 266275) = 237696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b604_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 604)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 604)) 266275) = 237696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a604_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 604))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 604) 186844) = 141247 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b604_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 604)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 604)) 186844) = 141247 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o604 : xone 604 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a604_0 b604_0 a604_1 b604_1 a604_2 b604_2
    a604_3 b604_3 a604_4 b604_4 a604_5 b604_5

theorem a605_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 605))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 605) 0) = 290201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b605_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 605)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 605)) 0) = 290201 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a605_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 605))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 605) 305530) = 163964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b605_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 605)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 605)) 305530) = 163964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a605_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 605))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 605) 5604) = 68521 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b605_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 605)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 605)) 5604) = 68521 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a605_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 605))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 605) 221549) = 265955 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b605_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 605)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 605)) 221549) = 265955 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a605_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 605))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 605) 266275) = 191441 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b605_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 605)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 605)) 266275) = 191441 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a605_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 605))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 605) 186844) = 80601 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b605_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 605)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 605)) 186844) = 80601 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o605 : xone 605 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a605_0 b605_0 a605_1 b605_1 a605_2 b605_2
    a605_3 b605_3 a605_4 b605_4 a605_5 b605_5

theorem a606_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 606))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 606) 0) = 93026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b606_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 606)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 606)) 0) = 93026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a606_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 606))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 606) 305530) = 118589 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b606_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 606)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 606)) 305530) = 118589 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a606_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 606))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 606) 5604) = 244586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b606_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 606)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 606)) 5604) = 244586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a606_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 606))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 606) 221549) = 252220 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b606_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 606)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 606)) 221549) = 252220 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a606_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 606))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 606) 266275) = 138720 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b606_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 606)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 606)) 266275) = 138720 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a606_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 606))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 606) 186844) = 132254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b606_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 606)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 606)) 186844) = 132254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o606 : xone 606 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a606_0 b606_0 a606_1 b606_1 a606_2 b606_2
    a606_3 b606_3 a606_4 b606_4 a606_5 b606_5

theorem a607_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 607))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 607) 0) = 53889 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b607_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 607)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 607)) 0) = 53889 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a607_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 607))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 607) 305530) = 257570 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b607_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 607)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 607)) 305530) = 257570 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a607_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 607))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 607) 5604) = 277813 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b607_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 607)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 607)) 5604) = 277813 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a607_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 607))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 607) 221549) = 158027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b607_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 607)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 607)) 221549) = 158027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a607_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 607))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 607) 266275) = 202324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b607_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 607)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 607)) 266275) = 202324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a607_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 607))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 607) 186844) = 68941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b607_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 607)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 607)) 186844) = 68941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o607 : xone 607 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a607_0 b607_0 a607_1 b607_1 a607_2 b607_2
    a607_3 b607_3 a607_4 b607_4 a607_5 b607_5

theorem a608_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 608))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 608) 0) = 14960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b608_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 608)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 608)) 0) = 14960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a608_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 608))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 608) 305530) = 912 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b608_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 608)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 608)) 305530) = 912 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a608_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 608))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 608) 5604) = 301712 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b608_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 608)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 608)) 5604) = 301712 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a608_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 608))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 608) 221549) = 45103 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b608_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 608)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 608)) 221549) = 45103 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a608_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 608))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 608) 266275) = 32241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b608_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 608)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 608)) 266275) = 32241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a608_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 608))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 608) 186844) = 181188 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b608_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 608)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 608)) 186844) = 181188 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o608 : xone 608 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a608_0 b608_0 a608_1 b608_1 a608_2 b608_2
    a608_3 b608_3 a608_4 b608_4 a608_5 b608_5

theorem a609_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 609))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 609) 0) = 54971 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b609_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 609)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 609)) 0) = 54971 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a609_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 609))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 609) 305530) = 220747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b609_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 609)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 609)) 305530) = 220747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a609_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 609))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 609) 5604) = 254099 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b609_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 609)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 609)) 5604) = 254099 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a609_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 609))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 609) 221549) = 150988 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b609_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 609)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 609)) 221549) = 150988 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a609_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 609))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 609) 266275) = 206232 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b609_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 609)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 609)) 266275) = 206232 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a609_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 609))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 609) 186844) = 67163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b609_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 609)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 609)) 186844) = 67163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o609 : xone 609 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a609_0 b609_0 a609_1 b609_1 a609_2 b609_2
    a609_3 b609_3 a609_4 b609_4 a609_5 b609_5

theorem a610_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 610))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 610) 0) = 231900 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b610_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 610)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 610)) 0) = 231900 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a610_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 610))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 610) 305530) = 260731 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b610_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 610)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 610)) 305530) = 260731 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a610_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 610))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 610) 5604) = 294803 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b610_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 610)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 610)) 5604) = 294803 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a610_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 610))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 610) 221549) = 270826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b610_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 610)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 610)) 221549) = 270826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a610_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 610))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 610) 266275) = 132547 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b610_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 610)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 610)) 266275) = 132547 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a610_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 610))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 610) 186844) = 38310 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b610_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 610)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 610)) 186844) = 38310 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o610 : xone 610 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a610_0 b610_0 a610_1 b610_1 a610_2 b610_2
    a610_3 b610_3 a610_4 b610_4 a610_5 b610_5

theorem a611_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 611))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 611) 0) = 67093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b611_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 611)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 611)) 0) = 67093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a611_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 611))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 611) 305530) = 140646 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b611_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 611)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 611)) 305530) = 140646 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a611_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 611))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 611) 5604) = 245841 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b611_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 611)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 611)) 5604) = 245841 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a611_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 611))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 611) 221549) = 248838 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b611_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 611)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 611)) 221549) = 248838 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a611_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 611))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 611) 266275) = 267273 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b611_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 611)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 611)) 266275) = 267273 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a611_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 611))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 611) 186844) = 25347 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b611_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 611)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 611)) 186844) = 25347 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o611 : xone 611 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a611_0 b611_0 a611_1 b611_1 a611_2 b611_2
    a611_3 b611_3 a611_4 b611_4 a611_5 b611_5

theorem a612_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 612))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 612) 0) = 175269 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b612_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 612)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 612)) 0) = 175269 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a612_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 612))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 612) 305530) = 116921 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b612_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 612)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 612)) 305530) = 116921 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a612_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 612))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 612) 5604) = 84192 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b612_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 612)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 612)) 5604) = 84192 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a612_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 612))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 612) 221549) = 256802 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b612_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 612)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 612)) 221549) = 256802 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a612_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 612))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 612) 266275) = 247194 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b612_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 612)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 612)) 266275) = 247194 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a612_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 612))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 612) 186844) = 219410 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b612_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 612)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 612)) 186844) = 219410 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o612 : xone 612 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a612_0 b612_0 a612_1 b612_1 a612_2 b612_2
    a612_3 b612_3 a612_4 b612_4 a612_5 b612_5

theorem a613_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 613))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 613) 0) = 67464 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b613_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 613)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 613)) 0) = 67464 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a613_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 613))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 613) 305530) = 216186 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b613_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 613)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 613)) 305530) = 216186 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a613_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 613))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 613) 5604) = 124502 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b613_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 613)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 613)) 5604) = 124502 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a613_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 613))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 613) 221549) = 271375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b613_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 613)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 613)) 221549) = 271375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a613_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 613))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 613) 266275) = 295625 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b613_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 613)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 613)) 266275) = 295625 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a613_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 613))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 613) 186844) = 177154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b613_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 613)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 613)) 186844) = 177154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o613 : xone 613 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a613_0 b613_0 a613_1 b613_1 a613_2 b613_2
    a613_3 b613_3 a613_4 b613_4 a613_5 b613_5

theorem a614_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 614))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 614) 0) = 27687 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b614_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 614)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 614)) 0) = 27687 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a614_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 614))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 614) 305530) = 190181 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b614_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 614)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 614)) 305530) = 190181 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a614_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 614))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 614) 5604) = 303842 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b614_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 614)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 614)) 5604) = 303842 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a614_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 614))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 614) 221549) = 84506 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b614_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 614)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 614)) 221549) = 84506 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a614_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 614))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 614) 266275) = 122031 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b614_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 614)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 614)) 266275) = 122031 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a614_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 614))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 614) 186844) = 276309 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b614_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 614)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 614)) 186844) = 276309 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o614 : xone 614 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a614_0 b614_0 a614_1 b614_1 a614_2 b614_2
    a614_3 b614_3 a614_4 b614_4 a614_5 b614_5

theorem a615_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 615))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 615) 0) = 230929 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b615_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 615)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 615)) 0) = 230929 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a615_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 615))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 615) 305530) = 13892 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b615_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 615)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 615)) 305530) = 13892 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a615_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 615))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 615) 5604) = 81493 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b615_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 615)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 615)) 5604) = 81493 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a615_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 615))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 615) 221549) = 250275 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b615_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 615)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 615)) 221549) = 250275 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a615_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 615))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 615) 266275) = 170205 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b615_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 615)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 615)) 266275) = 170205 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a615_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 615))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 615) 186844) = 77807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b615_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 615)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 615)) 186844) = 77807 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o615 : xone 615 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a615_0 b615_0 a615_1 b615_1 a615_2 b615_2
    a615_3 b615_3 a615_4 b615_4 a615_5 b615_5

theorem a616_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 616))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 616) 0) = 254835 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b616_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 616)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 616)) 0) = 254835 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a616_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 616))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 616) 305530) = 168756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b616_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 616)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 616)) 305530) = 168756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a616_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 616))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 616) 5604) = 305819 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b616_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 616)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 616)) 5604) = 305819 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a616_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 616))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 616) 221549) = 236849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b616_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 616)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 616)) 221549) = 236849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a616_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 616))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 616) 266275) = 32709 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b616_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 616)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 616)) 266275) = 32709 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a616_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 616))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 616) 186844) = 28086 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b616_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 616)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 616)) 186844) = 28086 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o616 : xone 616 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a616_0 b616_0 a616_1 b616_1 a616_2 b616_2
    a616_3 b616_3 a616_4 b616_4 a616_5 b616_5

theorem a617_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 617))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 617) 0) = 131016 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b617_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 617)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 617)) 0) = 131016 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a617_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 617))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 617) 305530) = 86206 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b617_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 617)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 617)) 305530) = 86206 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a617_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 617))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 617) 5604) = 257640 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b617_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 617)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 617)) 5604) = 257640 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a617_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 617))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 617) 221549) = 273209 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b617_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 617)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 617)) 221549) = 273209 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a617_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 617))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 617) 266275) = 225883 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b617_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 617)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 617)) 266275) = 225883 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a617_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 617))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 617) 186844) = 140327 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b617_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 617)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 617)) 186844) = 140327 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o617 : xone 617 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a617_0 b617_0 a617_1 b617_1 a617_2 b617_2
    a617_3 b617_3 a617_4 b617_4 a617_5 b617_5

theorem a618_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 618))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 618) 0) = 210401 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b618_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 618)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 618)) 0) = 210401 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a618_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 618))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 618) 305530) = 188492 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b618_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 618)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 618)) 305530) = 188492 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a618_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 618))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 618) 5604) = 29684 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b618_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 618)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 618)) 5604) = 29684 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a618_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 618))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 618) 221549) = 72433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b618_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 618)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 618)) 221549) = 72433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a618_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 618))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 618) 266275) = 303016 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b618_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 618)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 618)) 266275) = 303016 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a618_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 618))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 618) 186844) = 13599 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b618_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 618)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 618)) 186844) = 13599 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o618 : xone 618 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a618_0 b618_0 a618_1 b618_1 a618_2 b618_2
    a618_3 b618_3 a618_4 b618_4 a618_5 b618_5

theorem a619_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 619))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 619) 0) = 279335 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b619_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 619)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 619)) 0) = 279335 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a619_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 619))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 619) 305530) = 177109 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b619_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 619)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 619)) 305530) = 177109 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a619_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 619))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 619) 5604) = 234218 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b619_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 619)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 619)) 5604) = 234218 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a619_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 619))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 619) 221549) = 48345 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b619_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 619)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 619)) 221549) = 48345 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a619_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 619))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 619) 266275) = 242957 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b619_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 619)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 619)) 266275) = 242957 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a619_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 619))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 619) 186844) = 184118 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b619_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 619)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 619)) 186844) = 184118 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o619 : xone 619 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a619_0 b619_0 a619_1 b619_1 a619_2 b619_2
    a619_3 b619_3 a619_4 b619_4 a619_5 b619_5

theorem a620_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 620))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 620) 0) = 69389 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b620_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 620)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 620)) 0) = 69389 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a620_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 620))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 620) 305530) = 80488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b620_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 620)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 620)) 305530) = 80488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a620_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 620))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 620) 5604) = 207238 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b620_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 620)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 620)) 5604) = 207238 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a620_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 620))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 620) 221549) = 15729 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b620_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 620)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 620)) 221549) = 15729 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a620_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 620))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 620) 266275) = 76949 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b620_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 620)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 620)) 266275) = 76949 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a620_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 620))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 620) 186844) = 169791 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b620_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 620)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 620)) 186844) = 169791 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o620 : xone 620 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a620_0 b620_0 a620_1 b620_1 a620_2 b620_2
    a620_3 b620_3 a620_4 b620_4 a620_5 b620_5

theorem a621_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 621))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 621) 0) = 180316 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b621_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 621)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 621)) 0) = 180316 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a621_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 621))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 621) 305530) = 222061 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b621_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 621)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 621)) 305530) = 222061 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a621_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 621))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 621) 5604) = 29758 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b621_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 621)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 621)) 5604) = 29758 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a621_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 621))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 621) 221549) = 178289 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b621_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 621)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 621)) 221549) = 178289 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a621_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 621))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 621) 266275) = 28189 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b621_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 621)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 621)) 266275) = 28189 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a621_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 621))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 621) 186844) = 272472 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b621_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 621)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 621)) 186844) = 272472 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o621 : xone 621 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a621_0 b621_0 a621_1 b621_1 a621_2 b621_2
    a621_3 b621_3 a621_4 b621_4 a621_5 b621_5

theorem a622_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 622))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 622) 0) = 65453 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b622_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 622)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 622)) 0) = 65453 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a622_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 622))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 622) 305530) = 3877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b622_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 622)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 622)) 305530) = 3877 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a622_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 622))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 622) 5604) = 197354 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b622_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 622)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 622)) 5604) = 197354 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a622_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 622))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 622) 221549) = 293529 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b622_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 622)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 622)) 221549) = 293529 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a622_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 622))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 622) 266275) = 234354 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b622_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 622)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 622)) 266275) = 234354 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a622_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 622))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 622) 186844) = 296168 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b622_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 622)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 622)) 186844) = 296168 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o622 : xone 622 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a622_0 b622_0 a622_1 b622_1 a622_2 b622_2
    a622_3 b622_3 a622_4 b622_4 a622_5 b622_5

theorem a623_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 623))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 623) 0) = 117263 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b623_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 623)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 623)) 0) = 117263 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a623_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 623))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 623) 305530) = 306189 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b623_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 623)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 623)) 305530) = 306189 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a623_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 623))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 623) 5604) = 86010 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b623_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 623)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 623)) 5604) = 86010 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a623_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 623))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 623) 221549) = 128917 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b623_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 623)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 623)) 221549) = 128917 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a623_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 623))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 623) 266275) = 65615 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b623_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 623)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 623)) 266275) = 65615 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a623_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 623))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 623) 186844) = 23533 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b623_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 623)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 623)) 186844) = 23533 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o623 : xone 623 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a623_0 b623_0 a623_1 b623_1 a623_2 b623_2
    a623_3 b623_3 a623_4 b623_4 a623_5 b623_5

end CFSG.KD.Fi24Pc.Ck

public section

namespace CFSG.KD.Fi24Pc.Ck

theorem x52 : CFSG.KD.Fi24Pc.xck (nat_lit 52) = true :=
  xck_of o416 (by quickRfl) o417 (by quickRfl) o418 (by quickRfl) o419 (by quickRfl)
    o420 (by quickRfl) o421 (by quickRfl) o422 (by quickRfl) o423 (by quickRfl)

theorem x53 : CFSG.KD.Fi24Pc.xck (nat_lit 53) = true :=
  xck_of o424 (by quickRfl) o425 (by quickRfl) o426 (by quickRfl) o427 (by quickRfl)
    o428 (by quickRfl) o429 (by quickRfl) o430 (by quickRfl) o431 (by quickRfl)

theorem x54 : CFSG.KD.Fi24Pc.xck (nat_lit 54) = true :=
  xck_of o432 (by quickRfl) o433 (by quickRfl) o434 (by quickRfl) o435 (by quickRfl)
    o436 (by quickRfl) o437 (by quickRfl) o438 (by quickRfl) o439 (by quickRfl)

theorem x55 : CFSG.KD.Fi24Pc.xck (nat_lit 55) = true :=
  xck_of o440 (by quickRfl) o441 (by quickRfl) o442 (by quickRfl) o443 (by quickRfl)
    o444 (by quickRfl) o445 (by quickRfl) o446 (by quickRfl) o447 (by quickRfl)

theorem x56 : CFSG.KD.Fi24Pc.xck (nat_lit 56) = true :=
  xck_of o448 (by quickRfl) o449 (by quickRfl) o450 (by quickRfl) o451 (by quickRfl)
    o452 (by quickRfl) o453 (by quickRfl) o454 (by quickRfl) o455 (by quickRfl)

theorem x57 : CFSG.KD.Fi24Pc.xck (nat_lit 57) = true :=
  xck_of o456 (by quickRfl) o457 (by quickRfl) o458 (by quickRfl) o459 (by quickRfl)
    o460 (by quickRfl) o461 (by quickRfl) o462 (by quickRfl) o463 (by quickRfl)

theorem x58 : CFSG.KD.Fi24Pc.xck (nat_lit 58) = true :=
  xck_of o464 (by quickRfl) o465 (by quickRfl) o466 (by quickRfl) o467 (by quickRfl)
    o468 (by quickRfl) o469 (by quickRfl) o470 (by quickRfl) o471 (by quickRfl)

theorem x59 : CFSG.KD.Fi24Pc.xck (nat_lit 59) = true :=
  xck_of o472 (by quickRfl) o473 (by quickRfl) o474 (by quickRfl) o475 (by quickRfl)
    o476 (by quickRfl) o477 (by quickRfl) o478 (by quickRfl) o479 (by quickRfl)

theorem x60 : CFSG.KD.Fi24Pc.xck (nat_lit 60) = true :=
  xck_of o480 (by quickRfl) o481 (by quickRfl) o482 (by quickRfl) o483 (by quickRfl)
    o484 (by quickRfl) o485 (by quickRfl) o486 (by quickRfl) o487 (by quickRfl)

theorem x61 : CFSG.KD.Fi24Pc.xck (nat_lit 61) = true :=
  xck_of o488 (by quickRfl) o489 (by quickRfl) o490 (by quickRfl) o491 (by quickRfl)
    o492 (by quickRfl) o493 (by quickRfl) o494 (by quickRfl) o495 (by quickRfl)

theorem x62 : CFSG.KD.Fi24Pc.xck (nat_lit 62) = true :=
  xck_of o496 (by quickRfl) o497 (by quickRfl) o498 (by quickRfl) o499 (by quickRfl)
    o500 (by quickRfl) o501 (by quickRfl) o502 (by quickRfl) o503 (by quickRfl)

theorem x63 : CFSG.KD.Fi24Pc.xck (nat_lit 63) = true :=
  xck_of o504 (by quickRfl) o505 (by quickRfl) o506 (by quickRfl) o507 (by quickRfl)
    o508 (by quickRfl) o509 (by quickRfl) o510 (by quickRfl) o511 (by quickRfl)

theorem x64 : CFSG.KD.Fi24Pc.xck (nat_lit 64) = true :=
  xck_of o512 (by quickRfl) o513 (by quickRfl) o514 (by quickRfl) o515 (by quickRfl)
    o516 (by quickRfl) o517 (by quickRfl) o518 (by quickRfl) o519 (by quickRfl)

theorem x65 : CFSG.KD.Fi24Pc.xck (nat_lit 65) = true :=
  xck_of o520 (by quickRfl) o521 (by quickRfl) o522 (by quickRfl) o523 (by quickRfl)
    o524 (by quickRfl) o525 (by quickRfl) o526 (by quickRfl) o527 (by quickRfl)

theorem x66 : CFSG.KD.Fi24Pc.xck (nat_lit 66) = true :=
  xck_of o528 (by quickRfl) o529 (by quickRfl) o530 (by quickRfl) o531 (by quickRfl)
    o532 (by quickRfl) o533 (by quickRfl) o534 (by quickRfl) o535 (by quickRfl)

theorem x67 : CFSG.KD.Fi24Pc.xck (nat_lit 67) = true :=
  xck_of o536 (by quickRfl) o537 (by quickRfl) o538 (by quickRfl) o539 (by quickRfl)
    o540 (by quickRfl) o541 (by quickRfl) o542 (by quickRfl) o543 (by quickRfl)

theorem x68 : CFSG.KD.Fi24Pc.xck (nat_lit 68) = true :=
  xck_of o544 (by quickRfl) o545 (by quickRfl) o546 (by quickRfl) o547 (by quickRfl)
    o548 (by quickRfl) o549 (by quickRfl) o550 (by quickRfl) o551 (by quickRfl)

theorem x69 : CFSG.KD.Fi24Pc.xck (nat_lit 69) = true :=
  xck_of o552 (by quickRfl) o553 (by quickRfl) o554 (by quickRfl) o555 (by quickRfl)
    o556 (by quickRfl) o557 (by quickRfl) o558 (by quickRfl) o559 (by quickRfl)

theorem x70 : CFSG.KD.Fi24Pc.xck (nat_lit 70) = true :=
  xck_of o560 (by quickRfl) o561 (by quickRfl) o562 (by quickRfl) o563 (by quickRfl)
    o564 (by quickRfl) o565 (by quickRfl) o566 (by quickRfl) o567 (by quickRfl)

theorem x71 : CFSG.KD.Fi24Pc.xck (nat_lit 71) = true :=
  xck_of o568 (by quickRfl) o569 (by quickRfl) o570 (by quickRfl) o571 (by quickRfl)
    o572 (by quickRfl) o573 (by quickRfl) o574 (by quickRfl) o575 (by quickRfl)

theorem x72 : CFSG.KD.Fi24Pc.xck (nat_lit 72) = true :=
  xck_of o576 (by quickRfl) o577 (by quickRfl) o578 (by quickRfl) o579 (by quickRfl)
    o580 (by quickRfl) o581 (by quickRfl) o582 (by quickRfl) o583 (by quickRfl)

theorem x73 : CFSG.KD.Fi24Pc.xck (nat_lit 73) = true :=
  xck_of o584 (by quickRfl) o585 (by quickRfl) o586 (by quickRfl) o587 (by quickRfl)
    o588 (by quickRfl) o589 (by quickRfl) o590 (by quickRfl) o591 (by quickRfl)

theorem x74 : CFSG.KD.Fi24Pc.xck (nat_lit 74) = true :=
  xck_of o592 (by quickRfl) o593 (by quickRfl) o594 (by quickRfl) o595 (by quickRfl)
    o596 (by quickRfl) o597 (by quickRfl) o598 (by quickRfl) o599 (by quickRfl)

theorem x75 : CFSG.KD.Fi24Pc.xck (nat_lit 75) = true :=
  xck_of o600 (by quickRfl) o601 (by quickRfl) o602 (by quickRfl) o603 (by quickRfl)
    o604 (by quickRfl) o605 (by quickRfl) o606 (by quickRfl) o607 (by quickRfl)

theorem x76 : CFSG.KD.Fi24Pc.xck (nat_lit 76) = true :=
  xck_of o608 (by quickRfl) o609 (by quickRfl) o610 (by quickRfl) o611 (by quickRfl)
    o612 (by quickRfl) o613 (by quickRfl) o614 (by quickRfl) o615 (by quickRfl)

theorem x77 : CFSG.KD.Fi24Pc.xck (nat_lit 77) = true :=
  xck_of o616 (by quickRfl) o617 (by quickRfl) o618 (by quickRfl) o619 (by quickRfl)
    o620 (by quickRfl) o621 (by quickRfl) o622 (by quickRfl) o623 (by quickRfl)

end CFSG.KD.Fi24Pc.Ck

end
