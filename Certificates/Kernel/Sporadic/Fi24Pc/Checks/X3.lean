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

theorem a624_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 624))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 624) 0) = 182783 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b624_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 624)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 624)) 0) = 182783 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a624_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 624))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 624) 305530) = 250974 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b624_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 624)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 624)) 305530) = 250974 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a624_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 624))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 624) 5604) = 169177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b624_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 624)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 624)) 5604) = 169177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a624_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 624))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 624) 221549) = 4676 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b624_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 624)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 624)) 221549) = 4676 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a624_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 624))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 624) 266275) = 233968 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b624_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 624)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 624)) 266275) = 233968 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a624_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 624))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 624) 186844) = 88041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b624_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 624)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 624)) 186844) = 88041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o624 : xone 624 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a624_0 b624_0 a624_1 b624_1 a624_2 b624_2
    a624_3 b624_3 a624_4 b624_4 a624_5 b624_5

theorem a625_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 625))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 625) 0) = 143130 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b625_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 625)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 625)) 0) = 143130 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a625_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 625))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 625) 305530) = 135566 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b625_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 625)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 625)) 305530) = 135566 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a625_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 625))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 625) 5604) = 300914 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b625_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 625)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 625)) 5604) = 300914 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a625_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 625))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 625) 221549) = 253585 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b625_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 625)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 625)) 221549) = 253585 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a625_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 625))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 625) 266275) = 261471 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b625_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 625)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 625)) 266275) = 261471 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a625_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 625))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 625) 186844) = 224916 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b625_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 625)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 625)) 186844) = 224916 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o625 : xone 625 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a625_0 b625_0 a625_1 b625_1 a625_2 b625_2
    a625_3 b625_3 a625_4 b625_4 a625_5 b625_5

theorem a626_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 626))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 626) 0) = 45419 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b626_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 626)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 626)) 0) = 45419 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a626_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 626))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 626) 305530) = 117868 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b626_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 626)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 626)) 305530) = 117868 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a626_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 626))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 626) 5604) = 156027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b626_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 626)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 626)) 5604) = 156027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a626_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 626))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 626) 221549) = 93650 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b626_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 626)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 626)) 221549) = 93650 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a626_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 626))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 626) 266275) = 254344 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b626_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 626)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 626)) 266275) = 254344 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a626_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 626))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 626) 186844) = 114543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b626_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 626)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 626)) 186844) = 114543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o626 : xone 626 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a626_0 b626_0 a626_1 b626_1 a626_2 b626_2
    a626_3 b626_3 a626_4 b626_4 a626_5 b626_5

theorem a627_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 627))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 627) 0) = 160724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b627_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 627)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 627)) 0) = 160724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a627_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 627))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 627) 305530) = 246386 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b627_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 627)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 627)) 305530) = 246386 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a627_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 627))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 627) 5604) = 196239 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b627_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 627)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 627)) 5604) = 196239 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a627_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 627))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 627) 221549) = 155440 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b627_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 627)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 627)) 221549) = 155440 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a627_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 627))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 627) 266275) = 266565 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b627_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 627)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 627)) 266275) = 266565 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a627_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 627))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 627) 186844) = 189712 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b627_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 627)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 627)) 186844) = 189712 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o627 : xone 627 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a627_0 b627_0 a627_1 b627_1 a627_2 b627_2
    a627_3 b627_3 a627_4 b627_4 a627_5 b627_5

theorem a628_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 628))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 628) 0) = 194679 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b628_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 628)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 628)) 0) = 194679 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a628_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 628))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 628) 305530) = 97839 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b628_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 628)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 628)) 305530) = 97839 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a628_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 628))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 628) 5604) = 64001 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b628_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 628)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 628)) 5604) = 64001 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a628_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 628))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 628) 221549) = 270518 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b628_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 628)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 628)) 221549) = 270518 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a628_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 628))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 628) 266275) = 148045 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b628_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 628)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 628)) 266275) = 148045 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a628_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 628))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 628) 186844) = 217180 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b628_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 628)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 628)) 186844) = 217180 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o628 : xone 628 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a628_0 b628_0 a628_1 b628_1 a628_2 b628_2
    a628_3 b628_3 a628_4 b628_4 a628_5 b628_5

theorem a629_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 629))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 629) 0) = 163995 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b629_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 629)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 629)) 0) = 163995 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a629_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 629))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 629) 305530) = 141820 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b629_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 629)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 629)) 305530) = 141820 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a629_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 629))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 629) 5604) = 42699 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b629_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 629)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 629)) 5604) = 42699 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a629_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 629))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 629) 221549) = 173060 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b629_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 629)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 629)) 221549) = 173060 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a629_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 629))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 629) 266275) = 219041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b629_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 629)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 629)) 266275) = 219041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a629_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 629))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 629) 186844) = 255241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b629_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 629)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 629)) 186844) = 255241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o629 : xone 629 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a629_0 b629_0 a629_1 b629_1 a629_2 b629_2
    a629_3 b629_3 a629_4 b629_4 a629_5 b629_5

theorem a630_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 630))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 630) 0) = 153429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b630_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 630)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 630)) 0) = 153429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a630_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 630))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 630) 305530) = 259319 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b630_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 630)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 630)) 305530) = 259319 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a630_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 630))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 630) 5604) = 16012 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b630_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 630)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 630)) 5604) = 16012 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a630_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 630))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 630) 221549) = 125564 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b630_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 630)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 630)) 221549) = 125564 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a630_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 630))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 630) 266275) = 304999 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b630_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 630)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 630)) 266275) = 304999 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a630_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 630))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 630) 186844) = 171345 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b630_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 630)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 630)) 186844) = 171345 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o630 : xone 630 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a630_0 b630_0 a630_1 b630_1 a630_2 b630_2
    a630_3 b630_3 a630_4 b630_4 a630_5 b630_5

theorem a631_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 631))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 631) 0) = 253776 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b631_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 631)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 631)) 0) = 253776 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a631_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 631))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 631) 305530) = 200953 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b631_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 631)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 631)) 305530) = 200953 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a631_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 631))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 631) 5604) = 81387 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b631_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 631)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 631)) 5604) = 81387 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a631_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 631))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 631) 221549) = 72011 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b631_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 631)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 631)) 221549) = 72011 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a631_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 631))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 631) 266275) = 265437 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b631_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 631)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 631)) 266275) = 265437 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a631_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 631))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 631) 186844) = 8506 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b631_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 631)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 631)) 186844) = 8506 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o631 : xone 631 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a631_0 b631_0 a631_1 b631_1 a631_2 b631_2
    a631_3 b631_3 a631_4 b631_4 a631_5 b631_5

theorem a632_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 632))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 632) 0) = 278113 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b632_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 632)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 632)) 0) = 278113 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a632_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 632))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 632) 305530) = 109495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b632_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 632)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 632)) 305530) = 109495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a632_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 632))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 632) 5604) = 189199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b632_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 632)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 632)) 5604) = 189199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a632_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 632))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 632) 221549) = 174839 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b632_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 632)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 632)) 221549) = 174839 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a632_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 632))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 632) 266275) = 204164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b632_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 632)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 632)) 266275) = 204164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a632_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 632))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 632) 186844) = 6507 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b632_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 632)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 632)) 186844) = 6507 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o632 : xone 632 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a632_0 b632_0 a632_1 b632_1 a632_2 b632_2
    a632_3 b632_3 a632_4 b632_4 a632_5 b632_5

theorem a633_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 633))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 633) 0) = 223491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b633_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 633)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 633)) 0) = 223491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a633_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 633))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 633) 305530) = 47000 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b633_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 633)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 633)) 305530) = 47000 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a633_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 633))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 633) 5604) = 184622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b633_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 633)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 633)) 5604) = 184622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a633_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 633))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 633) 221549) = 247837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b633_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 633)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 633)) 221549) = 247837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a633_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 633))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 633) 266275) = 170125 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b633_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 633)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 633)) 266275) = 170125 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a633_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 633))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 633) 186844) = 148810 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b633_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 633)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 633)) 186844) = 148810 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o633 : xone 633 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a633_0 b633_0 a633_1 b633_1 a633_2 b633_2
    a633_3 b633_3 a633_4 b633_4 a633_5 b633_5

theorem a634_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 634))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 634) 0) = 265618 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b634_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 634)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 634)) 0) = 265618 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a634_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 634))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 634) 305530) = 40775 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b634_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 634)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 634)) 305530) = 40775 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a634_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 634))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 634) 5604) = 142738 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b634_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 634)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 634)) 5604) = 142738 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a634_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 634))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 634) 221549) = 182433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b634_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 634)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 634)) 221549) = 182433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a634_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 634))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 634) 266275) = 45388 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b634_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 634)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 634)) 266275) = 45388 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a634_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 634))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 634) 186844) = 299343 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b634_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 634)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 634)) 186844) = 299343 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o634 : xone 634 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a634_0 b634_0 a634_1 b634_1 a634_2 b634_2
    a634_3 b634_3 a634_4 b634_4 a634_5 b634_5

theorem a635_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 635))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 635) 0) = 88402 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b635_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 635)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 635)) 0) = 88402 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a635_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 635))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 635) 305530) = 230812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b635_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 635)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 635)) 305530) = 230812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a635_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 635))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 635) 5604) = 16304 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b635_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 635)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 635)) 5604) = 16304 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a635_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 635))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 635) 221549) = 37996 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b635_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 635)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 635)) 221549) = 37996 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a635_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 635))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 635) 266275) = 148995 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b635_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 635)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 635)) 266275) = 148995 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a635_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 635))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 635) 186844) = 267563 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b635_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 635)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 635)) 186844) = 267563 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o635 : xone 635 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a635_0 b635_0 a635_1 b635_1 a635_2 b635_2
    a635_3 b635_3 a635_4 b635_4 a635_5 b635_5

theorem a636_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 636))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 636) 0) = 131510 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b636_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 636)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 636)) 0) = 131510 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a636_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 636))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 636) 305530) = 231723 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b636_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 636)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 636)) 305530) = 231723 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a636_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 636))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 636) 5604) = 233869 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b636_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 636)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 636)) 5604) = 233869 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a636_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 636))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 636) 221549) = 189438 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b636_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 636)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 636)) 221549) = 189438 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a636_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 636))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 636) 266275) = 107472 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b636_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 636)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 636)) 266275) = 107472 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a636_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 636))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 636) 186844) = 259030 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b636_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 636)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 636)) 186844) = 259030 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o636 : xone 636 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a636_0 b636_0 a636_1 b636_1 a636_2 b636_2
    a636_3 b636_3 a636_4 b636_4 a636_5 b636_5

theorem a637_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 637))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 637) 0) = 72297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b637_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 637)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 637)) 0) = 72297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a637_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 637))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 637) 305530) = 111330 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b637_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 637)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 637)) 305530) = 111330 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a637_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 637))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 637) 5604) = 202136 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b637_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 637)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 637)) 5604) = 202136 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a637_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 637))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 637) 221549) = 274724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b637_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 637)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 637)) 221549) = 274724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a637_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 637))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 637) 266275) = 295423 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b637_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 637)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 637)) 266275) = 295423 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a637_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 637))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 637) 186844) = 108254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b637_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 637)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 637)) 186844) = 108254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o637 : xone 637 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a637_0 b637_0 a637_1 b637_1 a637_2 b637_2
    a637_3 b637_3 a637_4 b637_4 a637_5 b637_5

theorem a638_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 638))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 638) 0) = 80652 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b638_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 638)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 638)) 0) = 80652 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a638_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 638))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 638) 305530) = 187072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b638_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 638)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 638)) 305530) = 187072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a638_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 638))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 638) 5604) = 98055 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b638_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 638)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 638)) 5604) = 98055 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a638_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 638))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 638) 221549) = 211048 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b638_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 638)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 638)) 221549) = 211048 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a638_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 638))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 638) 266275) = 203927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b638_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 638)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 638)) 266275) = 203927 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a638_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 638))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 638) 186844) = 162872 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b638_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 638)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 638)) 186844) = 162872 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o638 : xone 638 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a638_0 b638_0 a638_1 b638_1 a638_2 b638_2
    a638_3 b638_3 a638_4 b638_4 a638_5 b638_5

theorem a639_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 639))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 639) 0) = 17131 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b639_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 639)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 639)) 0) = 17131 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a639_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 639))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 639) 305530) = 275444 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b639_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 639)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 639)) 305530) = 275444 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a639_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 639))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 639) 5604) = 260660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b639_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 639)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 639)) 5604) = 260660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a639_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 639))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 639) 221549) = 91026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b639_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 639)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 639)) 221549) = 91026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a639_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 639))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 639) 266275) = 225594 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b639_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 639)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 639)) 266275) = 225594 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a639_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 639))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 639) 186844) = 119013 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b639_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 639)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 639)) 186844) = 119013 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o639 : xone 639 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a639_0 b639_0 a639_1 b639_1 a639_2 b639_2
    a639_3 b639_3 a639_4 b639_4 a639_5 b639_5

theorem a640_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 640))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 640) 0) = 36822 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b640_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 640)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 640)) 0) = 36822 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a640_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 640))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 640) 305530) = 41645 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b640_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 640)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 640)) 305530) = 41645 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a640_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 640))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 640) 5604) = 203140 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b640_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 640)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 640)) 5604) = 203140 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a640_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 640))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 640) 221549) = 182251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b640_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 640)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 640)) 221549) = 182251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a640_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 640))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 640) 266275) = 56359 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b640_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 640)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 640)) 266275) = 56359 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a640_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 640))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 640) 186844) = 39303 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b640_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 640)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 640)) 186844) = 39303 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o640 : xone 640 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a640_0 b640_0 a640_1 b640_1 a640_2 b640_2
    a640_3 b640_3 a640_4 b640_4 a640_5 b640_5

theorem a641_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 641))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 641) 0) = 125250 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b641_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 641)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 641)) 0) = 125250 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a641_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 641))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 641) 305530) = 80349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b641_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 641)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 641)) 305530) = 80349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a641_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 641))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 641) 5604) = 10704 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b641_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 641)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 641)) 5604) = 10704 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a641_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 641))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 641) 221549) = 240139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b641_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 641)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 641)) 221549) = 240139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a641_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 641))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 641) 266275) = 258315 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b641_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 641)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 641)) 266275) = 258315 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a641_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 641))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 641) 186844) = 36662 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b641_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 641)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 641)) 186844) = 36662 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o641 : xone 641 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a641_0 b641_0 a641_1 b641_1 a641_2 b641_2
    a641_3 b641_3 a641_4 b641_4 a641_5 b641_5

theorem a642_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 642))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 642) 0) = 43817 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b642_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 642)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 642)) 0) = 43817 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a642_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 642))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 642) 305530) = 18481 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b642_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 642)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 642)) 305530) = 18481 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a642_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 642))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 642) 5604) = 106152 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b642_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 642)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 642)) 5604) = 106152 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a642_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 642))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 642) 221549) = 83362 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b642_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 642)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 642)) 221549) = 83362 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a642_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 642))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 642) 266275) = 30955 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b642_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 642)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 642)) 266275) = 30955 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a642_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 642))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 642) 186844) = 270664 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b642_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 642)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 642)) 186844) = 270664 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o642 : xone 642 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a642_0 b642_0 a642_1 b642_1 a642_2 b642_2
    a642_3 b642_3 a642_4 b642_4 a642_5 b642_5

theorem a643_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 643))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 643) 0) = 244727 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b643_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 643)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 643)) 0) = 244727 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a643_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 643))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 643) 305530) = 69324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b643_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 643)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 643)) 305530) = 69324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a643_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 643))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 643) 5604) = 185179 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b643_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 643)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 643)) 5604) = 185179 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a643_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 643))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 643) 221549) = 233233 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b643_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 643)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 643)) 221549) = 233233 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a643_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 643))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 643) 266275) = 235907 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b643_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 643)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 643)) 266275) = 235907 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a643_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 643))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 643) 186844) = 216439 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b643_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 643)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 643)) 186844) = 216439 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o643 : xone 643 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a643_0 b643_0 a643_1 b643_1 a643_2 b643_2
    a643_3 b643_3 a643_4 b643_4 a643_5 b643_5

theorem a644_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 644))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 644) 0) = 181253 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b644_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 644)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 644)) 0) = 181253 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a644_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 644))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 644) 305530) = 303554 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b644_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 644)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 644)) 305530) = 303554 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a644_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 644))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 644) 5604) = 220746 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b644_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 644)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 644)) 5604) = 220746 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a644_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 644))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 644) 221549) = 55577 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b644_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 644)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 644)) 221549) = 55577 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a644_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 644))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 644) 266275) = 64462 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b644_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 644)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 644)) 266275) = 64462 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a644_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 644))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 644) 186844) = 296077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b644_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 644)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 644)) 186844) = 296077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o644 : xone 644 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a644_0 b644_0 a644_1 b644_1 a644_2 b644_2
    a644_3 b644_3 a644_4 b644_4 a644_5 b644_5

theorem a645_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 645))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 645) 0) = 203093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b645_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 645)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 645)) 0) = 203093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a645_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 645))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 645) 305530) = 88835 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b645_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 645)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 645)) 305530) = 88835 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a645_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 645))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 645) 5604) = 131164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b645_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 645)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 645)) 5604) = 131164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a645_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 645))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 645) 221549) = 124311 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b645_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 645)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 645)) 221549) = 124311 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a645_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 645))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 645) 266275) = 257356 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b645_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 645)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 645)) 266275) = 257356 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a645_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 645))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 645) 186844) = 2051 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b645_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 645)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 645)) 186844) = 2051 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o645 : xone 645 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a645_0 b645_0 a645_1 b645_1 a645_2 b645_2
    a645_3 b645_3 a645_4 b645_4 a645_5 b645_5

theorem a646_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 646))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 646) 0) = 207988 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b646_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 646)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 646)) 0) = 207988 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a646_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 646))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 646) 305530) = 217406 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b646_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 646)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 646)) 305530) = 217406 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a646_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 646))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 646) 5604) = 257738 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b646_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 646)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 646)) 5604) = 257738 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a646_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 646))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 646) 221549) = 38149 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b646_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 646)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 646)) 221549) = 38149 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a646_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 646))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 646) 266275) = 23233 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b646_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 646)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 646)) 266275) = 23233 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a646_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 646))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 646) 186844) = 91351 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b646_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 646)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 646)) 186844) = 91351 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o646 : xone 646 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a646_0 b646_0 a646_1 b646_1 a646_2 b646_2
    a646_3 b646_3 a646_4 b646_4 a646_5 b646_5

theorem a647_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 647))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 647) 0) = 271018 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b647_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 647)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 647)) 0) = 271018 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a647_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 647))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 647) 305530) = 258365 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b647_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 647)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 647)) 305530) = 258365 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a647_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 647))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 647) 5604) = 68463 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b647_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 647)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 647)) 5604) = 68463 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a647_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 647))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 647) 221549) = 92855 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b647_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 647)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 647)) 221549) = 92855 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a647_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 647))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 647) 266275) = 5129 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b647_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 647)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 647)) 266275) = 5129 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a647_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 647))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 647) 186844) = 233041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b647_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 647)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 647)) 186844) = 233041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o647 : xone 647 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a647_0 b647_0 a647_1 b647_1 a647_2 b647_2
    a647_3 b647_3 a647_4 b647_4 a647_5 b647_5

theorem a648_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 648))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 648) 0) = 296786 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b648_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 648)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 648)) 0) = 296786 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a648_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 648))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 648) 305530) = 151941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b648_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 648)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 648)) 305530) = 151941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a648_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 648))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 648) 5604) = 72574 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b648_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 648)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 648)) 5604) = 72574 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a648_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 648))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 648) 221549) = 205474 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b648_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 648)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 648)) 221549) = 205474 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a648_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 648))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 648) 266275) = 28424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b648_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 648)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 648)) 266275) = 28424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a648_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 648))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 648) 186844) = 195405 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b648_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 648)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 648)) 186844) = 195405 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o648 : xone 648 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a648_0 b648_0 a648_1 b648_1 a648_2 b648_2
    a648_3 b648_3 a648_4 b648_4 a648_5 b648_5

theorem a649_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 649))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 649) 0) = 73543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b649_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 649)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 649)) 0) = 73543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a649_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 649))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 649) 305530) = 290085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b649_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 649)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 649)) 305530) = 290085 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a649_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 649))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 649) 5604) = 230868 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b649_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 649)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 649)) 5604) = 230868 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a649_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 649))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 649) 221549) = 301222 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b649_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 649)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 649)) 221549) = 301222 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a649_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 649))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 649) 266275) = 203792 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b649_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 649)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 649)) 266275) = 203792 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a649_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 649))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 649) 186844) = 150868 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b649_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 649)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 649)) 186844) = 150868 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o649 : xone 649 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a649_0 b649_0 a649_1 b649_1 a649_2 b649_2
    a649_3 b649_3 a649_4 b649_4 a649_5 b649_5

theorem a650_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 650))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 650) 0) = 26458 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b650_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 650)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 650)) 0) = 26458 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a650_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 650))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 650) 305530) = 38131 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b650_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 650)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 650)) 305530) = 38131 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a650_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 650))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 650) 5604) = 164921 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b650_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 650)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 650)) 5604) = 164921 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a650_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 650))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 650) 221549) = 80806 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b650_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 650)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 650)) 221549) = 80806 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a650_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 650))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 650) 266275) = 167991 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b650_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 650)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 650)) 266275) = 167991 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a650_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 650))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 650) 186844) = 240312 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b650_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 650)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 650)) 186844) = 240312 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o650 : xone 650 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a650_0 b650_0 a650_1 b650_1 a650_2 b650_2
    a650_3 b650_3 a650_4 b650_4 a650_5 b650_5

theorem a651_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 651))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 651) 0) = 162308 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b651_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 651)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 651)) 0) = 162308 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a651_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 651))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 651) 305530) = 159162 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b651_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 651)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 651)) 305530) = 159162 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a651_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 651))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 651) 5604) = 130685 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b651_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 651)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 651)) 5604) = 130685 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a651_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 651))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 651) 221549) = 51770 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b651_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 651)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 651)) 221549) = 51770 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a651_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 651))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 651) 266275) = 213305 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b651_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 651)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 651)) 266275) = 213305 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a651_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 651))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 651) 186844) = 256687 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b651_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 651)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 651)) 186844) = 256687 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o651 : xone 651 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a651_0 b651_0 a651_1 b651_1 a651_2 b651_2
    a651_3 b651_3 a651_4 b651_4 a651_5 b651_5

theorem a652_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 652))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 652) 0) = 73374 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b652_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 652)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 652)) 0) = 73374 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a652_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 652))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 652) 305530) = 220287 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b652_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 652)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 652)) 305530) = 220287 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a652_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 652))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 652) 5604) = 42592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b652_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 652)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 652)) 5604) = 42592 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a652_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 652))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 652) 221549) = 167319 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b652_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 652)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 652)) 221549) = 167319 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a652_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 652))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 652) 266275) = 193760 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b652_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 652)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 652)) 266275) = 193760 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a652_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 652))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 652) 186844) = 33882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b652_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 652)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 652)) 186844) = 33882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o652 : xone 652 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a652_0 b652_0 a652_1 b652_1 a652_2 b652_2
    a652_3 b652_3 a652_4 b652_4 a652_5 b652_5

theorem a653_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 653))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 653) 0) = 98736 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b653_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 653)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 653)) 0) = 98736 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a653_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 653))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 653) 305530) = 40736 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b653_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 653)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 653)) 305530) = 40736 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a653_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 653))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 653) 5604) = 71728 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b653_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 653)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 653)) 5604) = 71728 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a653_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 653))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 653) 221549) = 263524 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b653_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 653)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 653)) 221549) = 263524 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a653_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 653))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 653) 266275) = 276681 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b653_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 653)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 653)) 266275) = 276681 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a653_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 653))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 653) 186844) = 299611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b653_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 653)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 653)) 186844) = 299611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o653 : xone 653 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a653_0 b653_0 a653_1 b653_1 a653_2 b653_2
    a653_3 b653_3 a653_4 b653_4 a653_5 b653_5

theorem a654_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 654))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 654) 0) = 257933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b654_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 654)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 654)) 0) = 257933 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a654_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 654))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 654) 305530) = 295024 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b654_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 654)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 654)) 305530) = 295024 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a654_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 654))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 654) 5604) = 88111 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b654_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 654)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 654)) 5604) = 88111 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a654_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 654))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 654) 221549) = 158356 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b654_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 654)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 654)) 221549) = 158356 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a654_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 654))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 654) 266275) = 97206 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b654_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 654)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 654)) 266275) = 97206 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a654_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 654))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 654) 186844) = 204840 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b654_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 654)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 654)) 186844) = 204840 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o654 : xone 654 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a654_0 b654_0 a654_1 b654_1 a654_2 b654_2
    a654_3 b654_3 a654_4 b654_4 a654_5 b654_5

theorem a655_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 655))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 655) 0) = 287880 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b655_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 655)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 655)) 0) = 287880 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a655_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 655))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 655) 305530) = 10787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b655_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 655)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 655)) 305530) = 10787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a655_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 655))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 655) 5604) = 28732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b655_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 655)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 655)) 5604) = 28732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a655_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 655))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 655) 221549) = 24411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b655_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 655)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 655)) 221549) = 24411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a655_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 655))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 655) 266275) = 204742 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b655_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 655)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 655)) 266275) = 204742 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a655_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 655))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 655) 186844) = 74318 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b655_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 655)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 655)) 186844) = 74318 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o655 : xone 655 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a655_0 b655_0 a655_1 b655_1 a655_2 b655_2
    a655_3 b655_3 a655_4 b655_4 a655_5 b655_5

theorem a656_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 656))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 656) 0) = 230371 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b656_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 656)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 656)) 0) = 230371 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a656_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 656))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 656) 305530) = 136302 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b656_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 656)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 656)) 305530) = 136302 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a656_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 656))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 656) 5604) = 146180 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b656_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 656)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 656)) 5604) = 146180 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a656_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 656))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 656) 221549) = 248849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b656_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 656)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 656)) 221549) = 248849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a656_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 656))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 656) 266275) = 94719 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b656_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 656)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 656)) 266275) = 94719 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a656_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 656))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 656) 186844) = 140382 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b656_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 656)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 656)) 186844) = 140382 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o656 : xone 656 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a656_0 b656_0 a656_1 b656_1 a656_2 b656_2
    a656_3 b656_3 a656_4 b656_4 a656_5 b656_5

theorem a657_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 657))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 657) 0) = 182915 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b657_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 657)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 657)) 0) = 182915 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a657_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 657))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 657) 305530) = 115335 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b657_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 657)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 657)) 305530) = 115335 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a657_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 657))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 657) 5604) = 102585 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b657_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 657)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 657)) 5604) = 102585 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a657_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 657))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 657) 221549) = 141253 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b657_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 657)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 657)) 221549) = 141253 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a657_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 657))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 657) 266275) = 208756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b657_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 657)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 657)) 266275) = 208756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a657_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 657))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 657) 186844) = 284996 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b657_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 657)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 657)) 186844) = 284996 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o657 : xone 657 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a657_0 b657_0 a657_1 b657_1 a657_2 b657_2
    a657_3 b657_3 a657_4 b657_4 a657_5 b657_5

theorem a658_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 658))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 658) 0) = 88206 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b658_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 658)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 658)) 0) = 88206 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a658_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 658))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 658) 305530) = 122851 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b658_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 658)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 658)) 305530) = 122851 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a658_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 658))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 658) 5604) = 55866 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b658_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 658)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 658)) 5604) = 55866 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a658_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 658))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 658) 221549) = 296153 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b658_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 658)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 658)) 221549) = 296153 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a658_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 658))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 658) 266275) = 250197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b658_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 658)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 658)) 266275) = 250197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a658_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 658))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 658) 186844) = 30967 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b658_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 658)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 658)) 186844) = 30967 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o658 : xone 658 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a658_0 b658_0 a658_1 b658_1 a658_2 b658_2
    a658_3 b658_3 a658_4 b658_4 a658_5 b658_5

theorem a659_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 659))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 659) 0) = 262156 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b659_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 659)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 659)) 0) = 262156 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a659_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 659))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 659) 305530) = 274114 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b659_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 659)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 659)) 305530) = 274114 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a659_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 659))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 659) 5604) = 24115 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b659_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 659)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 659)) 5604) = 24115 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a659_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 659))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 659) 221549) = 98036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b659_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 659)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 659)) 221549) = 98036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a659_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 659))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 659) 266275) = 39658 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b659_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 659)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 659)) 266275) = 39658 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a659_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 659))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 659) 186844) = 143921 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b659_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 659)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 659)) 186844) = 143921 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o659 : xone 659 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a659_0 b659_0 a659_1 b659_1 a659_2 b659_2
    a659_3 b659_3 a659_4 b659_4 a659_5 b659_5

theorem a660_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 660))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 660) 0) = 97128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b660_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 660)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 660)) 0) = 97128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a660_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 660))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 660) 305530) = 143719 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b660_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 660)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 660)) 305530) = 143719 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a660_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 660))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 660) 5604) = 98729 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b660_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 660)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 660)) 5604) = 98729 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a660_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 660))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 660) 221549) = 292324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b660_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 660)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 660)) 221549) = 292324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a660_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 660))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 660) 266275) = 96288 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b660_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 660)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 660)) 266275) = 96288 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a660_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 660))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 660) 186844) = 239586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b660_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 660)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 660)) 186844) = 239586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o660 : xone 660 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a660_0 b660_0 a660_1 b660_1 a660_2 b660_2
    a660_3 b660_3 a660_4 b660_4 a660_5 b660_5

theorem a661_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 661))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 661) 0) = 146452 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b661_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 661)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 661)) 0) = 146452 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a661_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 661))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 661) 305530) = 231477 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b661_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 661)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 661)) 305530) = 231477 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a661_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 661))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 661) 5604) = 233956 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b661_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 661)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 661)) 5604) = 233956 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a661_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 661))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 661) 221549) = 29539 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b661_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 661)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 661)) 221549) = 29539 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a661_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 661))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 661) 266275) = 156304 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b661_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 661)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 661)) 266275) = 156304 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a661_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 661))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 661) 186844) = 152461 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b661_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 661)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 661)) 186844) = 152461 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o661 : xone 661 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a661_0 b661_0 a661_1 b661_1 a661_2 b661_2
    a661_3 b661_3 a661_4 b661_4 a661_5 b661_5

theorem a662_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 662))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 662) 0) = 145437 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b662_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 662)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 662)) 0) = 145437 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a662_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 662))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 662) 305530) = 275492 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b662_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 662)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 662)) 305530) = 275492 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a662_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 662))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 662) 5604) = 177069 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b662_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 662)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 662)) 5604) = 177069 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a662_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 662))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 662) 221549) = 124986 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b662_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 662)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 662)) 221549) = 124986 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a662_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 662))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 662) 266275) = 304482 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b662_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 662)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 662)) 266275) = 304482 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a662_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 662))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 662) 186844) = 248433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b662_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 662)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 662)) 186844) = 248433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o662 : xone 662 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a662_0 b662_0 a662_1 b662_1 a662_2 b662_2
    a662_3 b662_3 a662_4 b662_4 a662_5 b662_5

theorem a663_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 663))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 663) 0) = 2743 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b663_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 663)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 663)) 0) = 2743 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a663_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 663))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 663) 305530) = 111222 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b663_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 663)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 663)) 305530) = 111222 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a663_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 663))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 663) 5604) = 292783 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b663_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 663)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 663)) 5604) = 292783 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a663_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 663))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 663) 221549) = 70887 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b663_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 663)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 663)) 221549) = 70887 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a663_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 663))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 663) 266275) = 220504 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b663_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 663)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 663)) 266275) = 220504 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a663_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 663))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 663) 186844) = 105643 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b663_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 663)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 663)) 186844) = 105643 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o663 : xone 663 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a663_0 b663_0 a663_1 b663_1 a663_2 b663_2
    a663_3 b663_3 a663_4 b663_4 a663_5 b663_5

theorem a664_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 664))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 664) 0) = 198487 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b664_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 664)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 664)) 0) = 198487 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a664_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 664))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 664) 305530) = 257876 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b664_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 664)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 664)) 305530) = 257876 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a664_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 664))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 664) 5604) = 139245 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b664_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 664)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 664)) 5604) = 139245 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a664_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 664))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 664) 221549) = 302905 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b664_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 664)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 664)) 221549) = 302905 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a664_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 664))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 664) 266275) = 92397 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b664_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 664)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 664)) 266275) = 92397 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a664_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 664))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 664) 186844) = 7147 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b664_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 664)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 664)) 186844) = 7147 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o664 : xone 664 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a664_0 b664_0 a664_1 b664_1 a664_2 b664_2
    a664_3 b664_3 a664_4 b664_4 a664_5 b664_5

theorem a665_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 665))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 665) 0) = 154025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b665_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 665)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 665)) 0) = 154025 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a665_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 665))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 665) 305530) = 178711 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b665_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 665)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 665)) 305530) = 178711 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a665_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 665))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 665) 5604) = 204749 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b665_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 665)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 665)) 5604) = 204749 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a665_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 665))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 665) 221549) = 75083 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b665_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 665)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 665)) 221549) = 75083 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a665_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 665))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 665) 266275) = 15640 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b665_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 665)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 665)) 266275) = 15640 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a665_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 665))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 665) 186844) = 2359 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b665_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 665)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 665)) 186844) = 2359 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o665 : xone 665 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a665_0 b665_0 a665_1 b665_1 a665_2 b665_2
    a665_3 b665_3 a665_4 b665_4 a665_5 b665_5

theorem a666_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 666))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 666) 0) = 95768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b666_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 666)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 666)) 0) = 95768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a666_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 666))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 666) 305530) = 170043 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b666_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 666)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 666)) 305530) = 170043 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a666_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 666))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 666) 5604) = 590 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b666_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 666)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 666)) 5604) = 590 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a666_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 666))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 666) 221549) = 278850 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b666_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 666)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 666)) 221549) = 278850 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a666_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 666))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 666) 266275) = 93842 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b666_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 666)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 666)) 266275) = 93842 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a666_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 666))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 666) 186844) = 105593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b666_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 666)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 666)) 186844) = 105593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o666 : xone 666 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a666_0 b666_0 a666_1 b666_1 a666_2 b666_2
    a666_3 b666_3 a666_4 b666_4 a666_5 b666_5

theorem a667_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 667))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 667) 0) = 64925 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b667_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 667)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 667)) 0) = 64925 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a667_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 667))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 667) 305530) = 237716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b667_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 667)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 667)) 305530) = 237716 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a667_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 667))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 667) 5604) = 305672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b667_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 667)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 667)) 5604) = 305672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a667_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 667))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 667) 221549) = 268791 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b667_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 667)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 667)) 221549) = 268791 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a667_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 667))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 667) 266275) = 216689 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b667_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 667)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 667)) 266275) = 216689 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a667_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 667))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 667) 186844) = 143783 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b667_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 667)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 667)) 186844) = 143783 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o667 : xone 667 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a667_0 b667_0 a667_1 b667_1 a667_2 b667_2
    a667_3 b667_3 a667_4 b667_4 a667_5 b667_5

theorem a668_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 668))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 668) 0) = 247226 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b668_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 668)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 668)) 0) = 247226 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a668_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 668))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 668) 305530) = 180704 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b668_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 668)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 668)) 305530) = 180704 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a668_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 668))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 668) 5604) = 106486 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b668_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 668)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 668)) 5604) = 106486 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a668_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 668))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 668) 221549) = 215858 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b668_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 668)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 668)) 221549) = 215858 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a668_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 668))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 668) 266275) = 140622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b668_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 668)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 668)) 266275) = 140622 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a668_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 668))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 668) 186844) = 231160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b668_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 668)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 668)) 186844) = 231160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o668 : xone 668 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a668_0 b668_0 a668_1 b668_1 a668_2 b668_2
    a668_3 b668_3 a668_4 b668_4 a668_5 b668_5

theorem a669_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 669))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 669) 0) = 42306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b669_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 669)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 669)) 0) = 42306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a669_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 669))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 669) 305530) = 191028 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b669_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 669)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 669)) 305530) = 191028 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a669_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 669))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 669) 5604) = 98804 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b669_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 669)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 669)) 5604) = 98804 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a669_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 669))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 669) 221549) = 223954 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b669_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 669)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 669)) 221549) = 223954 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a669_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 669))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 669) 266275) = 122142 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b669_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 669)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 669)) 266275) = 122142 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a669_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 669))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 669) 186844) = 276702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b669_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 669)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 669)) 186844) = 276702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o669 : xone 669 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a669_0 b669_0 a669_1 b669_1 a669_2 b669_2
    a669_3 b669_3 a669_4 b669_4 a669_5 b669_5

theorem a670_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 670))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 670) 0) = 40094 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b670_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 670)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 670)) 0) = 40094 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a670_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 670))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 670) 305530) = 42664 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b670_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 670)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 670)) 305530) = 42664 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a670_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 670))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 670) 5604) = 266238 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b670_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 670)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 670)) 5604) = 266238 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a670_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 670))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 670) 221549) = 146246 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b670_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 670)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 670)) 221549) = 146246 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a670_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 670))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 670) 266275) = 172718 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b670_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 670)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 670)) 266275) = 172718 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a670_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 670))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 670) 186844) = 299942 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b670_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 670)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 670)) 186844) = 299942 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o670 : xone 670 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a670_0 b670_0 a670_1 b670_1 a670_2 b670_2
    a670_3 b670_3 a670_4 b670_4 a670_5 b670_5

theorem a671_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 671))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 671) 0) = 236930 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b671_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 671)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 671)) 0) = 236930 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a671_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 671))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 671) 305530) = 159375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b671_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 671)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 671)) 305530) = 159375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a671_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 671))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 671) 5604) = 266182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b671_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 671)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 671)) 5604) = 266182 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a671_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 671))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 671) 221549) = 73169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b671_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 671)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 671)) 221549) = 73169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a671_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 671))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 671) 266275) = 225169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b671_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 671)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 671)) 266275) = 225169 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a671_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 671))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 671) 186844) = 153941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b671_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 671)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 671)) 186844) = 153941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o671 : xone 671 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a671_0 b671_0 a671_1 b671_1 a671_2 b671_2
    a671_3 b671_3 a671_4 b671_4 a671_5 b671_5

theorem a672_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 672))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 672) 0) = 89619 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b672_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 672)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 672)) 0) = 89619 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a672_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 672))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 672) 305530) = 64154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b672_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 672)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 672)) 305530) = 64154 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a672_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 672))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 672) 5604) = 97648 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b672_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 672)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 672)) 5604) = 97648 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a672_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 672))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 672) 221549) = 239969 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b672_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 672)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 672)) 221549) = 239969 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a672_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 672))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 672) 266275) = 73613 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b672_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 672)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 672)) 266275) = 73613 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a672_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 672))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 672) 186844) = 140300 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b672_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 672)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 672)) 186844) = 140300 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o672 : xone 672 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a672_0 b672_0 a672_1 b672_1 a672_2 b672_2
    a672_3 b672_3 a672_4 b672_4 a672_5 b672_5

theorem a673_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 673))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 673) 0) = 258087 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b673_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 673)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 673)) 0) = 258087 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a673_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 673))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 673) 305530) = 70424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b673_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 673)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 673)) 305530) = 70424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a673_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 673))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 673) 5604) = 140597 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b673_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 673)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 673)) 5604) = 140597 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a673_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 673))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 673) 221549) = 202872 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b673_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 673)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 673)) 221549) = 202872 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a673_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 673))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 673) 266275) = 170609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b673_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 673)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 673)) 266275) = 170609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a673_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 673))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 673) 186844) = 124944 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b673_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 673)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 673)) 186844) = 124944 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o673 : xone 673 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a673_0 b673_0 a673_1 b673_1 a673_2 b673_2
    a673_3 b673_3 a673_4 b673_4 a673_5 b673_5

theorem a674_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 674))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 674) 0) = 143104 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b674_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 674)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 674)) 0) = 143104 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a674_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 674))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 674) 305530) = 247902 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b674_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 674)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 674)) 305530) = 247902 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a674_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 674))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 674) 5604) = 89102 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b674_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 674)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 674)) 5604) = 89102 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a674_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 674))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 674) 221549) = 92466 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b674_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 674)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 674)) 221549) = 92466 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a674_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 674))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 674) 266275) = 162977 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b674_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 674)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 674)) 266275) = 162977 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a674_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 674))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 674) 186844) = 130176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b674_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 674)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 674)) 186844) = 130176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o674 : xone 674 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a674_0 b674_0 a674_1 b674_1 a674_2 b674_2
    a674_3 b674_3 a674_4 b674_4 a674_5 b674_5

theorem a675_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 675))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 675) 0) = 215862 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b675_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 675)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 675)) 0) = 215862 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a675_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 675))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 675) 305530) = 212677 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b675_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 675)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 675)) 305530) = 212677 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a675_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 675))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 675) 5604) = 60811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b675_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 675)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 675)) 5604) = 60811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a675_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 675))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 675) 221549) = 284561 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b675_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 675)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 675)) 221549) = 284561 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a675_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 675))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 675) 266275) = 18810 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b675_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 675)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 675)) 266275) = 18810 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a675_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 675))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 675) 186844) = 57583 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b675_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 675)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 675)) 186844) = 57583 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o675 : xone 675 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a675_0 b675_0 a675_1 b675_1 a675_2 b675_2
    a675_3 b675_3 a675_4 b675_4 a675_5 b675_5

theorem a676_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 676))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 676) 0) = 199036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b676_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 676)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 676)) 0) = 199036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a676_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 676))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 676) 305530) = 134743 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b676_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 676)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 676)) 305530) = 134743 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a676_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 676))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 676) 5604) = 26733 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b676_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 676)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 676)) 5604) = 26733 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a676_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 676))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 676) 221549) = 121539 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b676_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 676)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 676)) 221549) = 121539 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a676_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 676))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 676) 266275) = 83308 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b676_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 676)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 676)) 266275) = 83308 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a676_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 676))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 676) 186844) = 135893 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b676_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 676)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 676)) 186844) = 135893 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o676 : xone 676 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a676_0 b676_0 a676_1 b676_1 a676_2 b676_2
    a676_3 b676_3 a676_4 b676_4 a676_5 b676_5

theorem a677_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 677))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 677) 0) = 51583 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b677_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 677)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 677)) 0) = 51583 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a677_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 677))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 677) 305530) = 254483 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b677_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 677)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 677)) 305530) = 254483 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a677_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 677))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 677) 5604) = 215590 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b677_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 677)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 677)) 5604) = 215590 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a677_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 677))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 677) 221549) = 87346 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b677_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 677)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 677)) 221549) = 87346 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a677_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 677))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 677) 266275) = 79100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b677_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 677)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 677)) 266275) = 79100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a677_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 677))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 677) 186844) = 111177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b677_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 677)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 677)) 186844) = 111177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o677 : xone 677 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a677_0 b677_0 a677_1 b677_1 a677_2 b677_2
    a677_3 b677_3 a677_4 b677_4 a677_5 b677_5

theorem a678_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 678))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 678) 0) = 84100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b678_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 678)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 678)) 0) = 84100 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a678_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 678))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 678) 305530) = 293078 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b678_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 678)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 678)) 305530) = 293078 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a678_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 678))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 678) 5604) = 236490 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b678_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 678)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 678)) 5604) = 236490 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a678_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 678))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 678) 221549) = 137712 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b678_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 678)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 678)) 221549) = 137712 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a678_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 678))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 678) 266275) = 82414 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b678_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 678)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 678)) 266275) = 82414 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a678_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 678))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 678) 186844) = 123815 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b678_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 678)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 678)) 186844) = 123815 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o678 : xone 678 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a678_0 b678_0 a678_1 b678_1 a678_2 b678_2
    a678_3 b678_3 a678_4 b678_4 a678_5 b678_5

theorem a679_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 679))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 679) 0) = 180148 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b679_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 679)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 679)) 0) = 180148 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a679_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 679))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 679) 305530) = 104298 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b679_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 679)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 679)) 305530) = 104298 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a679_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 679))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 679) 5604) = 86077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b679_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 679)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 679)) 5604) = 86077 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a679_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 679))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 679) 221549) = 155279 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b679_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 679)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 679)) 221549) = 155279 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a679_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 679))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 679) 266275) = 14394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b679_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 679)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 679)) 266275) = 14394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a679_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 679))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 679) 186844) = 250309 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b679_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 679)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 679)) 186844) = 250309 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o679 : xone 679 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a679_0 b679_0 a679_1 b679_1 a679_2 b679_2
    a679_3 b679_3 a679_4 b679_4 a679_5 b679_5

theorem a680_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 680))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 680) 0) = 70297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b680_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 680)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 680)) 0) = 70297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a680_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 680))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 680) 305530) = 171766 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b680_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 680)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 680)) 305530) = 171766 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a680_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 680))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 680) 5604) = 169815 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b680_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 680)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 680)) 5604) = 169815 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a680_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 680))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 680) 221549) = 9789 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b680_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 680)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 680)) 221549) = 9789 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a680_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 680))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 680) 266275) = 170762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b680_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 680)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 680)) 266275) = 170762 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a680_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 680))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 680) 186844) = 200212 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b680_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 680)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 680)) 186844) = 200212 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o680 : xone 680 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a680_0 b680_0 a680_1 b680_1 a680_2 b680_2
    a680_3 b680_3 a680_4 b680_4 a680_5 b680_5

theorem a681_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 681))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 681) 0) = 205782 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b681_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 681)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 681)) 0) = 205782 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a681_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 681))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 681) 305530) = 120970 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b681_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 681)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 681)) 305530) = 120970 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a681_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 681))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 681) 5604) = 126474 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b681_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 681)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 681)) 5604) = 126474 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a681_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 681))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 681) 221549) = 269105 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b681_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 681)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 681)) 221549) = 269105 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a681_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 681))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 681) 266275) = 155344 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b681_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 681)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 681)) 266275) = 155344 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a681_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 681))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 681) 186844) = 168879 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b681_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 681)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 681)) 186844) = 168879 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o681 : xone 681 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a681_0 b681_0 a681_1 b681_1 a681_2 b681_2
    a681_3 b681_3 a681_4 b681_4 a681_5 b681_5

theorem a682_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 682))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 682) 0) = 291045 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b682_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 682)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 682)) 0) = 291045 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a682_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 682))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 682) 305530) = 66522 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b682_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 682)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 682)) 305530) = 66522 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a682_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 682))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 682) 5604) = 73536 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b682_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 682)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 682)) 5604) = 73536 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a682_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 682))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 682) 221549) = 295222 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b682_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 682)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 682)) 221549) = 295222 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a682_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 682))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 682) 266275) = 139080 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b682_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 682)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 682)) 266275) = 139080 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a682_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 682))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 682) 186844) = 252187 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b682_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 682)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 682)) 186844) = 252187 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o682 : xone 682 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a682_0 b682_0 a682_1 b682_1 a682_2 b682_2
    a682_3 b682_3 a682_4 b682_4 a682_5 b682_5

theorem a683_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 683))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 683) 0) = 151111 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b683_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 683)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 683)) 0) = 151111 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a683_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 683))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 683) 305530) = 256698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b683_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 683)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 683)) 305530) = 256698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a683_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 683))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 683) 5604) = 16756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b683_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 683)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 683)) 5604) = 16756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a683_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 683))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 683) 221549) = 120317 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b683_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 683)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 683)) 221549) = 120317 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a683_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 683))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 683) 266275) = 193419 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b683_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 683)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 683)) 266275) = 193419 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a683_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 683))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 683) 186844) = 215244 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b683_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 683)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 683)) 186844) = 215244 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o683 : xone 683 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a683_0 b683_0 a683_1 b683_1 a683_2 b683_2
    a683_3 b683_3 a683_4 b683_4 a683_5 b683_5

theorem a684_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 684))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 684) 0) = 16309 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b684_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 684)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 684)) 0) = 16309 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a684_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 684))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 684) 305530) = 102796 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b684_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 684)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 684)) 305530) = 102796 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a684_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 684))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 684) 5604) = 259568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b684_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 684)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 684)) 5604) = 259568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a684_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 684))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 684) 221549) = 281650 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b684_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 684)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 684)) 221549) = 281650 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a684_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 684))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 684) 266275) = 123134 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b684_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 684)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 684)) 266275) = 123134 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a684_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 684))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 684) 186844) = 70087 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b684_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 684)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 684)) 186844) = 70087 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o684 : xone 684 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a684_0 b684_0 a684_1 b684_1 a684_2 b684_2
    a684_3 b684_3 a684_4 b684_4 a684_5 b684_5

theorem a685_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 685))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 685) 0) = 130832 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b685_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 685)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 685)) 0) = 130832 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a685_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 685))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 685) 305530) = 26698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b685_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 685)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 685)) 305530) = 26698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a685_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 685))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 685) 5604) = 96110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b685_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 685)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 685)) 5604) = 96110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a685_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 685))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 685) 221549) = 140610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b685_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 685)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 685)) 221549) = 140610 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a685_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 685))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 685) 266275) = 230464 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b685_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 685)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 685)) 266275) = 230464 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a685_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 685))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 685) 186844) = 171982 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b685_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 685)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 685)) 186844) = 171982 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o685 : xone 685 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a685_0 b685_0 a685_1 b685_1 a685_2 b685_2
    a685_3 b685_3 a685_4 b685_4 a685_5 b685_5

theorem a686_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 686))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 686) 0) = 179698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b686_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 686)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 686)) 0) = 179698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a686_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 686))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 686) 305530) = 57910 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b686_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 686)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 686)) 305530) = 57910 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a686_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 686))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 686) 5604) = 56891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b686_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 686)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 686)) 5604) = 56891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a686_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 686))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 686) 221549) = 155034 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b686_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 686)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 686)) 221549) = 155034 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a686_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 686))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 686) 266275) = 76550 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b686_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 686)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 686)) 266275) = 76550 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a686_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 686))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 686) 186844) = 248054 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b686_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 686)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 686)) 186844) = 248054 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o686 : xone 686 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a686_0 b686_0 a686_1 b686_1 a686_2 b686_2
    a686_3 b686_3 a686_4 b686_4 a686_5 b686_5

theorem a687_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 687))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 687) 0) = 273300 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b687_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 687)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 687)) 0) = 273300 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a687_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 687))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 687) 305530) = 254768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b687_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 687)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 687)) 305530) = 254768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a687_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 687))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 687) 5604) = 247385 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b687_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 687)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 687)) 5604) = 247385 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a687_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 687))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 687) 221549) = 212627 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b687_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 687)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 687)) 221549) = 212627 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a687_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 687))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 687) 266275) = 177636 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b687_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 687)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 687)) 266275) = 177636 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a687_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 687))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 687) 186844) = 95593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b687_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 687)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 687)) 186844) = 95593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o687 : xone 687 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a687_0 b687_0 a687_1 b687_1 a687_2 b687_2
    a687_3 b687_3 a687_4 b687_4 a687_5 b687_5

theorem a688_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 688))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 688) 0) = 3916 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b688_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 688)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 688)) 0) = 3916 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a688_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 688))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 688) 305530) = 170749 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b688_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 688)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 688)) 305530) = 170749 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a688_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 688))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 688) 5604) = 260741 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b688_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 688)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 688)) 5604) = 260741 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a688_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 688))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 688) 221549) = 203713 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b688_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 688)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 688)) 221549) = 203713 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a688_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 688))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 688) 266275) = 160409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b688_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 688)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 688)) 266275) = 160409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a688_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 688))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 688) 186844) = 206219 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b688_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 688)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 688)) 186844) = 206219 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o688 : xone 688 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a688_0 b688_0 a688_1 b688_1 a688_2 b688_2
    a688_3 b688_3 a688_4 b688_4 a688_5 b688_5

theorem a689_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 689))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 689) 0) = 150843 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b689_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 689)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 689)) 0) = 150843 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a689_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 689))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 689) 305530) = 29827 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b689_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 689)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 689)) 305530) = 29827 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a689_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 689))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 689) 5604) = 124555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b689_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 689)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 689)) 5604) = 124555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a689_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 689))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 689) 221549) = 82451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b689_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 689)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 689)) 221549) = 82451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a689_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 689))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 689) 266275) = 305672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b689_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 689)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 689)) 266275) = 305672 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a689_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 689))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 689) 186844) = 151132 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b689_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 689)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 689)) 186844) = 151132 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o689 : xone 689 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a689_0 b689_0 a689_1 b689_1 a689_2 b689_2
    a689_3 b689_3 a689_4 b689_4 a689_5 b689_5

theorem a690_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 690))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 690) 0) = 128395 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b690_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 690)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 690)) 0) = 128395 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a690_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 690))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 690) 305530) = 259951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b690_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 690)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 690)) 305530) = 259951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a690_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 690))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 690) 5604) = 105484 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b690_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 690)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 690)) 5604) = 105484 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a690_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 690))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 690) 221549) = 146337 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b690_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 690)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 690)) 221549) = 146337 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a690_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 690))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 690) 266275) = 76735 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b690_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 690)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 690)) 266275) = 76735 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a690_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 690))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 690) 186844) = 28745 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b690_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 690)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 690)) 186844) = 28745 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o690 : xone 690 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a690_0 b690_0 a690_1 b690_1 a690_2 b690_2
    a690_3 b690_3 a690_4 b690_4 a690_5 b690_5

theorem a691_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 691))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 691) 0) = 241607 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b691_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 691)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 691)) 0) = 241607 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a691_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 691))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 691) 305530) = 11755 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b691_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 691)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 691)) 305530) = 11755 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a691_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 691))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 691) 5604) = 248429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b691_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 691)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 691)) 5604) = 248429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a691_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 691))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 691) 221549) = 148152 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b691_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 691)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 691)) 221549) = 148152 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a691_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 691))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 691) 266275) = 201362 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b691_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 691)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 691)) 266275) = 201362 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a691_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 691))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 691) 186844) = 268019 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b691_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 691)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 691)) 186844) = 268019 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o691 : xone 691 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a691_0 b691_0 a691_1 b691_1 a691_2 b691_2
    a691_3 b691_3 a691_4 b691_4 a691_5 b691_5

theorem a692_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 692))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 692) 0) = 117371 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b692_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 692)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 692)) 0) = 117371 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a692_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 692))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 692) 305530) = 113520 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b692_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 692)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 692)) 305530) = 113520 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a692_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 692))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 692) 5604) = 50540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b692_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 692)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 692)) 5604) = 50540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a692_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 692))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 692) 221549) = 145432 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b692_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 692)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 692)) 221549) = 145432 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a692_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 692))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 692) 266275) = 32199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b692_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 692)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 692)) 266275) = 32199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a692_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 692))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 692) 186844) = 268190 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b692_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 692)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 692)) 186844) = 268190 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o692 : xone 692 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a692_0 b692_0 a692_1 b692_1 a692_2 b692_2
    a692_3 b692_3 a692_4 b692_4 a692_5 b692_5

theorem a693_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 693))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 693) 0) = 9140 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b693_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 693)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 693)) 0) = 9140 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a693_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 693))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 693) 305530) = 271959 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b693_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 693)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 693)) 305530) = 271959 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a693_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 693))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 693) 5604) = 262511 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b693_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 693)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 693)) 5604) = 262511 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a693_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 693))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 693) 221549) = 63778 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b693_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 693)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 693)) 221549) = 63778 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a693_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 693))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 693) 266275) = 173072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b693_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 693)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 693)) 266275) = 173072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a693_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 693))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 693) 186844) = 80222 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b693_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 693)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 693)) 186844) = 80222 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o693 : xone 693 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a693_0 b693_0 a693_1 b693_1 a693_2 b693_2
    a693_3 b693_3 a693_4 b693_4 a693_5 b693_5

theorem a694_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 694))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 694) 0) = 150188 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b694_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 694)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 694)) 0) = 150188 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a694_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 694))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 694) 305530) = 286724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b694_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 694)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 694)) 305530) = 286724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a694_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 694))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 694) 5604) = 255852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b694_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 694)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 694)) 5604) = 255852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a694_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 694))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 694) 221549) = 50133 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b694_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 694)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 694)) 221549) = 50133 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a694_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 694))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 694) 266275) = 127388 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b694_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 694)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 694)) 266275) = 127388 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a694_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 694))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 694) 186844) = 141506 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b694_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 694)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 694)) 186844) = 141506 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o694 : xone 694 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a694_0 b694_0 a694_1 b694_1 a694_2 b694_2
    a694_3 b694_3 a694_4 b694_4 a694_5 b694_5

theorem a695_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 695))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 695) 0) = 165194 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b695_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 695)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 695)) 0) = 165194 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a695_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 695))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 695) 305530) = 296663 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b695_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 695)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 695)) 305530) = 296663 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a695_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 695))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 695) 5604) = 184756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b695_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 695)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 695)) 5604) = 184756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a695_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 695))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 695) 221549) = 273704 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b695_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 695)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 695)) 221549) = 273704 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a695_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 695))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 695) 266275) = 20106 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b695_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 695)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 695)) 266275) = 20106 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a695_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 695))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 695) 186844) = 78083 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b695_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 695)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 695)) 186844) = 78083 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o695 : xone 695 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a695_0 b695_0 a695_1 b695_1 a695_2 b695_2
    a695_3 b695_3 a695_4 b695_4 a695_5 b695_5

theorem a696_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 696))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 696) 0) = 59206 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b696_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 696)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 696)) 0) = 59206 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a696_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 696))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 696) 305530) = 177732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b696_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 696)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 696)) 305530) = 177732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a696_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 696))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 696) 5604) = 58139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b696_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 696)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 696)) 5604) = 58139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a696_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 696))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 696) 221549) = 151993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b696_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 696)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 696)) 221549) = 151993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a696_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 696))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 696) 266275) = 7454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b696_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 696)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 696)) 266275) = 7454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a696_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 696))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 696) 186844) = 91447 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b696_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 696)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 696)) 186844) = 91447 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o696 : xone 696 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a696_0 b696_0 a696_1 b696_1 a696_2 b696_2
    a696_3 b696_3 a696_4 b696_4 a696_5 b696_5

theorem a697_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 697))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 697) 0) = 101196 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b697_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 697)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 697)) 0) = 101196 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a697_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 697))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 697) 305530) = 294909 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b697_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 697)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 697)) 305530) = 294909 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a697_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 697))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 697) 5604) = 224170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b697_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 697)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 697)) 5604) = 224170 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a697_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 697))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 697) 221549) = 151164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b697_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 697)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 697)) 221549) = 151164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a697_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 697))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 697) 266275) = 65993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b697_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 697)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 697)) 266275) = 65993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a697_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 697))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 697) 186844) = 128973 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b697_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 697)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 697)) 186844) = 128973 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o697 : xone 697 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a697_0 b697_0 a697_1 b697_1 a697_2 b697_2
    a697_3 b697_3 a697_4 b697_4 a697_5 b697_5

theorem a698_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 698))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 698) 0) = 52780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b698_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 698)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 698)) 0) = 52780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a698_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 698))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 698) 305530) = 263769 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b698_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 698)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 698)) 305530) = 263769 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a698_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 698))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 698) 5604) = 122421 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b698_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 698)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 698)) 5604) = 122421 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a698_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 698))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 698) 221549) = 66983 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b698_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 698)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 698)) 221549) = 66983 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a698_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 698))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 698) 266275) = 204530 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b698_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 698)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 698)) 266275) = 204530 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a698_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 698))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 698) 186844) = 210225 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b698_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 698)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 698)) 186844) = 210225 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o698 : xone 698 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a698_0 b698_0 a698_1 b698_1 a698_2 b698_2
    a698_3 b698_3 a698_4 b698_4 a698_5 b698_5

theorem a699_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 699))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 699) 0) = 214781 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b699_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 699)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 699)) 0) = 214781 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a699_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 699))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 699) 305530) = 226494 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b699_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 699)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 699)) 305530) = 226494 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a699_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 699))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 699) 5604) = 286370 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b699_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 699)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 699)) 5604) = 286370 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a699_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 699))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 699) 221549) = 155628 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b699_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 699)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 699)) 221549) = 155628 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a699_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 699))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 699) 266275) = 96757 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b699_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 699)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 699)) 266275) = 96757 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a699_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 699))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 699) 186844) = 251849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b699_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 699)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 699)) 186844) = 251849 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o699 : xone 699 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a699_0 b699_0 a699_1 b699_1 a699_2 b699_2
    a699_3 b699_3 a699_4 b699_4 a699_5 b699_5

theorem a700_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 700))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 700) 0) = 257638 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b700_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 700)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 700)) 0) = 257638 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a700_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 700))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 700) 305530) = 129679 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b700_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 700)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 700)) 305530) = 129679 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a700_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 700))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 700) 5604) = 73462 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b700_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 700)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 700)) 5604) = 73462 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a700_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 700))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 700) 221549) = 205905 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b700_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 700)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 700)) 221549) = 205905 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a700_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 700))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 700) 266275) = 148564 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b700_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 700)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 700)) 266275) = 148564 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a700_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 700))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 700) 186844) = 294819 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b700_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 700)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 700)) 186844) = 294819 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o700 : xone 700 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a700_0 b700_0 a700_1 b700_1 a700_2 b700_2
    a700_3 b700_3 a700_4 b700_4 a700_5 b700_5

theorem a701_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 701))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 701) 0) = 170337 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b701_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 701)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 701)) 0) = 170337 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a701_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 701))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 701) 305530) = 169988 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b701_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 701)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 701)) 305530) = 169988 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a701_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 701))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 701) 5604) = 184612 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b701_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 701)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 701)) 5604) = 184612 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a701_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 701))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 701) 221549) = 141092 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b701_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 701)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 701)) 221549) = 141092 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a701_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 701))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 701) 266275) = 52363 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b701_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 701)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 701)) 266275) = 52363 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a701_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 701))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 701) 186844) = 59517 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b701_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 701)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 701)) 186844) = 59517 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o701 : xone 701 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a701_0 b701_0 a701_1 b701_1 a701_2 b701_2
    a701_3 b701_3 a701_4 b701_4 a701_5 b701_5

theorem a702_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 702))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 702) 0) = 269467 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b702_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 702)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 702)) 0) = 269467 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a702_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 702))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 702) 305530) = 132630 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b702_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 702)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 702)) 305530) = 132630 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a702_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 702))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 702) 5604) = 85966 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b702_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 702)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 702)) 5604) = 85966 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a702_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 702))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 702) 221549) = 52349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b702_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 702)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 702)) 221549) = 52349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a702_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 702))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 702) 266275) = 42663 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b702_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 702)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 702)) 266275) = 42663 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a702_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 702))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 702) 186844) = 92262 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b702_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 702)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 702)) 186844) = 92262 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o702 : xone 702 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a702_0 b702_0 a702_1 b702_1 a702_2 b702_2
    a702_3 b702_3 a702_4 b702_4 a702_5 b702_5

theorem a703_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 703))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 703) 0) = 185692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b703_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 703)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 703)) 0) = 185692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a703_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 703))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 703) 305530) = 300542 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b703_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 703)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 703)) 305530) = 300542 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a703_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 703))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 703) 5604) = 55934 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b703_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 703)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 703)) 5604) = 55934 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a703_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 703))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 703) 221549) = 12028 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b703_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 703)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 703)) 221549) = 12028 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a703_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 703))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 703) 266275) = 284540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b703_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 703)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 703)) 266275) = 284540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a703_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 703))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 703) 186844) = 231520 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b703_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 703)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 703)) 186844) = 231520 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o703 : xone 703 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a703_0 b703_0 a703_1 b703_1 a703_2 b703_2
    a703_3 b703_3 a703_4 b703_4 a703_5 b703_5

theorem a704_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 704))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 704) 0) = 219552 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b704_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 704)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 704)) 0) = 219552 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a704_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 704))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 704) 305530) = 221831 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b704_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 704)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 704)) 305530) = 221831 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a704_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 704))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 704) 5604) = 97137 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b704_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 704)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 704)) 5604) = 97137 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a704_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 704))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 704) 221549) = 130684 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b704_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 704)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 704)) 221549) = 130684 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a704_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 704))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 704) 266275) = 46069 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b704_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 704)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 704)) 266275) = 46069 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a704_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 704))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 704) 186844) = 224242 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b704_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 704)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 704)) 186844) = 224242 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o704 : xone 704 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a704_0 b704_0 a704_1 b704_1 a704_2 b704_2
    a704_3 b704_3 a704_4 b704_4 a704_5 b704_5

theorem a705_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 705))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 705) 0) = 122297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b705_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 705)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 705)) 0) = 122297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a705_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 705))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 705) 305530) = 127567 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b705_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 705)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 705)) 305530) = 127567 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a705_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 705))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 705) 5604) = 34525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b705_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 705)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 705)) 5604) = 34525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a705_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 705))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 705) 221549) = 99541 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b705_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 705)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 705)) 221549) = 99541 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a705_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 705))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 705) 266275) = 241193 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b705_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 705)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 705)) 266275) = 241193 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a705_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 705))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 705) 186844) = 91736 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b705_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 705)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 705)) 186844) = 91736 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o705 : xone 705 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a705_0 b705_0 a705_1 b705_1 a705_2 b705_2
    a705_3 b705_3 a705_4 b705_4 a705_5 b705_5

theorem a706_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 706))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 706) 0) = 44276 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b706_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 706)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 706)) 0) = 44276 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a706_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 706))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 706) 305530) = 126186 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b706_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 706)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 706)) 305530) = 126186 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a706_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 706))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 706) 5604) = 7032 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b706_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 706)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 706)) 5604) = 7032 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a706_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 706))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 706) 221549) = 262355 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b706_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 706)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 706)) 221549) = 262355 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a706_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 706))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 706) 266275) = 291760 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b706_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 706)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 706)) 266275) = 291760 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a706_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 706))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 706) 186844) = 77242 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b706_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 706)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 706)) 186844) = 77242 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o706 : xone 706 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a706_0 b706_0 a706_1 b706_1 a706_2 b706_2
    a706_3 b706_3 a706_4 b706_4 a706_5 b706_5

theorem a707_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 707))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 707) 0) = 3424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b707_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 707)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 707)) 0) = 3424 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a707_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 707))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 707) 305530) = 291525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b707_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 707)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 707)) 305530) = 291525 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a707_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 707))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 707) 5604) = 184118 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b707_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 707)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 707)) 5604) = 184118 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a707_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 707))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 707) 221549) = 11488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b707_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 707)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 707)) 221549) = 11488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a707_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 707))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 707) 266275) = 104812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b707_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 707)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 707)) 266275) = 104812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a707_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 707))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 707) 186844) = 235381 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b707_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 707)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 707)) 186844) = 235381 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o707 : xone 707 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a707_0 b707_0 a707_1 b707_1 a707_2 b707_2
    a707_3 b707_3 a707_4 b707_4 a707_5 b707_5

theorem a708_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 708))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 708) 0) = 129845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b708_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 708)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 708)) 0) = 129845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a708_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 708))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 708) 305530) = 185750 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b708_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 708)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 708)) 305530) = 185750 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a708_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 708))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 708) 5604) = 7300 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b708_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 708)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 708)) 5604) = 7300 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a708_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 708))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 708) 221549) = 85162 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b708_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 708)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 708)) 221549) = 85162 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a708_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 708))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 708) 266275) = 297983 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b708_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 708)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 708)) 266275) = 297983 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a708_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 708))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 708) 186844) = 253809 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b708_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 708)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 708)) 186844) = 253809 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o708 : xone 708 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a708_0 b708_0 a708_1 b708_1 a708_2 b708_2
    a708_3 b708_3 a708_4 b708_4 a708_5 b708_5

theorem a709_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 709))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 709) 0) = 77689 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b709_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 709)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 709)) 0) = 77689 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a709_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 709))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 709) 305530) = 78021 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b709_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 709)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 709)) 305530) = 78021 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a709_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 709))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 709) 5604) = 84697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b709_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 709)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 709)) 5604) = 84697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a709_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 709))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 709) 221549) = 257235 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b709_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 709)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 709)) 221549) = 257235 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a709_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 709))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 709) 266275) = 262684 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b709_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 709)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 709)) 266275) = 262684 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a709_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 709))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 709) 186844) = 238104 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b709_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 709)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 709)) 186844) = 238104 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o709 : xone 709 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a709_0 b709_0 a709_1 b709_1 a709_2 b709_2
    a709_3 b709_3 a709_4 b709_4 a709_5 b709_5

theorem a710_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 710))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 710) 0) = 167295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b710_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 710)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 710)) 0) = 167295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a710_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 710))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 710) 305530) = 227637 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b710_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 710)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 710)) 305530) = 227637 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a710_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 710))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 710) 5604) = 160192 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b710_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 710)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 710)) 5604) = 160192 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a710_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 710))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 710) 221549) = 241420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b710_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 710)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 710)) 221549) = 241420 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a710_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 710))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 710) 266275) = 20822 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b710_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 710)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 710)) 266275) = 20822 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a710_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 710))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 710) 186844) = 27004 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b710_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 710)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 710)) 186844) = 27004 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o710 : xone 710 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a710_0 b710_0 a710_1 b710_1 a710_2 b710_2
    a710_3 b710_3 a710_4 b710_4 a710_5 b710_5

theorem a711_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 711))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 711) 0) = 279155 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b711_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 711)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 711)) 0) = 279155 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a711_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 711))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 711) 305530) = 236826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b711_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 711)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 711)) 305530) = 236826 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a711_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 711))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 711) 5604) = 153685 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b711_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 711)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 711)) 5604) = 153685 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a711_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 711))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 711) 221549) = 207234 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b711_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 711)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 711)) 221549) = 207234 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a711_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 711))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 711) 266275) = 248945 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b711_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 711)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 711)) 266275) = 248945 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a711_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 711))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 711) 186844) = 106701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b711_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 711)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 711)) 186844) = 106701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o711 : xone 711 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a711_0 b711_0 a711_1 b711_1 a711_2 b711_2
    a711_3 b711_3 a711_4 b711_4 a711_5 b711_5

theorem a712_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 712))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 712) 0) = 135808 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b712_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 712)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 712)) 0) = 135808 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a712_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 712))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 712) 305530) = 212983 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b712_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 712)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 712)) 305530) = 212983 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a712_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 712))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 712) 5604) = 298209 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b712_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 712)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 712)) 5604) = 298209 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a712_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 712))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 712) 221549) = 264305 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b712_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 712)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 712)) 221549) = 264305 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a712_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 712))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 712) 266275) = 70863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b712_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 712)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 712)) 266275) = 70863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a712_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 712))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 712) 186844) = 149184 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b712_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 712)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 712)) 186844) = 149184 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o712 : xone 712 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a712_0 b712_0 a712_1 b712_1 a712_2 b712_2
    a712_3 b712_3 a712_4 b712_4 a712_5 b712_5

theorem a713_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 713))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 713) 0) = 108414 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b713_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 713)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 713)) 0) = 108414 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a713_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 713))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 713) 305530) = 222023 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b713_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 713)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 713)) 305530) = 222023 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a713_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 713))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 713) 5604) = 95909 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b713_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 713)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 713)) 5604) = 95909 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a713_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 713))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 713) 221549) = 300357 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b713_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 713)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 713)) 221549) = 300357 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a713_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 713))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 713) 266275) = 150834 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b713_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 713)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 713)) 266275) = 150834 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a713_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 713))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 713) 186844) = 242118 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b713_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 713)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 713)) 186844) = 242118 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o713 : xone 713 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a713_0 b713_0 a713_1 b713_1 a713_2 b713_2
    a713_3 b713_3 a713_4 b713_4 a713_5 b713_5

theorem a714_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 714))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 714) 0) = 191850 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b714_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 714)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 714)) 0) = 191850 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a714_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 714))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 714) 305530) = 56559 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b714_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 714)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 714)) 305530) = 56559 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a714_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 714))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 714) 5604) = 236568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b714_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 714)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 714)) 5604) = 236568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a714_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 714))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 714) 221549) = 89883 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b714_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 714)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 714)) 221549) = 89883 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a714_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 714))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 714) 266275) = 179177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b714_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 714)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 714)) 266275) = 179177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a714_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 714))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 714) 186844) = 236763 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b714_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 714)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 714)) 186844) = 236763 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o714 : xone 714 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a714_0 b714_0 a714_1 b714_1 a714_2 b714_2
    a714_3 b714_3 a714_4 b714_4 a714_5 b714_5

theorem a715_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 715))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 715) 0) = 183165 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b715_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 715)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 715)) 0) = 183165 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a715_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 715))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 715) 305530) = 19375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b715_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 715)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 715)) 305530) = 19375 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a715_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 715))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 715) 5604) = 293839 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b715_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 715)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 715)) 5604) = 293839 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a715_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 715))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 715) 221549) = 185603 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b715_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 715)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 715)) 221549) = 185603 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a715_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 715))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 715) 266275) = 215784 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b715_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 715)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 715)) 266275) = 215784 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a715_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 715))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 715) 186844) = 210463 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b715_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 715)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 715)) 186844) = 210463 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o715 : xone 715 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a715_0 b715_0 a715_1 b715_1 a715_2 b715_2
    a715_3 b715_3 a715_4 b715_4 a715_5 b715_5

theorem a716_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 716))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 716) 0) = 303959 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b716_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 716)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 716)) 0) = 303959 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a716_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 716))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 716) 305530) = 277411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b716_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 716)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 716)) 305530) = 277411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a716_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 716))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 716) 5604) = 156026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b716_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 716)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 716)) 5604) = 156026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a716_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 716))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 716) 221549) = 77230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b716_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 716)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 716)) 221549) = 77230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a716_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 716))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 716) 266275) = 57350 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b716_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 716)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 716)) 266275) = 57350 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a716_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 716))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 716) 186844) = 218851 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b716_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 716)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 716)) 186844) = 218851 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o716 : xone 716 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a716_0 b716_0 a716_1 b716_1 a716_2 b716_2
    a716_3 b716_3 a716_4 b716_4 a716_5 b716_5

theorem a717_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 717))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 717) 0) = 167407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b717_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 717)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 717)) 0) = 167407 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a717_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 717))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 717) 305530) = 2831 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b717_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 717)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 717)) 305530) = 2831 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a717_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 717))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 717) 5604) = 296543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b717_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 717)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 717)) 5604) = 296543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a717_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 717))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 717) 221549) = 242510 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b717_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 717)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 717)) 221549) = 242510 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a717_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 717))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 717) 266275) = 13002 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b717_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 717)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 717)) 266275) = 13002 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a717_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 717))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 717) 186844) = 131943 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b717_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 717)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 717)) 186844) = 131943 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o717 : xone 717 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a717_0 b717_0 a717_1 b717_1 a717_2 b717_2
    a717_3 b717_3 a717_4 b717_4 a717_5 b717_5

theorem a718_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 718))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 718) 0) = 181778 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b718_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 718)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 718)) 0) = 181778 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a718_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 718))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 718) 305530) = 245230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b718_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 718)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 718)) 305530) = 245230 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a718_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 718))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 718) 5604) = 297901 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b718_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 718)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 718)) 5604) = 297901 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a718_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 718))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 718) 221549) = 220797 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b718_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 718)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 718)) 221549) = 220797 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a718_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 718))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 718) 266275) = 126593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b718_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 718)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 718)) 266275) = 126593 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a718_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 718))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 718) 186844) = 3869 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b718_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 718)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 718)) 186844) = 3869 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o718 : xone 718 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a718_0 b718_0 a718_1 b718_1 a718_2 b718_2
    a718_3 b718_3 a718_4 b718_4 a718_5 b718_5

theorem a719_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 719))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 719) 0) = 99261 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b719_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 719)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 719)) 0) = 99261 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a719_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 719))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 719) 305530) = 198208 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b719_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 719)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 719)) 305530) = 198208 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a719_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 719))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 719) 5604) = 102688 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b719_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 719)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 719)) 5604) = 102688 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a719_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 719))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 719) 221549) = 73589 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b719_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 719)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 719)) 221549) = 73589 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a719_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 719))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 719) 266275) = 126461 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b719_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 719)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 719)) 266275) = 126461 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a719_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 719))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 719) 186844) = 100300 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b719_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 719)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 719)) 186844) = 100300 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o719 : xone 719 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a719_0 b719_0 a719_1 b719_1 a719_2 b719_2
    a719_3 b719_3 a719_4 b719_4 a719_5 b719_5

theorem a720_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 720))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 720) 0) = 91714 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b720_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 720)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 720)) 0) = 91714 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a720_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 720))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 720) 305530) = 169627 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b720_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 720)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 720)) 305530) = 169627 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a720_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 720))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 720) 5604) = 83131 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b720_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 720)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 720)) 5604) = 83131 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a720_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 720))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 720) 221549) = 268837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b720_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 720)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 720)) 221549) = 268837 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a720_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 720))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 720) 266275) = 127902 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b720_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 720)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 720)) 266275) = 127902 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a720_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 720))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 720) 186844) = 140090 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b720_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 720)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 720)) 186844) = 140090 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o720 : xone 720 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a720_0 b720_0 a720_1 b720_1 a720_2 b720_2
    a720_3 b720_3 a720_4 b720_4 a720_5 b720_5

theorem a721_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 721))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 721) 0) = 166600 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b721_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 721)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 721)) 0) = 166600 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a721_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 721))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 721) 305530) = 217008 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b721_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 721)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 721)) 305530) = 217008 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a721_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 721))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 721) 5604) = 139105 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b721_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 721)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 721)) 5604) = 139105 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a721_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 721))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 721) 221549) = 272059 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b721_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 721)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 721)) 221549) = 272059 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a721_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 721))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 721) 266275) = 241148 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b721_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 721)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 721)) 266275) = 241148 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a721_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 721))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 721) 186844) = 205983 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b721_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 721)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 721)) 186844) = 205983 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o721 : xone 721 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a721_0 b721_0 a721_1 b721_1 a721_2 b721_2
    a721_3 b721_3 a721_4 b721_4 a721_5 b721_5

theorem a722_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 722))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 722) 0) = 181465 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b722_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 722)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 722)) 0) = 181465 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a722_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 722))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 722) 305530) = 1956 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b722_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 722)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 722)) 305530) = 1956 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a722_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 722))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 722) 5604) = 119454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b722_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 722)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 722)) 5604) = 119454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a722_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 722))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 722) 221549) = 230985 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b722_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 722)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 722)) 221549) = 230985 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a722_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 722))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 722) 266275) = 256891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b722_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 722)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 722)) 266275) = 256891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a722_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 722))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 722) 186844) = 186043 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b722_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 722)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 722)) 186844) = 186043 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o722 : xone 722 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a722_0 b722_0 a722_1 b722_1 a722_2 b722_2
    a722_3 b722_3 a722_4 b722_4 a722_5 b722_5

theorem a723_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 723))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 723) 0) = 52236 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b723_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 723)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 723)) 0) = 52236 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a723_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 723))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 723) 305530) = 130924 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b723_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 723)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 723)) 305530) = 130924 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a723_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 723))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 723) 5604) = 75579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b723_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 723)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 723)) 5604) = 75579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a723_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 723))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 723) 221549) = 84787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b723_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 723)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 723)) 221549) = 84787 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a723_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 723))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 723) 266275) = 83838 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b723_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 723)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 723)) 266275) = 83838 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a723_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 723))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 723) 186844) = 45685 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b723_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 723)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 723)) 186844) = 45685 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o723 : xone 723 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a723_0 b723_0 a723_1 b723_1 a723_2 b723_2
    a723_3 b723_3 a723_4 b723_4 a723_5 b723_5

theorem a724_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 724))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 724) 0) = 210555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b724_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 724)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 724)) 0) = 210555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a724_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 724))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 724) 305530) = 24744 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b724_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 724)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 724)) 305530) = 24744 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a724_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 724))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 724) 5604) = 34436 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b724_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 724)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 724)) 5604) = 34436 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a724_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 724))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 724) 221549) = 289091 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b724_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 724)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 724)) 221549) = 289091 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a724_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 724))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 724) 266275) = 5745 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b724_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 724)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 724)) 266275) = 5745 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a724_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 724))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 724) 186844) = 153328 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b724_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 724)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 724)) 186844) = 153328 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o724 : xone 724 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a724_0 b724_0 a724_1 b724_1 a724_2 b724_2
    a724_3 b724_3 a724_4 b724_4 a724_5 b724_5

theorem a725_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 725))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 725) 0) = 41403 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b725_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 725)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 725)) 0) = 41403 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a725_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 725))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 725) 305530) = 180450 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b725_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 725)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 725)) 305530) = 180450 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a725_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 725))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 725) 5604) = 61260 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b725_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 725)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 725)) 5604) = 61260 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a725_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 725))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 725) 221549) = 295854 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b725_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 725)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 725)) 221549) = 295854 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a725_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 725))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 725) 266275) = 66177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b725_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 725)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 725)) 266275) = 66177 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a725_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 725))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 725) 186844) = 135349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b725_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 725)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 725)) 186844) = 135349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o725 : xone 725 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a725_0 b725_0 a725_1 b725_1 a725_2 b725_2
    a725_3 b725_3 a725_4 b725_4 a725_5 b725_5

theorem a726_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 726))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 726) 0) = 303164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b726_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 726)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 726)) 0) = 303164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a726_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 726))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 726) 305530) = 260297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b726_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 726)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 726)) 305530) = 260297 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a726_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 726))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 726) 5604) = 171872 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b726_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 726)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 726)) 5604) = 171872 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a726_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 726))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 726) 221549) = 118999 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b726_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 726)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 726)) 221549) = 118999 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a726_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 726))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 726) 266275) = 210518 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b726_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 726)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 726)) 266275) = 210518 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a726_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 726))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 726) 186844) = 57564 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b726_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 726)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 726)) 186844) = 57564 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o726 : xone 726 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a726_0 b726_0 a726_1 b726_1 a726_2 b726_2
    a726_3 b726_3 a726_4 b726_4 a726_5 b726_5

theorem a727_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 727))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 727) 0) = 159303 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b727_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 727)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 727)) 0) = 159303 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a727_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 727))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 727) 305530) = 129540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b727_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 727)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 727)) 305530) = 129540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a727_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 727))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 727) 5604) = 104078 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b727_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 727)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 727)) 5604) = 104078 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a727_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 727))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 727) 221549) = 122343 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b727_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 727)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 727)) 221549) = 122343 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a727_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 727))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 727) 266275) = 46436 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b727_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 727)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 727)) 266275) = 46436 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a727_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 727))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 727) 186844) = 290259 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b727_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 727)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 727)) 186844) = 290259 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o727 : xone 727 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a727_0 b727_0 a727_1 b727_1 a727_2 b727_2
    a727_3 b727_3 a727_4 b727_4 a727_5 b727_5

theorem a728_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 728))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 728) 0) = 143863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b728_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 728)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 728)) 0) = 143863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a728_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 728))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 728) 305530) = 296027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b728_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 728)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 728)) 305530) = 296027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a728_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 728))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 728) 5604) = 128803 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b728_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 728)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 728)) 5604) = 128803 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a728_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 728))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 728) 221549) = 260640 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b728_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 728)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 728)) 221549) = 260640 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a728_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 728))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 728) 266275) = 221825 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b728_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 728)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 728)) 266275) = 221825 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a728_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 728))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 728) 186844) = 82880 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b728_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 728)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 728)) 186844) = 82880 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o728 : xone 728 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a728_0 b728_0 a728_1 b728_1 a728_2 b728_2
    a728_3 b728_3 a728_4 b728_4 a728_5 b728_5

theorem a729_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 729))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 729) 0) = 168732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b729_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 729)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 729)) 0) = 168732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a729_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 729))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 729) 305530) = 223850 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b729_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 729)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 729)) 305530) = 223850 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a729_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 729))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 729) 5604) = 116885 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b729_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 729)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 729)) 5604) = 116885 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a729_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 729))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 729) 221549) = 9146 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b729_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 729)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 729)) 221549) = 9146 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a729_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 729))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 729) 266275) = 98172 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b729_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 729)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 729)) 266275) = 98172 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a729_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 729))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 729) 186844) = 102908 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b729_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 729)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 729)) 186844) = 102908 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o729 : xone 729 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a729_0 b729_0 a729_1 b729_1 a729_2 b729_2
    a729_3 b729_3 a729_4 b729_4 a729_5 b729_5

theorem a730_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 730))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 730) 0) = 133191 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b730_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 730)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 730)) 0) = 133191 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a730_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 730))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 730) 305530) = 279274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b730_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 730)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 730)) 305530) = 279274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a730_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 730))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 730) 5604) = 1740 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b730_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 730)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 730)) 5604) = 1740 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a730_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 730))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 730) 221549) = 238503 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b730_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 730)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 730)) 221549) = 238503 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a730_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 730))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 730) 266275) = 95626 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b730_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 730)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 730)) 266275) = 95626 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a730_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 730))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 730) 186844) = 115545 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b730_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 730)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 730)) 186844) = 115545 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o730 : xone 730 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a730_0 b730_0 a730_1 b730_1 a730_2 b730_2
    a730_3 b730_3 a730_4 b730_4 a730_5 b730_5

theorem a731_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 731))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 731) 0) = 150557 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b731_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 731)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 731)) 0) = 150557 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a731_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 731))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 731) 305530) = 82701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b731_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 731)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 731)) 305530) = 82701 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a731_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 731))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 731) 5604) = 89062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b731_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 731)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 731)) 5604) = 89062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a731_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 731))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 731) 221549) = 235482 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b731_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 731)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 731)) 221549) = 235482 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a731_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 731))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 731) 266275) = 196388 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b731_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 731)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 731)) 266275) = 196388 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a731_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 731))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 731) 186844) = 234768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b731_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 731)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 731)) 186844) = 234768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o731 : xone 731 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a731_0 b731_0 a731_1 b731_1 a731_2 b731_2
    a731_3 b731_3 a731_4 b731_4 a731_5 b731_5

theorem a732_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 732))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 732) 0) = 238107 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b732_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 732)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 732)) 0) = 238107 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a732_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 732))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 732) 305530) = 22999 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b732_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 732)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 732)) 305530) = 22999 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a732_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 732))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 732) 5604) = 82990 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b732_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 732)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 732)) 5604) = 82990 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a732_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 732))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 732) 221549) = 239981 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b732_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 732)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 732)) 221549) = 239981 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a732_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 732))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 732) 266275) = 128577 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b732_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 732)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 732)) 266275) = 128577 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a732_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 732))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 732) 186844) = 217034 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b732_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 732)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 732)) 186844) = 217034 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o732 : xone 732 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a732_0 b732_0 a732_1 b732_1 a732_2 b732_2
    a732_3 b732_3 a732_4 b732_4 a732_5 b732_5

theorem a733_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 733))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 733) 0) = 180990 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b733_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 733)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 733)) 0) = 180990 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a733_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 733))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 733) 305530) = 116073 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b733_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 733)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 733)) 305530) = 116073 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a733_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 733))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 733) 5604) = 297330 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b733_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 733)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 733)) 5604) = 297330 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a733_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 733))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 733) 221549) = 3779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b733_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 733)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 733)) 221549) = 3779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a733_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 733))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 733) 266275) = 106232 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b733_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 733)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 733)) 266275) = 106232 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a733_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 733))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 733) 186844) = 91410 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b733_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 733)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 733)) 186844) = 91410 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o733 : xone 733 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a733_0 b733_0 a733_1 b733_1 a733_2 b733_2
    a733_3 b733_3 a733_4 b733_4 a733_5 b733_5

theorem a734_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 734))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 734) 0) = 183083 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b734_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 734)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 734)) 0) = 183083 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a734_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 734))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 734) 305530) = 258426 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b734_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 734)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 734)) 305530) = 258426 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a734_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 734))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 734) 5604) = 244573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b734_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 734)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 734)) 5604) = 244573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a734_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 734))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 734) 221549) = 58611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b734_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 734)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 734)) 221549) = 58611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a734_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 734))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 734) 266275) = 101380 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b734_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 734)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 734)) 266275) = 101380 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a734_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 734))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 734) 186844) = 294140 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b734_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 734)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 734)) 186844) = 294140 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o734 : xone 734 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a734_0 b734_0 a734_1 b734_1 a734_2 b734_2
    a734_3 b734_3 a734_4 b734_4 a734_5 b734_5

theorem a735_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 735))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 735) 0) = 190129 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b735_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 735)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 735)) 0) = 190129 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a735_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 735))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 735) 305530) = 88409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b735_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 735)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 735)) 305530) = 88409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a735_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 735))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 735) 5604) = 283210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b735_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 735)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 735)) 5604) = 283210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a735_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 735))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 735) 221549) = 213957 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b735_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 735)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 735)) 221549) = 213957 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a735_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 735))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 735) 266275) = 40930 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b735_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 735)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 735)) 266275) = 40930 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a735_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 735))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 735) 186844) = 74753 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b735_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 735)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 735)) 186844) = 74753 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o735 : xone 735 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a735_0 b735_0 a735_1 b735_1 a735_2 b735_2
    a735_3 b735_3 a735_4 b735_4 a735_5 b735_5

theorem a736_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 736))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 736) 0) = 103014 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b736_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 736)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 736)) 0) = 103014 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a736_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 736))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 736) 305530) = 111330 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b736_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 736)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 736)) 305530) = 111330 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a736_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 736))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 736) 5604) = 206551 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b736_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 736)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 736)) 5604) = 206551 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a736_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 736))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 736) 221549) = 296894 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b736_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 736)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 736)) 221549) = 296894 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a736_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 736))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 736) 266275) = 19589 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b736_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 736)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 736)) 266275) = 19589 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a736_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 736))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 736) 186844) = 255932 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b736_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 736)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 736)) 186844) = 255932 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o736 : xone 736 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a736_0 b736_0 a736_1 b736_1 a736_2 b736_2
    a736_3 b736_3 a736_4 b736_4 a736_5 b736_5

theorem a737_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 737))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 737) 0) = 137739 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b737_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 737)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 737)) 0) = 137739 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a737_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 737))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 737) 305530) = 250190 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b737_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 737)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 737)) 305530) = 250190 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a737_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 737))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 737) 5604) = 111132 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b737_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 737)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 737)) 5604) = 111132 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a737_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 737))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 737) 221549) = 187425 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b737_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 737)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 737)) 221549) = 187425 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a737_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 737))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 737) 266275) = 170504 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b737_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 737)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 737)) 266275) = 170504 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a737_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 737))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 737) 186844) = 235167 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b737_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 737)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 737)) 186844) = 235167 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o737 : xone 737 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a737_0 b737_0 a737_1 b737_1 a737_2 b737_2
    a737_3 b737_3 a737_4 b737_4 a737_5 b737_5

theorem a738_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 738))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 738) 0) = 119092 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b738_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 738)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 738)) 0) = 119092 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a738_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 738))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 738) 305530) = 298221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b738_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 738)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 738)) 305530) = 298221 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a738_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 738))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 738) 5604) = 260626 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b738_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 738)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 738)) 5604) = 260626 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a738_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 738))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 738) 221549) = 187179 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b738_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 738)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 738)) 221549) = 187179 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a738_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 738))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 738) 266275) = 96541 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b738_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 738)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 738)) 266275) = 96541 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a738_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 738))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 738) 186844) = 22875 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b738_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 738)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 738)) 186844) = 22875 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o738 : xone 738 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a738_0 b738_0 a738_1 b738_1 a738_2 b738_2
    a738_3 b738_3 a738_4 b738_4 a738_5 b738_5

theorem a739_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 739))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 739) 0) = 186782 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b739_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 739)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 739)) 0) = 186782 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a739_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 739))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 739) 305530) = 135275 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b739_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 739)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 739)) 305530) = 135275 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a739_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 739))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 739) 5604) = 155856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b739_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 739)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 739)) 5604) = 155856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a739_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 739))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 739) 221549) = 84921 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b739_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 739)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 739)) 221549) = 84921 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a739_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 739))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 739) 266275) = 42650 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b739_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 739)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 739)) 266275) = 42650 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a739_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 739))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 739) 186844) = 62540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b739_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 739)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 739)) 186844) = 62540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o739 : xone 739 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a739_0 b739_0 a739_1 b739_1 a739_2 b739_2
    a739_3 b739_3 a739_4 b739_4 a739_5 b739_5

theorem a740_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 740))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 740) 0) = 53534 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b740_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 740)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 740)) 0) = 53534 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a740_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 740))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 740) 305530) = 15061 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b740_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 740)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 740)) 305530) = 15061 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a740_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 740))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 740) 5604) = 281046 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b740_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 740)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 740)) 5604) = 281046 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a740_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 740))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 740) 221549) = 137293 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b740_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 740)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 740)) 221549) = 137293 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a740_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 740))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 740) 266275) = 19982 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b740_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 740)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 740)) 266275) = 19982 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a740_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 740))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 740) 186844) = 236885 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b740_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 740)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 740)) 186844) = 236885 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o740 : xone 740 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a740_0 b740_0 a740_1 b740_1 a740_2 b740_2
    a740_3 b740_3 a740_4 b740_4 a740_5 b740_5

theorem a741_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 741))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 741) 0) = 84659 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b741_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 741)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 741)) 0) = 84659 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a741_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 741))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 741) 305530) = 72783 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b741_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 741)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 741)) 305530) = 72783 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a741_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 741))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 741) 5604) = 101564 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b741_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 741)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 741)) 5604) = 101564 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a741_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 741))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 741) 221549) = 138295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b741_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 741)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 741)) 221549) = 138295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a741_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 741))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 741) 266275) = 297695 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b741_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 741)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 741)) 266275) = 297695 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a741_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 741))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 741) 186844) = 141817 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b741_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 741)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 741)) 186844) = 141817 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o741 : xone 741 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a741_0 b741_0 a741_1 b741_1 a741_2 b741_2
    a741_3 b741_3 a741_4 b741_4 a741_5 b741_5

theorem a742_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 742))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 742) 0) = 220579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b742_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 742)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 742)) 0) = 220579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a742_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 742))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 742) 305530) = 285964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b742_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 742)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 742)) 305530) = 285964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a742_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 742))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 742) 5604) = 243705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b742_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 742)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 742)) 5604) = 243705 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a742_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 742))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 742) 221549) = 110028 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b742_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 742)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 742)) 221549) = 110028 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a742_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 742))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 742) 266275) = 114566 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b742_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 742)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 742)) 266275) = 114566 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a742_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 742))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 742) 186844) = 160724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b742_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 742)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 742)) 186844) = 160724 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o742 : xone 742 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a742_0 b742_0 a742_1 b742_1 a742_2 b742_2
    a742_3 b742_3 a742_4 b742_4 a742_5 b742_5

theorem a743_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 743))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 743) 0) = 246163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b743_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 743)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 743)) 0) = 246163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a743_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 743))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 743) 305530) = 24269 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b743_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 743)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 743)) 305530) = 24269 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a743_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 743))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 743) 5604) = 137543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b743_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 743)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 743)) 5604) = 137543 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a743_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 743))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 743) 221549) = 207609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b743_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 743)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 743)) 221549) = 207609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a743_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 743))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 743) 266275) = 173888 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b743_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 743)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 743)) 266275) = 173888 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a743_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 743))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 743) 186844) = 101449 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b743_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 743)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 743)) 186844) = 101449 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o743 : xone 743 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a743_0 b743_0 a743_1 b743_1 a743_2 b743_2
    a743_3 b743_3 a743_4 b743_4 a743_5 b743_5

theorem a744_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 744))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 744) 0) = 142615 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b744_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 744)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 744)) 0) = 142615 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a744_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 744))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 744) 305530) = 67366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b744_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 744)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 744)) 305530) = 67366 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a744_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 744))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 744) 5604) = 188994 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b744_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 744)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 744)) 5604) = 188994 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a744_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 744))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 744) 221549) = 214196 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b744_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 744)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 744)) 221549) = 214196 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a744_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 744))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 744) 266275) = 151057 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b744_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 744)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 744)) 266275) = 151057 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a744_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 744))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 744) 186844) = 149535 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b744_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 744)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 744)) 186844) = 149535 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o744 : xone 744 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a744_0 b744_0 a744_1 b744_1 a744_2 b744_2
    a744_3 b744_3 a744_4 b744_4 a744_5 b744_5

theorem a745_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 745))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 745) 0) = 161880 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b745_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 745)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 745)) 0) = 161880 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a745_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 745))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 745) 305530) = 97618 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b745_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 745)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 745)) 305530) = 97618 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a745_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 745))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 745) 5604) = 259665 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b745_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 745)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 745)) 5604) = 259665 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a745_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 745))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 745) 221549) = 201382 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b745_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 745)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 745)) 221549) = 201382 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a745_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 745))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 745) 266275) = 126772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b745_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 745)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 745)) 266275) = 126772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a745_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 745))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 745) 186844) = 54655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b745_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 745)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 745)) 186844) = 54655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o745 : xone 745 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a745_0 b745_0 a745_1 b745_1 a745_2 b745_2
    a745_3 b745_3 a745_4 b745_4 a745_5 b745_5

theorem a746_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 746))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 746) 0) = 183487 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b746_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 746)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 746)) 0) = 183487 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a746_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 746))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 746) 305530) = 92664 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b746_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 746)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 746)) 305530) = 92664 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a746_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 746))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 746) 5604) = 140342 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b746_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 746)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 746)) 5604) = 140342 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a746_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 746))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 746) 221549) = 85272 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b746_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 746)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 746)) 221549) = 85272 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a746_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 746))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 746) 266275) = 262780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b746_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 746)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 746)) 266275) = 262780 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a746_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 746))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 746) 186844) = 236902 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b746_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 746)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 746)) 186844) = 236902 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o746 : xone 746 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a746_0 b746_0 a746_1 b746_1 a746_2 b746_2
    a746_3 b746_3 a746_4 b746_4 a746_5 b746_5

theorem a747_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 747))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 747) 0) = 30160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b747_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 747)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 747)) 0) = 30160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a747_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 747))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 747) 305530) = 189733 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b747_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 747)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 747)) 305530) = 189733 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a747_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 747))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 747) 5604) = 48945 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b747_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 747)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 747)) 5604) = 48945 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a747_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 747))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 747) 221549) = 110261 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b747_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 747)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 747)) 221549) = 110261 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a747_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 747))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 747) 266275) = 62924 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b747_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 747)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 747)) 266275) = 62924 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a747_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 747))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 747) 186844) = 274254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b747_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 747)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 747)) 186844) = 274254 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o747 : xone 747 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a747_0 b747_0 a747_1 b747_1 a747_2 b747_2
    a747_3 b747_3 a747_4 b747_4 a747_5 b747_5

theorem a748_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 748))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 748) 0) = 206295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b748_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 748)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 748)) 0) = 206295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a748_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 748))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 748) 305530) = 250204 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b748_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 748)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 748)) 305530) = 250204 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a748_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 748))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 748) 5604) = 292586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b748_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 748)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 748)) 5604) = 292586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a748_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 748))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 748) 221549) = 62160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b748_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 748)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 748)) 221549) = 62160 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a748_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 748))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 748) 266275) = 222267 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b748_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 748)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 748)) 266275) = 222267 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a748_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 748))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 748) 186844) = 137503 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b748_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 748)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 748)) 186844) = 137503 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o748 : xone 748 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a748_0 b748_0 a748_1 b748_1 a748_2 b748_2
    a748_3 b748_3 a748_4 b748_4 a748_5 b748_5

theorem a749_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 749))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 749) 0) = 70511 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b749_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 749)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 749)) 0) = 70511 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a749_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 749))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 749) 305530) = 232446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b749_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 749)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 749)) 305530) = 232446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a749_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 749))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 749) 5604) = 214773 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b749_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 749)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 749)) 5604) = 214773 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a749_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 749))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 749) 221549) = 28891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b749_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 749)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 749)) 221549) = 28891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a749_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 749))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 749) 266275) = 275313 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b749_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 749)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 749)) 266275) = 275313 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a749_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 749))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 749) 186844) = 288900 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b749_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 749)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 749)) 186844) = 288900 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o749 : xone 749 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a749_0 b749_0 a749_1 b749_1 a749_2 b749_2
    a749_3 b749_3 a749_4 b749_4 a749_5 b749_5

theorem a750_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 750))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 750) 0) = 168941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b750_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 750)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 750)) 0) = 168941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a750_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 750))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 750) 305530) = 82882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b750_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 750)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 750)) 305530) = 82882 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a750_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 750))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 750) 5604) = 112415 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b750_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 750)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 750)) 5604) = 112415 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a750_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 750))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 750) 221549) = 208433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b750_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 750)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 750)) 221549) = 208433 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a750_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 750))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 750) 266275) = 188070 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b750_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 750)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 750)) 266275) = 188070 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a750_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 750))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 750) 186844) = 191255 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b750_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 750)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 750)) 186844) = 191255 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o750 : xone 750 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a750_0 b750_0 a750_1 b750_1 a750_2 b750_2
    a750_3 b750_3 a750_4 b750_4 a750_5 b750_5

theorem a751_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 751))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 751) 0) = 304197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b751_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 751)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 751)) 0) = 304197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a751_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 751))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 751) 305530) = 110103 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b751_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 751)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 751)) 305530) = 110103 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a751_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 751))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 751) 5604) = 197772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b751_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 751)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 751)) 5604) = 197772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a751_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 751))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 751) 221549) = 151615 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b751_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 751)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 751)) 221549) = 151615 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a751_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 751))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 751) 266275) = 141836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b751_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 751)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 751)) 266275) = 141836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a751_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 751))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 751) 186844) = 260245 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b751_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 751)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 751)) 186844) = 260245 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o751 : xone 751 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a751_0 b751_0 a751_1 b751_1 a751_2 b751_2
    a751_3 b751_3 a751_4 b751_4 a751_5 b751_5

theorem a752_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 752))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 752) 0) = 55549 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b752_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 752)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 752)) 0) = 55549 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a752_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 752))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 752) 305530) = 207107 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b752_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 752)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 752)) 305530) = 207107 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a752_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 752))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 752) 5604) = 293198 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b752_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 752)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 752)) 5604) = 293198 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a752_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 752))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 752) 221549) = 69299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b752_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 752)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 752)) 221549) = 69299 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a752_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 752))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 752) 266275) = 147758 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b752_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 752)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 752)) 266275) = 147758 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a752_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 752))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 752) 186844) = 287080 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b752_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 752)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 752)) 186844) = 287080 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o752 : xone 752 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a752_0 b752_0 a752_1 b752_1 a752_2 b752_2
    a752_3 b752_3 a752_4 b752_4 a752_5 b752_5

theorem a753_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 753))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 753) 0) = 62698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b753_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 753)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 753)) 0) = 62698 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a753_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 753))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 753) 305530) = 108172 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b753_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 753)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 753)) 305530) = 108172 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a753_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 753))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 753) 5604) = 100973 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b753_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 753)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 753)) 5604) = 100973 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a753_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 753))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 753) 221549) = 178852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b753_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 753)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 753)) 221549) = 178852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a753_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 753))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 753) 266275) = 266574 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b753_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 753)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 753)) 266275) = 266574 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a753_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 753))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 753) 186844) = 64140 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b753_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 753)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 753)) 186844) = 64140 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o753 : xone 753 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a753_0 b753_0 a753_1 b753_1 a753_2 b753_2
    a753_3 b753_3 a753_4 b753_4 a753_5 b753_5

theorem a754_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 754))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 754) 0) = 22860 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b754_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 754)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 754)) 0) = 22860 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a754_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 754))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 754) 305530) = 153054 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b754_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 754)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 754)) 305530) = 153054 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a754_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 754))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 754) 5604) = 49532 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b754_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 754)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 754)) 5604) = 49532 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a754_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 754))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 754) 221549) = 298207 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b754_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 754)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 754)) 221549) = 298207 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a754_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 754))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 754) 266275) = 184518 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b754_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 754)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 754)) 266275) = 184518 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a754_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 754))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 754) 186844) = 110445 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b754_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 754)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 754)) 186844) = 110445 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o754 : xone 754 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a754_0 b754_0 a754_1 b754_1 a754_2 b754_2
    a754_3 b754_3 a754_4 b754_4 a754_5 b754_5

theorem a755_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 755))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 755) 0) = 134369 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b755_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 755)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 755)) 0) = 134369 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a755_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 755))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 755) 305530) = 124341 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b755_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 755)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 755)) 305530) = 124341 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a755_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 755))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 755) 5604) = 183062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b755_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 755)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 755)) 5604) = 183062 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a755_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 755))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 755) 221549) = 221181 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b755_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 755)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 755)) 221549) = 221181 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a755_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 755))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 755) 266275) = 245633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b755_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 755)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 755)) 266275) = 245633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a755_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 755))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 755) 186844) = 266555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b755_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 755)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 755)) 186844) = 266555 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o755 : xone 755 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a755_0 b755_0 a755_1 b755_1 a755_2 b755_2
    a755_3 b755_3 a755_4 b755_4 a755_5 b755_5

theorem a756_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 756))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 756) 0) = 200203 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b756_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 756)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 756)) 0) = 200203 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a756_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 756))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 756) 305530) = 26373 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b756_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 756)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 756)) 305530) = 26373 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a756_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 756))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 756) 5604) = 150238 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b756_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 756)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 756)) 5604) = 150238 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a756_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 756))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 756) 221549) = 175304 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b756_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 756)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 756)) 221549) = 175304 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a756_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 756))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 756) 266275) = 232428 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b756_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 756)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 756)) 266275) = 232428 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a756_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 756))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 756) 186844) = 115091 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b756_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 756)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 756)) 186844) = 115091 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o756 : xone 756 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a756_0 b756_0 a756_1 b756_1 a756_2 b756_2
    a756_3 b756_3 a756_4 b756_4 a756_5 b756_5

theorem a757_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 757))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 757) 0) = 26813 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b757_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 757)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 757)) 0) = 26813 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a757_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 757))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 757) 305530) = 95166 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b757_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 757)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 757)) 305530) = 95166 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a757_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 757))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 757) 5604) = 249556 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b757_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 757)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 757)) 5604) = 249556 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a757_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 757))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 757) 221549) = 125786 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b757_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 757)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 757)) 221549) = 125786 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a757_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 757))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 757) 266275) = 20218 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b757_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 757)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 757)) 266275) = 20218 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a757_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 757))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 757) 186844) = 31008 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b757_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 757)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 757)) 186844) = 31008 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o757 : xone 757 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a757_0 b757_0 a757_1 b757_1 a757_2 b757_2
    a757_3 b757_3 a757_4 b757_4 a757_5 b757_5

theorem a758_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 758))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 758) 0) = 140561 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b758_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 758)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 758)) 0) = 140561 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a758_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 758))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 758) 305530) = 240596 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b758_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 758)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 758)) 305530) = 240596 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a758_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 758))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 758) 5604) = 160019 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b758_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 758)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 758)) 5604) = 160019 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a758_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 758))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 758) 221549) = 134110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b758_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 758)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 758)) 221549) = 134110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a758_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 758))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 758) 266275) = 196519 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b758_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 758)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 758)) 266275) = 196519 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a758_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 758))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 758) 186844) = 196747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b758_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 758)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 758)) 186844) = 196747 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o758 : xone 758 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a758_0 b758_0 a758_1 b758_1 a758_2 b758_2
    a758_3 b758_3 a758_4 b758_4 a758_5 b758_5

theorem a759_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 759))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 759) 0) = 257233 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b759_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 759)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 759)) 0) = 257233 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a759_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 759))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 759) 305530) = 219372 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b759_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 759)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 759)) 305530) = 219372 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a759_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 759))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 759) 5604) = 82864 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b759_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 759)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 759)) 5604) = 82864 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a759_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 759))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 759) 221549) = 67979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b759_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 759)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 759)) 221549) = 67979 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a759_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 759))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 759) 266275) = 253495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b759_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 759)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 759)) 266275) = 253495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a759_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 759))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 759) 186844) = 29544 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b759_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 759)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 759)) 186844) = 29544 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o759 : xone 759 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a759_0 b759_0 a759_1 b759_1 a759_2 b759_2
    a759_3 b759_3 a759_4 b759_4 a759_5 b759_5

theorem a760_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 760))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 760) 0) = 172231 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b760_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 760)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 760)) 0) = 172231 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a760_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 760))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 760) 305530) = 75313 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b760_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 760)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 760)) 305530) = 75313 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a760_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 760))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 760) 5604) = 150897 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b760_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 760)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 760)) 5604) = 150897 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a760_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 760))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 760) 221549) = 46326 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b760_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 760)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 760)) 221549) = 46326 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a760_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 760))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 760) 266275) = 304917 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b760_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 760)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 760)) 266275) = 304917 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a760_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 760))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 760) 186844) = 178199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b760_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 760)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 760)) 186844) = 178199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o760 : xone 760 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a760_0 b760_0 a760_1 b760_1 a760_2 b760_2
    a760_3 b760_3 a760_4 b760_4 a760_5 b760_5

theorem a761_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 761))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 761) 0) = 114847 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b761_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 761)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 761)) 0) = 114847 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a761_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 761))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 761) 305530) = 59478 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b761_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 761)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 761)) 305530) = 59478 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a761_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 761))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 761) 5604) = 22411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b761_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 761)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 761)) 5604) = 22411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a761_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 761))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 761) 221549) = 154636 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b761_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 761)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 761)) 221549) = 154636 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a761_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 761))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 761) 266275) = 150061 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b761_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 761)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 761)) 266275) = 150061 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a761_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 761))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 761) 186844) = 206971 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b761_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 761)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 761)) 186844) = 206971 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o761 : xone 761 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a761_0 b761_0 a761_1 b761_1 a761_2 b761_2
    a761_3 b761_3 a761_4 b761_4 a761_5 b761_5

theorem a762_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 762))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 762) 0) = 235867 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b762_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 762)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 762)) 0) = 235867 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a762_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 762))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 762) 305530) = 257465 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b762_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 762)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 762)) 305530) = 257465 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a762_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 762))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 762) 5604) = 225249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b762_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 762)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 762)) 5604) = 225249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a762_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 762))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 762) 221549) = 129923 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b762_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 762)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 762)) 221549) = 129923 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a762_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 762))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 762) 266275) = 199442 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b762_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 762)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 762)) 266275) = 199442 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a762_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 762))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 762) 186844) = 12655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b762_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 762)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 762)) 186844) = 12655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o762 : xone 762 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a762_0 b762_0 a762_1 b762_1 a762_2 b762_2
    a762_3 b762_3 a762_4 b762_4 a762_5 b762_5

theorem a763_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 763))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 763) 0) = 283538 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b763_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 763)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 763)) 0) = 283538 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a763_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 763))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 763) 305530) = 176108 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b763_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 763)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 763)) 305530) = 176108 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a763_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 763))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 763) 5604) = 285702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b763_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 763)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 763)) 5604) = 285702 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a763_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 763))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 763) 221549) = 45303 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b763_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 763)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 763)) 221549) = 45303 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a763_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 763))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 763) 266275) = 295466 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b763_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 763)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 763)) 266275) = 295466 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a763_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 763))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 763) 186844) = 284066 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b763_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 763)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 763)) 186844) = 284066 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o763 : xone 763 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a763_0 b763_0 a763_1 b763_1 a763_2 b763_2
    a763_3 b763_3 a763_4 b763_4 a763_5 b763_5

theorem a764_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 764))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 764) 0) = 115168 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b764_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 764)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 764)) 0) = 115168 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a764_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 764))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 764) 305530) = 185884 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b764_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 764)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 764)) 305530) = 185884 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a764_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 764))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 764) 5604) = 266248 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b764_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 764)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 764)) 5604) = 266248 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a764_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 764))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 764) 221549) = 142237 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b764_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 764)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 764)) 221549) = 142237 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a764_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 764))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 764) 266275) = 177040 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b764_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 764)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 764)) 266275) = 177040 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a764_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 764))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 764) 186844) = 86015 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b764_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 764)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 764)) 186844) = 86015 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o764 : xone 764 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a764_0 b764_0 a764_1 b764_1 a764_2 b764_2
    a764_3 b764_3 a764_4 b764_4 a764_5 b764_5

theorem a765_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 765))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 765) 0) = 61741 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b765_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 765)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 765)) 0) = 61741 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a765_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 765))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 765) 305530) = 9768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b765_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 765)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 765)) 305530) = 9768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a765_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 765))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 765) 5604) = 267302 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b765_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 765)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 765)) 5604) = 267302 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a765_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 765))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 765) 221549) = 61469 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b765_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 765)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 765)) 221549) = 61469 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a765_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 765))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 765) 266275) = 294598 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b765_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 765)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 765)) 266275) = 294598 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a765_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 765))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 765) 186844) = 46764 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b765_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 765)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 765)) 186844) = 46764 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o765 : xone 765 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a765_0 b765_0 a765_1 b765_1 a765_2 b765_2
    a765_3 b765_3 a765_4 b765_4 a765_5 b765_5

theorem a766_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 766))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 766) 0) = 75533 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b766_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 766)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 766)) 0) = 75533 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a766_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 766))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 766) 305530) = 34703 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b766_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 766)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 766)) 305530) = 34703 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a766_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 766))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 766) 5604) = 51446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b766_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 766)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 766)) 5604) = 51446 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a766_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 766))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 766) 221549) = 249306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b766_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 766)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 766)) 221549) = 249306 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a766_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 766))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 766) 266275) = 252444 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b766_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 766)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 766)) 266275) = 252444 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a766_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 766))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 766) 186844) = 121588 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b766_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 766)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 766)) 186844) = 121588 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o766 : xone 766 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a766_0 b766_0 a766_1 b766_1 a766_2 b766_2
    a766_3 b766_3 a766_4 b766_4 a766_5 b766_5

theorem a767_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 767))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 767) 0) = 14408 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b767_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 767)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 767)) 0) = 14408 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a767_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 767))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 767) 305530) = 93190 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b767_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 767)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 767)) 305530) = 93190 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a767_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 767))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 767) 5604) = 186599 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b767_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 767)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 767)) 5604) = 186599 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a767_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 767))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 767) 221549) = 149341 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b767_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 767)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 767)) 221549) = 149341 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a767_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 767))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 767) 266275) = 51935 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b767_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 767)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 767)) 266275) = 51935 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a767_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 767))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 767) 186844) = 7852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b767_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 767)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 767)) 186844) = 7852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o767 : xone 767 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a767_0 b767_0 a767_1 b767_1 a767_2 b767_2
    a767_3 b767_3 a767_4 b767_4 a767_5 b767_5

theorem a768_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 768))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 768) 0) = 259586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b768_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 768)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 768)) 0) = 259586 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a768_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 768))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 768) 305530) = 195406 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b768_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 768)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 768)) 305530) = 195406 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a768_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 768))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 768) 5604) = 110598 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b768_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 768)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 768)) 5604) = 110598 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a768_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 768))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 768) 221549) = 162456 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b768_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 768)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 768)) 221549) = 162456 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a768_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 768))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 768) 266275) = 96812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b768_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 768)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 768)) 266275) = 96812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a768_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 768))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 768) 186844) = 254139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b768_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 768)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 768)) 186844) = 254139 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o768 : xone 768 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a768_0 b768_0 a768_1 b768_1 a768_2 b768_2
    a768_3 b768_3 a768_4 b768_4 a768_5 b768_5

theorem a769_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 769))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 769) 0) = 66409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b769_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 769)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 769)) 0) = 66409 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a769_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 769))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 769) 305530) = 215673 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b769_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 769)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 769)) 305530) = 215673 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a769_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 769))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 769) 5604) = 54238 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b769_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 769)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 769)) 5604) = 54238 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a769_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 769))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 769) 221549) = 118692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b769_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 769)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 769)) 221549) = 118692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a769_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 769))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 769) 266275) = 84790 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b769_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 769)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 769)) 266275) = 84790 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a769_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 769))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 769) 186844) = 296517 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b769_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 769)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 769)) 186844) = 296517 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o769 : xone 769 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a769_0 b769_0 a769_1 b769_1 a769_2 b769_2
    a769_3 b769_3 a769_4 b769_4 a769_5 b769_5

theorem a770_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 770))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 770) 0) = 30840 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b770_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 770)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 770)) 0) = 30840 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a770_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 770))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 770) 305530) = 230482 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b770_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 770)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 770)) 305530) = 230482 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a770_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 770))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 770) 5604) = 178135 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b770_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 770)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 770)) 5604) = 178135 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a770_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 770))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 770) 221549) = 213072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b770_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 770)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 770)) 221549) = 213072 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a770_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 770))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 770) 266275) = 233852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b770_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 770)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 770)) 266275) = 233852 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a770_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 770))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 770) 186844) = 123687 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b770_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 770)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 770)) 186844) = 123687 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o770 : xone 770 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a770_0 b770_0 a770_1 b770_1 a770_2 b770_2
    a770_3 b770_3 a770_4 b770_4 a770_5 b770_5

theorem a771_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 771))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 771) 0) = 207779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b771_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 771)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 771)) 0) = 207779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a771_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 771))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 771) 305530) = 283291 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b771_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 771)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 771)) 305530) = 283291 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a771_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 771))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 771) 5604) = 75164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b771_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 771)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 771)) 5604) = 75164 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a771_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 771))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 771) 221549) = 270472 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b771_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 771)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 771)) 221549) = 270472 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a771_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 771))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 771) 266275) = 17017 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b771_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 771)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 771)) 266275) = 17017 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a771_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 771))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 771) 186844) = 20801 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b771_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 771)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 771)) 186844) = 20801 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o771 : xone 771 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a771_0 b771_0 a771_1 b771_1 a771_2 b771_2
    a771_3 b771_3 a771_4 b771_4 a771_5 b771_5

theorem a772_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 772))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 772) 0) = 257814 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b772_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 772)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 772)) 0) = 257814 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a772_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 772))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 772) 305530) = 112108 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b772_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 772)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 772)) 305530) = 112108 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a772_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 772))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 772) 5604) = 198560 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b772_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 772)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 772)) 5604) = 198560 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a772_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 772))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 772) 221549) = 60332 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b772_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 772)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 772)) 221549) = 60332 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a772_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 772))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 772) 266275) = 95475 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b772_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 772)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 772)) 266275) = 95475 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a772_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 772))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 772) 186844) = 126199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b772_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 772)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 772)) 186844) = 126199 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o772 : xone 772 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a772_0 b772_0 a772_1 b772_1 a772_2 b772_2
    a772_3 b772_3 a772_4 b772_4 a772_5 b772_5

theorem a773_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 773))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 773) 0) = 49660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b773_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 773)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 773)) 0) = 49660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a773_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 773))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 773) 305530) = 161760 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b773_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 773)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 773)) 305530) = 161760 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a773_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 773))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 773) 5604) = 177244 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b773_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 773)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 773)) 5604) = 177244 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a773_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 773))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 773) 221549) = 42348 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b773_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 773)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 773)) 221549) = 42348 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a773_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 773))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 773) 266275) = 159707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b773_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 773)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 773)) 266275) = 159707 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a773_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 773))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 773) 186844) = 196989 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b773_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 773)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 773)) 186844) = 196989 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o773 : xone 773 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a773_0 b773_0 a773_1 b773_1 a773_2 b773_2
    a773_3 b773_3 a773_4 b773_4 a773_5 b773_5

theorem a774_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 774))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 774) 0) = 71108 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b774_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 774)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 774)) 0) = 71108 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a774_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 774))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 774) 305530) = 288004 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b774_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 774)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 774)) 305530) = 288004 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a774_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 774))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 774) 5604) = 33764 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b774_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 774)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 774)) 5604) = 33764 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a774_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 774))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 774) 221549) = 17070 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b774_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 774)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 774)) 221549) = 17070 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a774_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 774))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 774) 266275) = 224561 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b774_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 774)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 774)) 266275) = 224561 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a774_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 774))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 774) 186844) = 284241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b774_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 774)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 774)) 186844) = 284241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o774 : xone 774 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a774_0 b774_0 a774_1 b774_1 a774_2 b774_2
    a774_3 b774_3 a774_4 b774_4 a774_5 b774_5

theorem a775_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 775))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 775) 0) = 287627 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b775_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 775)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 775)) 0) = 287627 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a775_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 775))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 775) 305530) = 260797 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b775_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 775)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 775)) 305530) = 260797 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a775_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 775))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 775) 5604) = 138011 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b775_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 775)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 775)) 5604) = 138011 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a775_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 775))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 775) 221549) = 47470 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b775_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 775)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 775)) 221549) = 47470 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a775_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 775))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 775) 266275) = 71959 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b775_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 775)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 775)) 266275) = 71959 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a775_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 775))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 775) 186844) = 238798 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b775_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 775)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 775)) 186844) = 238798 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o775 : xone 775 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a775_0 b775_0 a775_1 b775_1 a775_2 b775_2
    a775_3 b775_3 a775_4 b775_4 a775_5 b775_5

theorem a776_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 776))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 776) 0) = 277451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b776_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 776)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 776)) 0) = 277451 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a776_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 776))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 776) 305530) = 50812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b776_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 776)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 776)) 305530) = 50812 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a776_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 776))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 776) 5604) = 181874 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b776_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 776)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 776)) 5604) = 181874 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a776_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 776))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 776) 221549) = 280213 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b776_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 776)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 776)) 221549) = 280213 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a776_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 776))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 776) 266275) = 296133 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b776_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 776)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 776)) 266275) = 296133 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a776_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 776))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 776) 186844) = 243761 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b776_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 776)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 776)) 186844) = 243761 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o776 : xone 776 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a776_0 b776_0 a776_1 b776_1 a776_2 b776_2
    a776_3 b776_3 a776_4 b776_4 a776_5 b776_5

theorem a777_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 777))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 777) 0) = 196003 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b777_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 777)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 777)) 0) = 196003 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a777_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 777))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 777) 305530) = 3353 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b777_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 777)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 777)) 305530) = 3353 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a777_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 777))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 777) 5604) = 139530 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b777_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 777)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 777)) 5604) = 139530 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a777_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 777))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 777) 221549) = 156082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b777_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 777)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 777)) 221549) = 156082 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a777_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 777))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 777) 266275) = 172660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b777_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 777)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 777)) 266275) = 172660 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a777_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 777))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 777) 186844) = 226183 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b777_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 777)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 777)) 186844) = 226183 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o777 : xone 777 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a777_0 b777_0 a777_1 b777_1 a777_2 b777_2
    a777_3 b777_3 a777_4 b777_4 a777_5 b777_5

theorem a778_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 778))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 778) 0) = 180649 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b778_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 778)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 778)) 0) = 180649 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a778_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 778))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 778) 305530) = 77039 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b778_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 778)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 778)) 305530) = 77039 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a778_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 778))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 778) 5604) = 34695 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b778_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 778)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 778)) 5604) = 34695 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a778_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 778))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 778) 221549) = 127319 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b778_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 778)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 778)) 221549) = 127319 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a778_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 778))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 778) 266275) = 164993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b778_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 778)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 778)) 266275) = 164993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a778_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 778))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 778) 186844) = 235944 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b778_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 778)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 778)) 186844) = 235944 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o778 : xone 778 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a778_0 b778_0 a778_1 b778_1 a778_2 b778_2
    a778_3 b778_3 a778_4 b778_4 a778_5 b778_5

theorem a779_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 779))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 779) 0) = 288482 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b779_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 779)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 779)) 0) = 288482 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a779_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 779))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 779) 305530) = 144566 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b779_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 779)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 779)) 305530) = 144566 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a779_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 779))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 779) 5604) = 116870 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b779_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 779)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 779)) 5604) = 116870 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a779_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 779))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 779) 221549) = 219248 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b779_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 779)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 779)) 221549) = 219248 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a779_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 779))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 779) 266275) = 106836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b779_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 779)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 779)) 266275) = 106836 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a779_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 779))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 779) 186844) = 256216 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b779_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 779)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 779)) 186844) = 256216 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o779 : xone 779 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a779_0 b779_0 a779_1 b779_1 a779_2 b779_2
    a779_3 b779_3 a779_4 b779_4 a779_5 b779_5

theorem a780_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 780))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 780) 0) = 221321 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b780_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 780)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 780)) 0) = 221321 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a780_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 780))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 780) 305530) = 226573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b780_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 780)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 780)) 305530) = 226573 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a780_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 780))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 780) 5604) = 267280 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b780_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 780)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 780)) 5604) = 267280 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a780_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 780))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 780) 221549) = 301198 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b780_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 780)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 780)) 221549) = 301198 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a780_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 780))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 780) 266275) = 9074 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b780_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 780)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 780)) 266275) = 9074 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a780_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 780))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 780) 186844) = 27189 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b780_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 780)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 780)) 186844) = 27189 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o780 : xone 780 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a780_0 b780_0 a780_1 b780_1 a780_2 b780_2
    a780_3 b780_3 a780_4 b780_4 a780_5 b780_5

theorem a781_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 781))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 781) 0) = 257051 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b781_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 781)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 781)) 0) = 257051 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a781_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 781))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 781) 305530) = 25715 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b781_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 781)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 781)) 305530) = 25715 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a781_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 781))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 781) 5604) = 132379 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b781_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 781)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 781)) 5604) = 132379 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a781_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 781))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 781) 221549) = 102863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b781_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 781)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 781)) 221549) = 102863 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a781_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 781))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 781) 266275) = 140631 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b781_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 781)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 781)) 266275) = 140631 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a781_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 781))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 781) 186844) = 240307 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b781_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 781)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 781)) 186844) = 240307 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o781 : xone 781 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a781_0 b781_0 a781_1 b781_1 a781_2 b781_2
    a781_3 b781_3 a781_4 b781_4 a781_5 b781_5

theorem a782_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 782))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 782) 0) = 247986 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b782_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 782)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 782)) 0) = 247986 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a782_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 782))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 782) 305530) = 210133 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b782_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 782)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 782)) 305530) = 210133 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a782_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 782))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 782) 5604) = 149041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b782_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 782)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 782)) 5604) = 149041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a782_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 782))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 782) 221549) = 265553 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b782_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 782)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 782)) 221549) = 265553 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a782_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 782))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 782) 266275) = 120854 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b782_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 782)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 782)) 266275) = 120854 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a782_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 782))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 782) 186844) = 16459 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b782_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 782)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 782)) 186844) = 16459 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o782 : xone 782 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a782_0 b782_0 a782_1 b782_1 a782_2 b782_2
    a782_3 b782_3 a782_4 b782_4 a782_5 b782_5

theorem a783_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 783))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 783) 0) = 35367 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b783_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 783)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 783)) 0) = 35367 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a783_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 783))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 783) 305530) = 57464 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b783_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 783)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 783)) 305530) = 57464 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a783_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 783))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 783) 5604) = 9799 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b783_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 783)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 783)) 5604) = 9799 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a783_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 783))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 783) 221549) = 241327 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b783_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 783)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 783)) 221549) = 241327 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a783_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 783))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 783) 266275) = 200803 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b783_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 783)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 783)) 266275) = 200803 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a783_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 783))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 783) 186844) = 200997 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b783_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 783)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 783)) 186844) = 200997 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o783 : xone 783 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a783_0 b783_0 a783_1 b783_1 a783_2 b783_2
    a783_3 b783_3 a783_4 b783_4 a783_5 b783_5

theorem a784_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 784))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 784) 0) = 40443 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b784_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 784)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 784)) 0) = 40443 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a784_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 784))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 784) 305530) = 232848 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b784_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 784)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 784)) 305530) = 232848 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a784_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 784))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 784) 5604) = 202454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b784_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 784)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 784)) 5604) = 202454 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a784_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 784))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 784) 221549) = 288123 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b784_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 784)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 784)) 221549) = 288123 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a784_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 784))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 784) 266275) = 178176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b784_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 784)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 784)) 266275) = 178176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a784_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 784))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 784) 186844) = 450 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b784_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 784)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 784)) 186844) = 450 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o784 : xone 784 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a784_0 b784_0 a784_1 b784_1 a784_2 b784_2
    a784_3 b784_3 a784_4 b784_4 a784_5 b784_5

theorem a785_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 785))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 785) 0) = 257421 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b785_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 785)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 785)) 0) = 257421 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a785_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 785))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 785) 305530) = 26772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b785_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 785)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 785)) 305530) = 26772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a785_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 785))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 785) 5604) = 194920 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b785_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 785)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 785)) 5604) = 194920 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a785_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 785))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 785) 221549) = 123010 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b785_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 785)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 785)) 221549) = 123010 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a785_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 785))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 785) 266275) = 79578 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b785_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 785)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 785)) 266275) = 79578 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a785_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 785))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 785) 186844) = 45051 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b785_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 785)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 785)) 186844) = 45051 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o785 : xone 785 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a785_0 b785_0 a785_1 b785_1 a785_2 b785_2
    a785_3 b785_3 a785_4 b785_4 a785_5 b785_5

theorem a786_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 786))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 786) 0) = 125369 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b786_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 786)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 786)) 0) = 125369 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a786_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 786))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 786) 305530) = 128127 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b786_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 786)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 786)) 305530) = 128127 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a786_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 786))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 786) 5604) = 291943 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b786_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 786)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 786)) 5604) = 291943 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a786_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 786))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 786) 221549) = 228964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b786_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 786)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 786)) 221549) = 228964 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a786_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 786))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 786) 266275) = 200183 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b786_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 786)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 786)) 266275) = 200183 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a786_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 786))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 786) 186844) = 173332 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b786_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 786)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 786)) 186844) = 173332 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o786 : xone 786 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a786_0 b786_0 a786_1 b786_1 a786_2 b786_2
    a786_3 b786_3 a786_4 b786_4 a786_5 b786_5

theorem a787_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 787))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 787) 0) = 175671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b787_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 787)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 787)) 0) = 175671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a787_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 787))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 787) 305530) = 12980 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b787_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 787)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 787)) 305530) = 12980 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a787_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 787))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 787) 5604) = 246251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b787_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 787)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 787)) 5604) = 246251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a787_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 787))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 787) 221549) = 172251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b787_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 787)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 787)) 221549) = 172251 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a787_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 787))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 787) 266275) = 251993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b787_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 787)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 787)) 266275) = 251993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a787_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 787))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 787) 186844) = 83691 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b787_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 787)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 787)) 186844) = 83691 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o787 : xone 787 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a787_0 b787_0 a787_1 b787_1 a787_2 b787_2
    a787_3 b787_3 a787_4 b787_4 a787_5 b787_5

theorem a788_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 788))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 788) 0) = 153012 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b788_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 788)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 788)) 0) = 153012 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a788_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 788))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 788) 305530) = 152284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b788_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 788)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 788)) 305530) = 152284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a788_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 788))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 788) 5604) = 164183 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b788_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 788)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 788)) 5604) = 164183 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a788_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 788))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 788) 221549) = 70060 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b788_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 788)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 788)) 221549) = 70060 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a788_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 788))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 788) 266275) = 42033 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b788_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 788)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 788)) 266275) = 42033 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a788_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 788))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 788) 186844) = 156284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b788_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 788)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 788)) 186844) = 156284 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o788 : xone 788 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a788_0 b788_0 a788_1 b788_1 a788_2 b788_2
    a788_3 b788_3 a788_4 b788_4 a788_5 b788_5

theorem a789_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 789))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 789) 0) = 204060 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b789_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 789)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 789)) 0) = 204060 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a789_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 789))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 789) 305530) = 220910 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b789_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 789)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 789)) 305530) = 220910 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a789_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 789))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 789) 5604) = 164046 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b789_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 789)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 789)) 5604) = 164046 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a789_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 789))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 789) 221549) = 242220 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b789_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 789)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 789)) 221549) = 242220 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a789_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 789))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 789) 266275) = 199043 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b789_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 789)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 789)) 266275) = 199043 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a789_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 789))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 789) 186844) = 143166 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b789_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 789)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 789)) 186844) = 143166 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o789 : xone 789 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a789_0 b789_0 a789_1 b789_1 a789_2 b789_2
    a789_3 b789_3 a789_4 b789_4 a789_5 b789_5

theorem a790_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 790))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 790) 0) = 58027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b790_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 790)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 790)) 0) = 58027 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a790_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 790))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 790) 305530) = 290055 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b790_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 790)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 790)) 305530) = 290055 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a790_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 790))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 790) 5604) = 197301 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b790_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 790)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 790)) 5604) = 197301 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a790_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 790))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 790) 221549) = 118671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b790_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 790)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 790)) 221549) = 118671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a790_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 790))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 790) 266275) = 131492 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b790_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 790)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 790)) 266275) = 131492 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a790_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 790))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 790) 186844) = 66012 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b790_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 790)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 790)) 186844) = 66012 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o790 : xone 790 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a790_0 b790_0 a790_1 b790_1 a790_2 b790_2
    a790_3 b790_3 a790_4 b790_4 a790_5 b790_5

theorem a791_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 791))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 791) 0) = 15463 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b791_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 791)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 791)) 0) = 15463 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a791_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 791))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 791) 305530) = 162456 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b791_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 791)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 791)) 305530) = 162456 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a791_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 791))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 791) 5604) = 174337 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b791_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 791)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 791)) 5604) = 174337 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a791_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 791))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 791) 221549) = 98673 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b791_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 791)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 791)) 221549) = 98673 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a791_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 791))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 791) 266275) = 166122 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b791_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 791)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 791)) 266275) = 166122 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a791_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 791))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 791) 186844) = 88824 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b791_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 791)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 791)) 186844) = 88824 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o791 : xone 791 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a791_0 b791_0 a791_1 b791_1 a791_2 b791_2
    a791_3 b791_3 a791_4 b791_4 a791_5 b791_5

theorem a792_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 792))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 792) 0) = 243561 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b792_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 792)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 792)) 0) = 243561 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a792_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 792))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 792) 305530) = 279432 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b792_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 792)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 792)) 305530) = 279432 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a792_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 792))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 792) 5604) = 62148 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b792_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 792)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 792)) 5604) = 62148 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a792_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 792))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 792) 221549) = 78033 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b792_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 792)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 792)) 221549) = 78033 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a792_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 792))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 792) 266275) = 95761 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b792_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 792)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 792)) 266275) = 95761 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a792_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 792))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 792) 186844) = 139411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b792_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 792)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 792)) 186844) = 139411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o792 : xone 792 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a792_0 b792_0 a792_1 b792_1 a792_2 b792_2
    a792_3 b792_3 a792_4 b792_4 a792_5 b792_5

theorem a793_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 793))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 793) 0) = 5265 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b793_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 793)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 793)) 0) = 5265 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a793_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 793))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 793) 305530) = 5041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b793_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 793)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 793)) 305530) = 5041 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a793_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 793))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 793) 5604) = 70076 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b793_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 793)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 793)) 5604) = 70076 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a793_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 793))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 793) 221549) = 14197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b793_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 793)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 793)) 221549) = 14197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a793_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 793))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 793) 266275) = 56234 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b793_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 793)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 793)) 266275) = 56234 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a793_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 793))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 793) 186844) = 190138 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b793_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 793)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 793)) 186844) = 190138 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o793 : xone 793 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a793_0 b793_0 a793_1 b793_1 a793_2 b793_2
    a793_3 b793_3 a793_4 b793_4 a793_5 b793_5

theorem a794_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 794))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 794) 0) = 191099 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b794_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 794)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 794)) 0) = 191099 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a794_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 794))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 794) 305530) = 249124 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b794_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 794)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 794)) 305530) = 249124 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a794_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 794))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 794) 5604) = 171611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b794_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 794)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 794)) 5604) = 171611 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a794_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 794))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 794) 221549) = 158491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b794_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 794)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 794)) 221549) = 158491 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a794_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 794))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 794) 266275) = 73910 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b794_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 794)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 794)) 266275) = 73910 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a794_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 794))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 794) 186844) = 169359 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b794_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 794)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 794)) 186844) = 169359 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o794 : xone 794 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a794_0 b794_0 a794_1 b794_1 a794_2 b794_2
    a794_3 b794_3 a794_4 b794_4 a794_5 b794_5

theorem a795_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 795))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 795) 0) = 302664 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b795_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 795)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 795)) 0) = 302664 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a795_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 795))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 795) 305530) = 306671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b795_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 795)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 795)) 305530) = 306671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a795_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 795))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 795) 5604) = 297052 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b795_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 795)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 795)) 5604) = 297052 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a795_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 795))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 795) 221549) = 154501 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b795_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 795)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 795)) 221549) = 154501 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a795_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 795))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 795) 266275) = 66628 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b795_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 795)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 795)) 266275) = 66628 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a795_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 795))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 795) 186844) = 225467 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b795_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 795)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 795)) 186844) = 225467 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o795 : xone 795 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a795_0 b795_0 a795_1 b795_1 a795_2 b795_2
    a795_3 b795_3 a795_4 b795_4 a795_5 b795_5

theorem a796_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 796))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 796) 0) = 120309 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b796_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 796)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 796)) 0) = 120309 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a796_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 796))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 796) 305530) = 116408 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b796_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 796)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 796)) 305530) = 116408 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a796_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 796))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 796) 5604) = 201285 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b796_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 796)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 796)) 5604) = 201285 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a796_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 796))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 796) 221549) = 159856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b796_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 796)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 796)) 221549) = 159856 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a796_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 796))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 796) 266275) = 60143 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b796_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 796)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 796)) 266275) = 60143 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a796_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 796))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 796) 186844) = 225110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b796_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 796)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 796)) 186844) = 225110 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o796 : xone 796 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a796_0 b796_0 a796_1 b796_1 a796_2 b796_2
    a796_3 b796_3 a796_4 b796_4 a796_5 b796_5

theorem a797_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 797))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 797) 0) = 137848 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b797_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 797)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 797)) 0) = 137848 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a797_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 797))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 797) 305530) = 104331 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b797_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 797)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 797)) 305530) = 104331 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a797_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 797))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 797) 5604) = 7327 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b797_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 797)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 797)) 5604) = 7327 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a797_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 797))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 797) 221549) = 68255 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b797_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 797)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 797)) 221549) = 68255 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a797_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 797))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 797) 266275) = 31030 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b797_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 797)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 797)) 266275) = 31030 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a797_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 797))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 797) 186844) = 73539 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b797_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 797)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 797)) 186844) = 73539 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o797 : xone 797 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a797_0 b797_0 a797_1 b797_1 a797_2 b797_2
    a797_3 b797_3 a797_4 b797_4 a797_5 b797_5

theorem a798_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 798))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 798) 0) = 109111 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b798_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 798)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 798)) 0) = 109111 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a798_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 798))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 798) 305530) = 264197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b798_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 798)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 798)) 305530) = 264197 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a798_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 798))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 798) 5604) = 301845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b798_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 798)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 798)) 5604) = 301845 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a798_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 798))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 798) 221549) = 303955 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b798_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 798)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 798)) 221549) = 303955 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a798_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 798))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 798) 266275) = 190248 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b798_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 798)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 798)) 266275) = 190248 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a798_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 798))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 798) 186844) = 214093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b798_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 798)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 798)) 186844) = 214093 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o798 : xone 798 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a798_0 b798_0 a798_1 b798_1 a798_2 b798_2
    a798_3 b798_3 a798_4 b798_4 a798_5 b798_5

theorem a799_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 799))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 799) 0) = 136382 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b799_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 799)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 799)) 0) = 136382 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a799_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 799))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 799) 305530) = 78568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b799_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 799)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 799)) 305530) = 78568 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a799_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 799))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 799) 5604) = 87859 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b799_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 799)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 799)) 5604) = 87859 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a799_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 799))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 799) 221549) = 151606 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b799_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 799)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 799)) 221549) = 151606 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a799_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 799))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 799) 266275) = 28853 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b799_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 799)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 799)) 266275) = 28853 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a799_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 799))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 799) 186844) = 222274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b799_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 799)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 799)) 186844) = 222274 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o799 : xone 799 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a799_0 b799_0 a799_1 b799_1 a799_2 b799_2
    a799_3 b799_3 a799_4 b799_4 a799_5 b799_5

theorem a800_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 800))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 800) 0) = 261394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b800_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 800)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 800)) 0) = 261394 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a800_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 800))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 800) 305530) = 60867 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b800_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 800)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 800)) 305530) = 60867 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a800_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 800))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 800) 5604) = 19737 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b800_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 800)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 800)) 5604) = 19737 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a800_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 800))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 800) 221549) = 290508 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b800_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 800)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 800)) 221549) = 290508 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a800_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 800))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 800) 266275) = 90497 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b800_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 800)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 800)) 266275) = 90497 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a800_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 800))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 800) 186844) = 280689 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b800_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 800)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 800)) 186844) = 280689 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o800 : xone 800 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a800_0 b800_0 a800_1 b800_1 a800_2 b800_2
    a800_3 b800_3 a800_4 b800_4 a800_5 b800_5

theorem a801_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 801))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 801) 0) = 171418 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b801_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 801)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 801)) 0) = 171418 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a801_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 801))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 801) 305530) = 34385 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b801_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 801)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 801)) 305530) = 34385 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a801_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 801))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 801) 5604) = 93868 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b801_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 801)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 801)) 5604) = 93868 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a801_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 801))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 801) 221549) = 49564 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b801_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 801)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 801)) 221549) = 49564 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a801_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 801))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 801) 266275) = 48992 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b801_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 801)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 801)) 266275) = 48992 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a801_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 801))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 801) 186844) = 259835 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b801_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 801)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 801)) 186844) = 259835 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o801 : xone 801 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a801_0 b801_0 a801_1 b801_1 a801_2 b801_2
    a801_3 b801_3 a801_4 b801_4 a801_5 b801_5

theorem a802_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 802))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 802) 0) = 296951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b802_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 802)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 802)) 0) = 296951 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a802_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 802))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 802) 305530) = 212181 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b802_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 802)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 802)) 305530) = 212181 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a802_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 802))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 802) 5604) = 222609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b802_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 802)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 802)) 5604) = 222609 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a802_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 802))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 802) 221549) = 186438 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b802_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 802)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 802)) 221549) = 186438 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a802_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 802))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 802) 266275) = 34768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b802_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 802)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 802)) 266275) = 34768 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a802_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 802))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 802) 186844) = 243078 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b802_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 802)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 802)) 186844) = 243078 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o802 : xone 802 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a802_0 b802_0 a802_1 b802_1 a802_2 b802_2
    a802_3 b802_3 a802_4 b802_4 a802_5 b802_5

theorem a803_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 803))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 803) 0) = 301095 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b803_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 803)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 803)) 0) = 301095 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a803_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 803))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 803) 305530) = 258131 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b803_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 803)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 803)) 305530) = 258131 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a803_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 803))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 803) 5604) = 70324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b803_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 803)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 803)) 5604) = 70324 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a803_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 803))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 803) 221549) = 283495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b803_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 803)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 803)) 221549) = 283495 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a803_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 803))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 803) 266275) = 37286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b803_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 803)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 803)) 266275) = 37286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a803_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 803))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 803) 186844) = 141349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b803_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 803)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 803)) 186844) = 141349 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o803 : xone 803 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a803_0 b803_0 a803_1 b803_1 a803_2 b803_2
    a803_3 b803_3 a803_4 b803_4 a803_5 b803_5

theorem a804_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 804))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 804) 0) = 112756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b804_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 804)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 804)) 0) = 112756 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a804_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 804))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 804) 305530) = 56163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b804_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 804)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 804)) 305530) = 56163 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a804_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 804))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 804) 5604) = 135608 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b804_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 804)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 804)) 5604) = 135608 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a804_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 804))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 804) 221549) = 145286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b804_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 804)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 804)) 221549) = 145286 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a804_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 804))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 804) 266275) = 299620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b804_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 804)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 804)) 266275) = 299620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a804_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 804))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 804) 186844) = 89461 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b804_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 804)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 804)) 186844) = 89461 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o804 : xone 804 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a804_0 b804_0 a804_1 b804_1 a804_2 b804_2
    a804_3 b804_3 a804_4 b804_4 a804_5 b804_5

theorem a805_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 805))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 805) 0) = 176903 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b805_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 805)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 805)) 0) = 176903 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a805_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 805))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 805) 305530) = 154692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b805_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 805)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 805)) 305530) = 154692 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a805_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 805))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 805) 5604) = 262503 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b805_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 805)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 805)) 5604) = 262503 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a805_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 805))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 805) 221549) = 218732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b805_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 805)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 805)) 221549) = 218732 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a805_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 805))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 805) 266275) = 122811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b805_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 805)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 805)) 266275) = 122811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a805_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 805))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 805) 186844) = 73671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b805_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 805)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 805)) 186844) = 73671 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o805 : xone 805 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a805_0 b805_0 a805_1 b805_1 a805_2 b805_2
    a805_3 b805_3 a805_4 b805_4 a805_5 b805_5

theorem a806_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 806))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 806) 0) = 291209 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b806_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 806)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 806)) 0) = 291209 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a806_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 806))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 806) 305530) = 107026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b806_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 806)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 806)) 305530) = 107026 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a806_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 806))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 806) 5604) = 267779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b806_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 806)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 806)) 5604) = 267779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a806_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 806))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 806) 221549) = 128411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b806_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 806)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 806)) 221549) = 128411 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a806_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 806))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 806) 266275) = 125328 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b806_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 806)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 806)) 266275) = 125328 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a806_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 806))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 806) 186844) = 115772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b806_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 806)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 806)) 186844) = 115772 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o806 : xone 806 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a806_0 b806_0 a806_1 b806_1 a806_2 b806_2
    a806_3 b806_3 a806_4 b806_4 a806_5 b806_5

theorem a807_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 807))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 807) 0) = 282021 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b807_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 807)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 807)) 0) = 282021 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a807_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 807))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 807) 305530) = 60295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b807_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 807)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 807)) 305530) = 60295 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a807_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 807))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 807) 5604) = 106282 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b807_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 807)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 807)) 5604) = 106282 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a807_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 807))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 807) 221549) = 172873 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b807_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 807)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 807)) 221549) = 172873 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a807_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 807))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 807) 266275) = 102380 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b807_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 807)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 807)) 266275) = 102380 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a807_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 807))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 807) 186844) = 162890 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b807_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 807)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 807)) 186844) = 162890 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o807 : xone 807 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a807_0 b807_0 a807_1 b807_1 a807_2 b807_2
    a807_3 b807_3 a807_4 b807_4 a807_5 b807_5

theorem a808_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 808))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 808) 0) = 194824 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b808_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 808)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 808)) 0) = 194824 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a808_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 808))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 808) 305530) = 25675 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b808_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 808)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 808)) 305530) = 25675 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a808_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 808))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 808) 5604) = 67172 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b808_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 808)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 808)) 5604) = 67172 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a808_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 808))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 808) 221549) = 62697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b808_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 808)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 808)) 221549) = 62697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a808_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 808))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 808) 266275) = 72841 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b808_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 808)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 808)) 266275) = 72841 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a808_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 808))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 808) 186844) = 153403 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b808_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 808)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 808)) 186844) = 153403 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o808 : xone 808 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a808_0 b808_0 a808_1 b808_1 a808_2 b808_2
    a808_3 b808_3 a808_4 b808_4 a808_5 b808_5

theorem a809_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 809))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 809) 0) = 289250 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b809_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 809)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 809)) 0) = 289250 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a809_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 809))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 809) 305530) = 129150 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b809_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 809)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 809)) 305530) = 129150 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a809_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 809))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 809) 5604) = 80498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b809_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 809)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 809)) 5604) = 80498 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a809_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 809))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 809) 221549) = 195993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b809_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 809)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 809)) 221549) = 195993 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a809_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 809))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 809) 266275) = 64380 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b809_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 809)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 809)) 266275) = 64380 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a809_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 809))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 809) 186844) = 243769 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b809_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 809)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 809)) 186844) = 243769 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o809 : xone 809 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a809_0 b809_0 a809_1 b809_1 a809_2 b809_2
    a809_3 b809_3 a809_4 b809_4 a809_5 b809_5

theorem a810_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 810))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 810) 0) = 268585 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b810_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 810)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 810)) 0) = 268585 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a810_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 810))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 810) 305530) = 275338 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b810_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 810)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 810)) 305530) = 275338 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a810_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 810))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 810) 5604) = 155697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b810_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 810)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 810)) 5604) = 155697 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a810_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 810))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 810) 221549) = 19876 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b810_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 810)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 810)) 221549) = 19876 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a810_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 810))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 810) 266275) = 97063 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b810_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 810)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 810)) 266275) = 97063 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a810_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 810))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 810) 186844) = 100626 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b810_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 810)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 810)) 186844) = 100626 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o810 : xone 810 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a810_0 b810_0 a810_1 b810_1 a810_2 b810_2
    a810_3 b810_3 a810_4 b810_4 a810_5 b810_5

theorem a811_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 811))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 811) 0) = 276620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b811_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 811)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 811)) 0) = 276620 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a811_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 811))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 811) 305530) = 63633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b811_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 811)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 811)) 305530) = 63633 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a811_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 811))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 811) 5604) = 59748 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b811_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 811)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 811)) 5604) = 59748 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a811_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 811))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 811) 221549) = 72432 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b811_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 811)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 811)) 221549) = 72432 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a811_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 811))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 811) 266275) = 72655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b811_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 811)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 811)) 266275) = 72655 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a811_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 811))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 811) 186844) = 257978 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b811_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 811)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 811)) 186844) = 257978 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o811 : xone 811 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a811_0 b811_0 a811_1 b811_1 a811_2 b811_2
    a811_3 b811_3 a811_4 b811_4 a811_5 b811_5

theorem a812_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 812))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 812) 0) = 94210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b812_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 812)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 812)) 0) = 94210 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a812_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 812))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 812) 305530) = 152976 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b812_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 812)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 812)) 305530) = 152976 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a812_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 812))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 812) 5604) = 180649 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b812_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 812)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 812)) 5604) = 180649 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a812_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 812))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 812) 221549) = 305316 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b812_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 812)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 812)) 221549) = 305316 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a812_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 812))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 812) 266275) = 258771 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b812_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 812)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 812)) 266275) = 258771 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a812_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 812))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 812) 186844) = 299318 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b812_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 812)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 812)) 186844) = 299318 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o812 : xone 812 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a812_0 b812_0 a812_1 b812_1 a812_2 b812_2
    a812_3 b812_3 a812_4 b812_4 a812_5 b812_5

theorem a813_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 813))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 813) 0) = 265539 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b813_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 813)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 813)) 0) = 265539 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a813_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 813))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 813) 305530) = 26579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b813_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 813)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 813)) 305530) = 26579 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a813_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 813))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 813) 5604) = 113423 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b813_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 813)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 813)) 5604) = 113423 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a813_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 813))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 813) 221549) = 2540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b813_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 813)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 813)) 221549) = 2540 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a813_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 813))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 813) 266275) = 44414 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b813_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 813)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 813)) 266275) = 44414 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a813_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 813))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 813) 186844) = 109916 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b813_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 813)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 813)) 186844) = 109916 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o813 : xone 813 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a813_0 b813_0 a813_1 b813_1 a813_2 b813_2
    a813_3 b813_3 a813_4 b813_4 a813_5 b813_5

theorem a814_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 814))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 814) 0) = 12038 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b814_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 814)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 814)) 0) = 12038 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a814_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 814))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 814) 305530) = 85390 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b814_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 814)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 814)) 305530) = 85390 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a814_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 814))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 814) 5604) = 158462 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b814_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 814)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 814)) 5604) = 158462 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a814_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 814))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 814) 221549) = 66226 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b814_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 814)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 814)) 221549) = 66226 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a814_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 814))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 814) 266275) = 213013 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b814_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 814)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 814)) 266275) = 213013 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a814_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 814))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 814) 186844) = 217982 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b814_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 814)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 814)) 186844) = 217982 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o814 : xone 814 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a814_0 b814_0 a814_1 b814_1 a814_2 b814_2
    a814_3 b814_3 a814_4 b814_4 a814_5 b814_5

theorem a815_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 815))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 815) 0) = 65140 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b815_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 815)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 815)) 0) = 65140 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a815_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 815))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 815) 305530) = 183683 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b815_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 815)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 815)) 305530) = 183683 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a815_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 815))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 815) 5604) = 207381 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b815_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 815)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 815)) 5604) = 207381 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a815_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 815))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 815) 221549) = 103009 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b815_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 815)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 815)) 221549) = 103009 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a815_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 815))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 815) 266275) = 265203 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b815_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 815)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 815)) 266275) = 265203 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a815_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 815))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 815) 186844) = 6811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b815_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 815)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 815)) 186844) = 6811 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o815 : xone 815 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a815_0 b815_0 a815_1 b815_1 a815_2 b815_2
    a815_3 b815_3 a815_4 b815_4 a815_5 b815_5

theorem a816_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 816))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 816) 0) = 53296 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b816_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 816)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 816)) 0) = 53296 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a816_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 816))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 816) 305530) = 155810 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b816_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 816)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 816)) 305530) = 155810 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a816_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 816))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 816) 5604) = 116021 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b816_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 816)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 816)) 5604) = 116021 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a816_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 816))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 816) 221549) = 89681 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b816_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 816)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 816)) 221549) = 89681 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a816_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 816))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 816) 266275) = 121276 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b816_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 816)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 816)) 266275) = 121276 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a816_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 816))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 816) 186844) = 76127 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b816_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 816)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 816)) 186844) = 76127 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o816 : xone 816 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a816_0 b816_0 a816_1 b816_1 a816_2 b816_2
    a816_3 b816_3 a816_4 b816_4 a816_5 b816_5

theorem a817_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 817))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 817) 0) = 177558 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b817_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 817)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 817)) 0) = 177558 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a817_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 817))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 817) 305530) = 299514 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b817_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 817)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 817)) 305530) = 299514 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a817_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 817))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 817) 5604) = 297405 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b817_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 817)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 817)) 5604) = 297405 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a817_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 817))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 817) 221549) = 164249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b817_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 817)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 817)) 221549) = 164249 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a817_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 817))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 817) 266275) = 68429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b817_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 817)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 817)) 266275) = 68429 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a817_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 817))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 817) 186844) = 15006 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b817_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 817)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 817)) 186844) = 15006 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o817 : xone 817 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a817_0 b817_0 a817_1 b817_1 a817_2 b817_2
    a817_3 b817_3 a817_4 b817_4 a817_5 b817_5

theorem a818_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 818))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 818) 0) = 304479 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b818_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 818)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 818)) 0) = 304479 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a818_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 818))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 818) 305530) = 180263 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b818_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 818)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 818)) 305530) = 180263 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a818_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 818))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 818) 5604) = 206039 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b818_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 818)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 818)) 5604) = 206039 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a818_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 818))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 818) 221549) = 94057 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b818_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 818)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 818)) 221549) = 94057 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a818_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 818))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 818) 266275) = 297049 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b818_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 818)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 818)) 266275) = 297049 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a818_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 818))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 818) 186844) = 38963 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b818_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 818)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 818)) 186844) = 38963 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o818 : xone 818 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a818_0 b818_0 a818_1 b818_1 a818_2 b818_2
    a818_3 b818_3 a818_4 b818_4 a818_5 b818_5

theorem a819_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 819))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 819) 0) = 292501 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b819_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 819)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 819)) 0) = 292501 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a819_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 819))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 819) 305530) = 23712 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b819_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 819)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 819)) 305530) = 23712 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a819_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 819))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 819) 5604) = 37031 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b819_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 819)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 819)) 5604) = 37031 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a819_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 819))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 819) 221549) = 148958 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b819_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 819)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 819)) 221549) = 148958 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a819_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 819))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 819) 266275) = 148779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b819_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 819)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 819)) 266275) = 148779 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a819_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 819))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 819) 186844) = 38991 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b819_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 819)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 819)) 186844) = 38991 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o819 : xone 819 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a819_0 b819_0 a819_1 b819_1 a819_2 b819_2
    a819_3 b819_3 a819_4 b819_4 a819_5 b819_5

theorem a820_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 820))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 820) 0) = 277941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b820_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 820)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 820)) 0) = 277941 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a820_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 820))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 820) 305530) = 273663 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b820_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 820)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 820)) 305530) = 273663 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a820_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 820))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 820) 5604) = 118948 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b820_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 820)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 820)) 5604) = 118948 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a820_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 820))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 820) 221549) = 230488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b820_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 820)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 820)) 221549) = 230488 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a820_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 820))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 820) 266275) = 198946 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b820_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 820)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 820)) 266275) = 198946 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a820_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 820))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 820) 186844) = 37054 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b820_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 820)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 820)) 186844) = 37054 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o820 : xone 820 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a820_0 b820_0 a820_1 b820_1 a820_2 b820_2
    a820_3 b820_3 a820_4 b820_4 a820_5 b820_5

theorem a821_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 821))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 821) 0) = 292542 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b821_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 821)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 821)) 0) = 292542 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a821_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 821))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 821) 305530) = 63893 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b821_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 821)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 821)) 305530) = 63893 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a821_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 821))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 821) 5604) = 34278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b821_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 821)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 821)) 5604) = 34278 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a821_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 821))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 821) 221549) = 290668 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b821_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 821)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 821)) 221549) = 290668 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a821_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 821))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 821) 266275) = 31996 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b821_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 821)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 821)) 266275) = 31996 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a821_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 821))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 821) 186844) = 122962 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b821_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 821)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 821)) 186844) = 122962 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o821 : xone 821 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a821_0 b821_0 a821_1 b821_1 a821_2 b821_2
    a821_3 b821_3 a821_4 b821_4 a821_5 b821_5

theorem a822_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 822))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 822) 0) = 148657 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b822_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 822)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 822)) 0) = 148657 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a822_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 822))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 822) 305530) = 248994 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b822_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 822)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 822)) 305530) = 248994 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a822_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 822))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 822) 5604) = 12848 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b822_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 822)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 822)) 5604) = 12848 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a822_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 822))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 822) 221549) = 246455 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b822_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 822)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 822)) 221549) = 246455 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a822_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 822))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 822) 266275) = 218241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b822_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 822)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 822)) 266275) = 218241 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a822_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 822))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 822) 186844) = 303174 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b822_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 822)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 822)) 186844) = 303174 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o822 : xone 822 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a822_0 b822_0 a822_1 b822_1 a822_2 b822_2
    a822_3 b822_3 a822_4 b822_4 a822_5 b822_5

theorem a823_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 823))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 823) 0) = 37165 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b823_0 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 823)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 823)) 0) = 37165 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a823_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 823))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 823) 305530) = 261752 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b823_1 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 823)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 823)) 305530) = 261752 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a823_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 823))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 823) 5604) = 301918 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b823_2 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 823)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 823)) 5604) = 301918 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a823_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 823))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 823) 221549) = 218696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b823_3 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 823)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 823)) 221549) = 218696 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a823_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 823))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 823) 266275) = 257036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b823_4 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 823)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 823)) 266275) = 257036 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem a823_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.tw (nth J.tgt 823))
    (apP CFSG.KD.Fi24Net.letPT (nthL J.trans 823) 186844) = 185753 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem b823_5 : apP CFSG.KD.Fi24Net.letPT (nthL J.trans 823)
    (apP CFSG.KD.Fi24Pc.letPX (nwL (f32 J.RP 823)) 186844) = 185753 :=
  Nat.eq_of_beq_eq_true (by quickRfl)
theorem o823 : xone 823 = true :=
  xone_of (by quickRfl) (by quickRfl)
    a823_0 b823_0 a823_1 b823_1 a823_2 b823_2
    a823_3 b823_3 a823_4 b823_4 a823_5 b823_5

end CFSG.KD.Fi24Pc.Ck

public section

namespace CFSG.KD.Fi24Pc.Ck

theorem x78 : CFSG.KD.Fi24Pc.xck (nat_lit 78) = true :=
  xck_of o624 (by quickRfl) o625 (by quickRfl) o626 (by quickRfl) o627 (by quickRfl)
    o628 (by quickRfl) o629 (by quickRfl) o630 (by quickRfl) o631 (by quickRfl)

theorem x79 : CFSG.KD.Fi24Pc.xck (nat_lit 79) = true :=
  xck_of o632 (by quickRfl) o633 (by quickRfl) o634 (by quickRfl) o635 (by quickRfl)
    o636 (by quickRfl) o637 (by quickRfl) o638 (by quickRfl) o639 (by quickRfl)

theorem x80 : CFSG.KD.Fi24Pc.xck (nat_lit 80) = true :=
  xck_of o640 (by quickRfl) o641 (by quickRfl) o642 (by quickRfl) o643 (by quickRfl)
    o644 (by quickRfl) o645 (by quickRfl) o646 (by quickRfl) o647 (by quickRfl)

theorem x81 : CFSG.KD.Fi24Pc.xck (nat_lit 81) = true :=
  xck_of o648 (by quickRfl) o649 (by quickRfl) o650 (by quickRfl) o651 (by quickRfl)
    o652 (by quickRfl) o653 (by quickRfl) o654 (by quickRfl) o655 (by quickRfl)

theorem x82 : CFSG.KD.Fi24Pc.xck (nat_lit 82) = true :=
  xck_of o656 (by quickRfl) o657 (by quickRfl) o658 (by quickRfl) o659 (by quickRfl)
    o660 (by quickRfl) o661 (by quickRfl) o662 (by quickRfl) o663 (by quickRfl)

theorem x83 : CFSG.KD.Fi24Pc.xck (nat_lit 83) = true :=
  xck_of o664 (by quickRfl) o665 (by quickRfl) o666 (by quickRfl) o667 (by quickRfl)
    o668 (by quickRfl) o669 (by quickRfl) o670 (by quickRfl) o671 (by quickRfl)

theorem x84 : CFSG.KD.Fi24Pc.xck (nat_lit 84) = true :=
  xck_of o672 (by quickRfl) o673 (by quickRfl) o674 (by quickRfl) o675 (by quickRfl)
    o676 (by quickRfl) o677 (by quickRfl) o678 (by quickRfl) o679 (by quickRfl)

theorem x85 : CFSG.KD.Fi24Pc.xck (nat_lit 85) = true :=
  xck_of o680 (by quickRfl) o681 (by quickRfl) o682 (by quickRfl) o683 (by quickRfl)
    o684 (by quickRfl) o685 (by quickRfl) o686 (by quickRfl) o687 (by quickRfl)

theorem x86 : CFSG.KD.Fi24Pc.xck (nat_lit 86) = true :=
  xck_of o688 (by quickRfl) o689 (by quickRfl) o690 (by quickRfl) o691 (by quickRfl)
    o692 (by quickRfl) o693 (by quickRfl) o694 (by quickRfl) o695 (by quickRfl)

theorem x87 : CFSG.KD.Fi24Pc.xck (nat_lit 87) = true :=
  xck_of o696 (by quickRfl) o697 (by quickRfl) o698 (by quickRfl) o699 (by quickRfl)
    o700 (by quickRfl) o701 (by quickRfl) o702 (by quickRfl) o703 (by quickRfl)

theorem x88 : CFSG.KD.Fi24Pc.xck (nat_lit 88) = true :=
  xck_of o704 (by quickRfl) o705 (by quickRfl) o706 (by quickRfl) o707 (by quickRfl)
    o708 (by quickRfl) o709 (by quickRfl) o710 (by quickRfl) o711 (by quickRfl)

theorem x89 : CFSG.KD.Fi24Pc.xck (nat_lit 89) = true :=
  xck_of o712 (by quickRfl) o713 (by quickRfl) o714 (by quickRfl) o715 (by quickRfl)
    o716 (by quickRfl) o717 (by quickRfl) o718 (by quickRfl) o719 (by quickRfl)

theorem x90 : CFSG.KD.Fi24Pc.xck (nat_lit 90) = true :=
  xck_of o720 (by quickRfl) o721 (by quickRfl) o722 (by quickRfl) o723 (by quickRfl)
    o724 (by quickRfl) o725 (by quickRfl) o726 (by quickRfl) o727 (by quickRfl)

theorem x91 : CFSG.KD.Fi24Pc.xck (nat_lit 91) = true :=
  xck_of o728 (by quickRfl) o729 (by quickRfl) o730 (by quickRfl) o731 (by quickRfl)
    o732 (by quickRfl) o733 (by quickRfl) o734 (by quickRfl) o735 (by quickRfl)

theorem x92 : CFSG.KD.Fi24Pc.xck (nat_lit 92) = true :=
  xck_of o736 (by quickRfl) o737 (by quickRfl) o738 (by quickRfl) o739 (by quickRfl)
    o740 (by quickRfl) o741 (by quickRfl) o742 (by quickRfl) o743 (by quickRfl)

theorem x93 : CFSG.KD.Fi24Pc.xck (nat_lit 93) = true :=
  xck_of o744 (by quickRfl) o745 (by quickRfl) o746 (by quickRfl) o747 (by quickRfl)
    o748 (by quickRfl) o749 (by quickRfl) o750 (by quickRfl) o751 (by quickRfl)

theorem x94 : CFSG.KD.Fi24Pc.xck (nat_lit 94) = true :=
  xck_of o752 (by quickRfl) o753 (by quickRfl) o754 (by quickRfl) o755 (by quickRfl)
    o756 (by quickRfl) o757 (by quickRfl) o758 (by quickRfl) o759 (by quickRfl)

theorem x95 : CFSG.KD.Fi24Pc.xck (nat_lit 95) = true :=
  xck_of o760 (by quickRfl) o761 (by quickRfl) o762 (by quickRfl) o763 (by quickRfl)
    o764 (by quickRfl) o765 (by quickRfl) o766 (by quickRfl) o767 (by quickRfl)

theorem x96 : CFSG.KD.Fi24Pc.xck (nat_lit 96) = true :=
  xck_of o768 (by quickRfl) o769 (by quickRfl) o770 (by quickRfl) o771 (by quickRfl)
    o772 (by quickRfl) o773 (by quickRfl) o774 (by quickRfl) o775 (by quickRfl)

theorem x97 : CFSG.KD.Fi24Pc.xck (nat_lit 97) = true :=
  xck_of o776 (by quickRfl) o777 (by quickRfl) o778 (by quickRfl) o779 (by quickRfl)
    o780 (by quickRfl) o781 (by quickRfl) o782 (by quickRfl) o783 (by quickRfl)

theorem x98 : CFSG.KD.Fi24Pc.xck (nat_lit 98) = true :=
  xck_of o784 (by quickRfl) o785 (by quickRfl) o786 (by quickRfl) o787 (by quickRfl)
    o788 (by quickRfl) o789 (by quickRfl) o790 (by quickRfl) o791 (by quickRfl)

theorem x99 : CFSG.KD.Fi24Pc.xck (nat_lit 99) = true :=
  xck_of o792 (by quickRfl) o793 (by quickRfl) o794 (by quickRfl) o795 (by quickRfl)
    o796 (by quickRfl) o797 (by quickRfl) o798 (by quickRfl) o799 (by quickRfl)

theorem x100 : CFSG.KD.Fi24Pc.xck (nat_lit 100) = true :=
  xck_of o800 (by quickRfl) o801 (by quickRfl) o802 (by quickRfl) o803 (by quickRfl)
    o804 (by quickRfl) o805 (by quickRfl) o806 (by quickRfl) o807 (by quickRfl)

theorem x101 : CFSG.KD.Fi24Pc.xck (nat_lit 101) = true :=
  xck_of o808 (by quickRfl) o809 (by quickRfl) o810 (by quickRfl) o811 (by quickRfl)
    o812 (by quickRfl) o813 (by quickRfl) o814 (by quickRfl) o815 (by quickRfl)

theorem x102 : CFSG.KD.Fi24Pc.xck (nat_lit 102) = true :=
  xck_of o816 (by quickRfl) o817 (by quickRfl) o818 (by quickRfl) o819 (by quickRfl)
    o820 (by quickRfl) o821 (by quickRfl) o822 (by quickRfl) o823 (by quickRfl)

end CFSG.KD.Fi24Pc.Ck

end
