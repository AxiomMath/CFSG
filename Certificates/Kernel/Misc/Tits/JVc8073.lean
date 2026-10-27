module

public import Certificates.Kernel.Misc.Tits.JTab8073
public import Certificates.Data.Kernel.SporSch.TitsEnum5
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsJT.V

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelMisc.TitsJT (Z C CI G GI)

@[expose] noncomputable def tr (k a : Nat) : Nat := trAt 1755 (1755 * 11) TitsJ.LR TitsJ.TR k a

@[expose] noncomputable def pt (g p : Nat) : Nat := pg 11 (mask 11) g p

@[expose] noncomputable def X (i p : Nat) : Nat :=
  gpt 11 (mask 11) (tr 0 (Nat.div i 256)) (tr 1 (Nat.mod (Nat.div i 128) 2))
    (tr 2 (Nat.mod (Nat.div i 2) 64)) (tr 3 (Nat.mod i 2)) (pidn 1755 11) p

@[expose] noncomputable def Pk (i : Nat) : Nat :=
  prod5K 1755 11 (mask 11) (tr 0 (Nat.div i 256)) (tr 1 (Nat.mod (Nat.div i 128) 2))
    (tr 2 (Nat.mod (Nat.div i 2) 64)) (tr 3 (Nat.mod i 2)) (pidn 1755 11)

@[expose] noncomputable def onB (f : Nat → Bool) : Bool := bAnd(f 5, bAnd(f 1, bAnd(f 24, f 12)))

@[expose] noncomputable def cm (i g : Nat) : Bool := onB fun p => Nat.beq (X i (pt g p)) (pt g (X i p))

@[expose] noncomputable def zc (i g : Nat) : Bool :=
  onB fun p => Nat.beq (X i (pt g p)) (pt Z (pt g (X i p)))

@[expose] noncomputable def Pb (i : Nat) : Bool :=
  allN 4 fun k => bIf(cm i (TitsJ.S k), true, zc i (TitsJ.S k))

@[expose] noncomputable def allc (i : Nat) : Bool := allN 4 fun k => cm i (TitsJ.S k)

@[expose] noncomputable def sq (i : Nat) : Bool := onB fun p => Nat.beq (X i (X i p)) p

@[expose] noncomputable def isOne (i : Nat) : Bool := onB fun p => Nat.beq (X i p) p

@[expose] noncomputable def isZ (i : Nat) : Bool := onB fun p => Nat.beq (X i p) (pt Z p)

@[expose] noncomputable def bI (m : Nat) : Nat :=
  nIf(Nat.beq m 0, 1, nIf(Nat.beq m 1, 2, nIf(Nat.beq m 2, 28, nIf(Nat.beq m 3, 30, 46))))

@[expose] noncomputable def Bc (j m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Pk (bI m))
    (fun _ ih => pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) C ih) CI) j

@[expose] noncomputable def pw (m : Nat) : Nat :=
  nIf(Nat.beq m 0, 1, nIf(Nat.beq m 1, 2, nIf(Nat.beq m 2, 4, nIf(Nat.beq m 3, 8, 16))))

@[expose] noncomputable def lb (j i m : Nat) : Nat := nIf(cm i (Bc j m), 0, pw m)

@[expose] noncomputable def lam (j i : Nat) : Nat :=
  Nat.add (lb j i 0) (Nat.add (lb j i 1) (Nat.add (lb j i 2) (Nat.add (lb j i 3) (lb j i 4))))

@[expose] noncomputable def memN (v : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a v, true, ih)) L

@[expose] noncomputable def xorL (v : Nat) (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun a _ ih => Nat.xor a v :: ih) L

@[expose] noncomputable def appL (L M : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) M (fun a _ ih => a :: ih) L

@[expose] noncomputable def spanF (vs : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun L => L)
    (fun v _ ih L => ih (appL L (xorL v L))) vs

@[expose] noncomputable def LAM : List Nat := [28, 12, 16, 0, 13, 29, 1, 17, 8, 24, 4, 20, 25, 9, 21, 5]

@[expose] noncomputable def cover (i : Nat) : Bool :=
  allL (fun v => memN v (spanF [lam 0 i, lam 4 i, lam 3 i, lam 2 i, lam 1 i] [0])) LAM

@[expose] noncomputable def test (i cl : Nat) : Bool :=
  bAnd(memN (lam 0 i) LAM,
    bIf(Pb i,
      bAnd(Nat.beq cl 0, bAnd(sq i, bAnd(Nat.beq (lam 0 i) 0,
        bIf(allc i, bIf(isOne i, true, isZ i), true)))),
      bAnd(bIf(Nat.beq cl 0, false, true), bAnd(bIf(Nat.beq (lam 0 i) 0, false, true),
        bAnd(bIf(Nat.beq (lam 4 i) (lam 0 i), false, true), bAnd(cover i,
          Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (sq i))
            (sq i) (Nat.beq cl 1)))))))

@[expose] noncomputable def EIX : List Nat := [0, 1, 2, 3, 28, 29, 30, 31, 34, 35, 46, 47, 60, 61,
  62, 63, 64, 65, 70, 71, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]

@[expose] noncomputable def wPt (w : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) p (fun k _ ih => pt (G k) ih) w

@[expose] noncomputable def wIPt (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p) (fun k _ ih p => ih (pt (GI k) p)) w

@[expose] noncomputable def wck (j : Nat) (w : List Nat) : Bool :=
  onB fun p => Nat.beq (wPt w (X 129 (wIPt w p))) (X j p)

@[expose] noncomputable def wAll (J : List Nat) (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun W => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) W)
    (fun j _ ih W => List.rec (motive := fun _ => Bool) false (fun w W' _ => bAnd(wck j w, ih W')) W)
    J W

@[expose] noncomputable def INV : List Nat := [129, 131, 157, 159, 163, 174, 189, 191, 193, 198, 244,
  246, 249, 250, 252, 254, 262, 263, 266, 267, 274, 275, 278, 279, 352, 353, 356, 357, 360, 361, 366,
  367, 385, 387, 393, 399, 405, 411, 412, 415, 416, 418, 421, 423, 424, 427, 428, 431, 432, 435, 437,
  438, 440, 443, 444, 447, 448, 451, 452, 455, 456, 459, 461, 463, 464, 466, 469, 472, 474, 477, 478,
  491, 492, 497, 500, 503, 505, 506, 509, 510]

@[expose] noncomputable def cls (i : Nat) : Nat := nIf(memN i EIX, 0, nIf(memN i INV, 1, 2))

@[expose] noncomputable def WD : List (List Nat) := [[], [0, 0, 1], [2, 0], [1, 2], [1, 2, 1, 2],
  [1, 1, 2, 0], [0, 2, 0, 0, 0], [1, 2, 0, 0, 1], [2, 0, 1, 2], [2, 0, 0, 1, 0], [1, 0, 0], [0, 1, 0],
  [0, 2, 0, 2], [1, 1], [1, 2, 1, 1], [0, 0, 2], [0, 2, 2, 0], [1, 0], [1, 0, 1, 1], [0, 0, 0],
  [2, 1, 0], [0, 2, 1, 2], [2, 2, 0, 1], [0, 1], [0, 2], [1, 0, 1, 2], [0, 1, 1, 2], [2, 0, 0, 0],
  [2, 0, 2], [2, 1, 0, 1, 2], [2, 0, 1], [1, 2, 2, 1], [1], [0, 0], [1, 0, 2, 1, 2], [1, 2, 0, 0, 0],
  [1, 1, 0], [0, 0, 1, 0], [2, 1, 1], [2], [2, 2], [0, 2, 2, 0, 0], [0, 2, 0, 0], [1, 2, 2],
  [1, 1, 2, 2], [2, 0, 0], [0, 1, 2, 1], [0, 0, 0, 1, 0], [2, 2, 1, 1], [2, 2, 2, 0], [1, 2, 1],
  [2, 1], [0, 2, 2, 1, 1], [1, 0, 2, 0, 0], [2, 1, 0, 0], [2, 0, 0, 1], [0, 2, 2, 1], [0, 2, 1],
  [2, 0, 2, 2, 1], [2, 1, 2], [0, 0, 2, 1], [1, 2, 0, 0], [0, 1, 0, 0], [0, 1, 2], [2, 2, 0, 0],
  [2, 1, 2, 1], [1, 0, 1], [0], [1, 0, 0, 0], [2, 2, 1], [0, 1, 1], [2, 1, 2, 0, 0], [1, 0, 2, 2, 0],
  [0, 0, 0, 1], [1, 1, 0, 0], [1, 2, 0], [1, 1, 2], [2, 2, 0], [0, 1, 1, 0], [2, 0, 0, 2]]

theorem lvK : bAnd(Nat.beq (rcnt (TitsJ.LR 0)) 2, bAnd(Nat.beq (rcnt (TitsJ.LR 1)) 2,
    bAnd(Nat.beq (rcnt (TitsJ.LR 2)) 64, Nat.beq (rcnt (TitsJ.LR 3)) 2))) = true := by quickRfl

theorem zK : bAnd(allN 4 (fun k => Nat.beq (pcomp 1755 11 (mask 11) Z (TitsJ.S k))
      (pcomp 1755 11 (mask 11) (TitsJ.S k) Z)),
    bAnd(Nat.beq (pcomp 1755 11 (mask 11) Z Z) (pidn 1755 11),
      bIf(Nat.beq Z (pidn 1755 11), false, true))) = true := by quickRfl

theorem canB : allN 5 (fun j => allN 5 (fun m => canonK 1755 11 (mask 11) (1755 * 11) (Bc j m))) =
    true := by quickRfl

theorem enumK : allN 512 (fun i => test i (cls i)) = true := by quickRfl

theorem wordsK : wAll INV WD = true := by quickRfl

end CertificateChecks.KernelMisc.TitsJT.V

end
