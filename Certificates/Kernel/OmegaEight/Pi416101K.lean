module

public import Certificates.Kernel.OmegaEight.Arr3009K
public import Certificates.Kernel.OmegaEight.Pi416101Chain
public import Certificates.Data.Kernel.J2Cover
public import Certificates.Data.O8PiQ8
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.KC.J2Cover CFSG.ClassicalInvolution.Q3.TL4.Z2W.O8Pi

@[expose] noncomputable def pg9 (X i : Nat) : Nat := pg 9 (mask 9) X i

@[expose] noncomputable def wPI (wd : List Int) : Nat :=
  wordK 360 9 (mask 9) (pidn 360 9) PI.S PI.SI wd

@[expose] noncomputable def piTK : List Nat :=
  [wPI [1, 2], wPI [3, 6], pc (pinv (wPI [1, 2])) (wPI [3, 6])]

@[expose] noncomputable def piTests : List (Nat × Nat) := piTK.map fun c => (c, pinv c)

@[expose] noncomputable def sqMovesK (X : Nat) : Bool :=
  (List.range 360).any fun i => pg9 X (pg9 X i) != i

@[expose] noncomputable def sqKeyK (X : Nat) : List Nat := imgs fun b => pg9 X (pg9 X b)

@[expose] noncomputable def q8ImgsK (x y : Nat) : List (List Nat) :=
  [imgs id, imgs (fun b => pg9 x (pg9 x b)), imgs (pg9 x), imgs (fun b => pg9 x (pg9 x (pg9 x b))),
    imgs (pg9 y), imgs (fun b => pg9 y (pg9 x (pg9 x b))), imgs (fun b => pg9 x (pg9 y b)),
    imgs (fun b => pg9 x (pg9 y (pg9 x (pg9 x b))))]

@[expose] noncomputable def conjImgK (c : Nat × Nat) (x : Nat) : List Nat :=
  imgs fun b => pg9 c.1 (pg9 x (pg9 c.2 b))

@[expose] noncomputable def movesBK (L : List (List Nat)) (x y : Nat) (c : Nat × Nat) : Bool :=
  !(L.contains (conjImgK c x) && L.contains (conjImgK c y))

@[expose] noncomputable def presBK (x y : Nat) : Bool :=
  baseN.all fun b => pg9 y (pg9 x b) == pg9 x (pg9 x (pg9 x (pg9 y b)))

@[expose] noncomputable def pairBK (tests : List (Nat × Nat)) (x y : Nat) : Bool :=
  !presBK x y || tests.all (movesBK (q8ImgsK x y) x y)

@[expose] noncomputable def piSq : List Nat := prodList 360 9 4 PI.LR PI.TR sqMovesK

@[expose] noncomputable def kNat (X : Nat) : Nat := (sqKeyK X).foldr (fun a acc => a + 512 * acc) 0

@[expose] noncomputable def keysK : List Nat := (piSq.map kNat).dedup

@[expose] noncomputable def q8Chunk (ks : List Nat) : Bool :=
  ks.all fun k =>
    let B := piSq.filter fun X => kNat X == k
    B.all fun x => B.all fun y => pairBK piTests x y

@[expose] noncomputable def q8Part (i : Nat) : Bool := q8Chunk (keysK.filter fun k => k % 8 == i)

theorem kGenPI : allN 4 (fun j => Nat.beq (PI.S j) (AP.S (piIdx.getD j 0))) = true := by quickRfl

theorem kTests : List.all piTK (fun c => bAnd(cn c, bAnd(pm c, cn (pinv c)))) = true := by
  quickRfl
end CertificateChecks.KernelO8

end
