module

public import Certificates.Kernel.Sporadic.Tits.Sift2264
public import Certificates.Kernel.SporSch.Tits.Common
public import Certificates.Kernel.SporSch.Tits.Action2262
public import Certificates.Kernel.Misc.Tits.Pi7092
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.Join
public import Certificates.Data.RuTypeJ47Inputs
meta import Certificates.Data.RuTypeJ47Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#ks_chars CertificateChecks.KernelMisc.J47T CFSG.Quasithin.RuType.J47.j47Text

#kmisc_hexflat CertificateChecks.KernelMisc.J47T CFSG.Quasithin.RuType.J47.j47Text 3 1755 11 7

namespace CertificateChecks.KernelMisc.TitsJ47

open CFSG.Quasithin.RuType.J47 CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native

meta def witM : Array (Array Nat) :=
  let ws := (List.range 1755).toArray.map fun q => Id.run do
    let mut r := (0, 0)
    for v in ptLineBuckets[q]! do
      for k in [0:3] do
        for w in ptLineBuckets[titsLinePtArr[3 * v + k]!]! do
          for k' in [0:3] do
            if uArr[titsLinePtArr[3 * w + k']!]! != titsLinePtArr[3 * w + k']! then
              r := (v, 16 * w + 4 * k + k')
    return r
  #[ws.map (·.1), ws.map (·.2)]

end CertificateChecks.KernelMisc.TitsJ47

#kmisc_packarrs CertificateChecks.KernelMisc.J47W CertificateChecks.KernelMisc.TitsJ47.witM 16

namespace CertificateChecks.KernelMisc.TitsJ47

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Join
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsAction CertificateChecks.KernelMisc

theorem j47_join : joinK 1 (11 * 1755) J47T.F J47T.F 7 = true := by
  quickRfl

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def pi (p : Nat) : Nat := pinvS 1755 11 (mask 11) p

@[expose] noncomputable def pt (P i : Nat) : Nat := pg 11 (mask 11) P i

@[expose] noncomputable def X (k : Nat) : Nat := J47T.F k

@[expose] noncomputable def cj (g x : Nat) : Nat := pc (pc g x) (pi g)
@[expose] noncomputable def cji (g x : Nat) : Nat := pc (pc (pi g) x) g

@[expose] noncomputable def jK : Nat := cj (X 0) (X 2)
@[expose] noncomputable def v1K : Nat := cji (X 0) TitsZ
@[expose] noncomputable def v2K : Nat := cj (X 2) v1K
@[expose] noncomputable def uK : Nat := cj (X 0) v2K
@[expose] noncomputable def tK : Nat := pc uK TitsZ
@[expose] noncomputable def zpK : Nat := cji (X 1) v1K
@[expose] noncomputable def jpK : Nat := cji (X 1) (X 2)
@[expose] noncomputable def w1K : Nat := cji (X 0) tK
@[expose] noncomputable def tpK : Nat := cji (X 1) w1K

@[expose] noncomputable def powK (x : Nat) : Nat → Nat
  | 0 => pidn 1755 11
  | k + 1 => pc x (powK x k)

@[expose] noncomputable def prodIK (p : Nat) : Nat := pc (powK (X 5) (p / 4)) (powK (X 6) (p % 4))

@[expose] noncomputable def onLineK (p v : Nat) : Bool :=
  Nat.beq (lpK (3 * v)) p || Nat.beq (lpK (3 * v + 1)) p || Nat.beq (lpK (3 * v + 2)) p

@[expose] noncomputable def lineFixedK (P v : Nat) : Bool :=
  (List.range 3).all fun k =>
    Nat.beq (pt P (lpK (3 * v + k))) (lpK (3 * v)) ||
      Nat.beq (pt P (lpK (3 * v + k))) (lpK (3 * v + 1)) ||
      Nat.beq (pt P (lpK (3 * v + k))) (lpK (3 * v + 2))

@[expose] noncomputable def lineMapsK (P v w : Nat) : Bool :=
  (List.range 3).all fun k => onLineK (pt P (lpK (3 * v + k))) w

@[expose] noncomputable def inSK (P : Nat) : Bool := Nat.beq (pt P 0) 0 && lineFixedK P 0

theorem perms : allN 7 (fun k => permC (X k)) = true ∧ permC TitsZ = true ∧
    permC TitsPi.P = true := by
  refine ⟨?_, ?_, ?_⟩ <;> quickRfl

@[expose] noncomputable def sx (k : Nat) : Nat :=
  nIf(Nat.beq k 0, pc (X 0) (GI 1), nIf(Nat.beq k 5, pc (X 5) (GI 1), X k))

theorem sifts : allN 7 (fun k => bAnd(siftD (sx k), permC (sx k))) = true := by
  quickRfl

theorem sift_neg : siftD (X 0) = false := by
  decide +kernel

@[expose] noncomputable def idK : Nat := pidn 1755 11

theorem canon : allN 9 (fun k => canonK 1755 11 (mask 11) (1755 * 11)
    (nIf(Nat.beq k 0, jK, nIf(Nat.beq k 1, v1K, nIf(Nat.beq k 2, v2K, nIf(Nat.beq k 3, uK,
    nIf(Nat.beq k 4, tK, nIf(Nat.beq k 5, zpK, nIf(Nat.beq k 6, jpK, nIf(Nat.beq k 7, w1K,
    tpK)))))))))) = true := by
  quickRfl

@[expose] noncomputable def letK : Bool :=
  Nat.beq (pt TitsPi.P 0) 0 && lineFixedK TitsPi.P 0 && Nat.beq (pt (X 0) 0) 1 &&
    lineFixedK (X 0) 0 && Nat.beq (pt (X 1) 0) 0 && Nat.beq (pt (X 2) 0) 0 &&
    Nat.beq (pc (X 2) (X 2)) idK && lineMapsK (pc (X 0) (X 2)) 0 5 && Nat.beq (pt jK 0) 10 &&
    lineFixedK (X 3) 0 && Nat.beq (pt (X 4) 0) 0 && Nat.beq (pt (X 5) 0) 0 &&
    Nat.beq (pt (X 6) 0) 0

@[expose] noncomputable def chainK : Bool :=
  [TitsZ, v1K, v2K, uK, zpK, jpK, tK, w1K, tpK].all inSK

@[expose] noncomputable def uChK : Bool :=
  !(Nat.beq uK TitsZ) && Nat.beq (pc uK TitsZ) (pc TitsZ uK) && Nat.beq (powK (X 4) 5) idK &&
    !(Nat.beq (X 4) idK) && Nat.beq (pc (pc uK (X 4)) uK) (powK (X 4) 4)

@[expose] noncomputable def normBK (g : Nat) : Bool :=
  (List.range 5).any fun k => Nat.beq (cj g (X 4)) (powK (X 4) k)

@[expose] noncomputable def iK : Bool :=
  Nat.beq (pc (X 5) (X 6)) (pc (X 6) (X 5)) && Nat.beq (pc (X 5) uK) (pc uK (X 5)) &&
    Nat.beq (pc (X 6) uK) (pc uK (X 6)) && normBK (X 5) && normBK (X 6) &&
    (allN 16 fun p => allN 16 fun q => p == q || !(Nat.beq (prodIK p) (prodIK q))) &&
    allN 16 fun p => !(Nat.beq (pc (prodIK p) (prodIK p)) idK) || Nat.beq (prodIK p) idK ||
      Nat.beq (prodIK p) TitsZ || Nat.beq (prodIK p) uK || Nat.beq (prodIK p) tK

theorem canonI : allN 16 (fun p => canonK 1755 11 (mask 11) (1755 * 11) (prodIK p)) = true ∧
    allN 6 (fun k => canonK 1755 11 (mask 11) (1755 * 11) (powK (X 4) k)) = true ∧
    allN 4 (fun k => canonK 1755 11 (mask 11) (1755 * 11) (powK (X 3) k)) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> quickRfl

@[expose] noncomputable def fixK : Bool :=
  Nat.beq ((List.range 1755).countP fun x => Nat.beq (pt uK x) x) 91 &&
    Nat.beq ((List.range 1755).countP fun x => Nat.beq (pt tK x) x) 27

@[expose] noncomputable def ballFixedK (P q : Nat) : Bool :=
  allN 2925 fun v => !(onLineK q v) || (List.range 3).all fun k =>
    allN 2925 fun w => !(onLineK (lpK (3 * v + k)) w) || (List.range 3).all fun k' =>
      Nat.beq (pt P (lpK (3 * w + k'))) (lpK (3 * w + k'))

@[expose] noncomputable def movedW (q : Nat) : Bool :=
  let v := pg 16 (mask 16) (J47W 0) q
  let c := pg 16 (mask 16) (J47W 1) q
  Nat.blt v 2925 && Nat.blt (c / 4 % 4) 3 && Nat.blt (c % 4) 3 && Nat.blt (c / 16) 2925 &&
    onLineK q v && onLineK (lpK (3 * v + c / 4 % 4)) (c / 16) &&
    !(Nat.beq (pt uK (lpK (3 * (c / 16) + c % 4))) (lpK (3 * (c / 16) + c % 4)))

@[expose] noncomputable def ballK : Bool :=
  onLineK 0 0 && onLineK 1 0 && onLineK 1 5 && onLineK 10 5 && ballFixedK uK 10 &&
    (allN 1755 fun q => Nat.beq q 10 || movedW q) &&
    (allN 2925 fun v => !(onLineK 0 v) || (List.range 3).all fun k =>
      allN 2925 fun w => !(onLineK (lpK (3 * v + k)) w && onLineK 10 w) ||
        (Nat.beq v 0 && Nat.beq (lpK (3 * v + k)) 1)) &&
    allN 2925 fun w => !(onLineK 1 w && onLineK 10 w) || Nat.beq w 5

@[expose] noncomputable def yK : Bool :=
  Nat.beq (powK (X 3) 3) idK && !(Nat.beq (X 3) idK) && Nat.beq (pc (X 3) tpK) (pc tpK (X 3)) &&
    Nat.beq (cj (X 3) zpK) jpK

theorem checks : letK = true ∧ chainK = true ∧ uChK = true ∧ iK = true ∧ fixK = true ∧
    ballK = true ∧ yK = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem ball_neg : ballFixedK uK 0 = false := by
  decide +kernel

end CertificateChecks.KernelMisc.TitsJ47

end
