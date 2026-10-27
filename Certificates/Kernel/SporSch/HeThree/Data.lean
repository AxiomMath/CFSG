module

public import Certificates.Kernel.SporSch.HeT.CntData
public import Certificates.Kernel.B3S3.HexGen
public import Certificates.Data.B3Spor3.He
public meta import Certificates.Kernel.SporSch.HeT.CntData
public meta import Certificates.Data.B3Spor3.He
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeThree

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB
open CFSG.Certificates.Native CFSG.HardMathSupport.Solomon.Coordinator.B3S3
open CertificateChecks.KernelSporSch.HeCn

meta def ysM : Array (Array Nat) := heS3CaseX

meta def nfOfM (g : Array Nat) : Nat :=
  packNF (decodeNF heLevels ((heBase.map fun b => g[b]!).toArray))

meta def permsM : Array (Array Nat) :=
  let xs := ysM.map xOf
  #[xs[0]!, invCand 8330 xs[0]!, xs[1]!, invCand 8330 xs[1]!]

meta def natsM : List Nat :=
  [packNF (cOf ysM[0]!), packNF (cOf ysM[1]!), nfOfM ysM[0]!, nfOfM ysM[1]!]

meta def vOf (c : Nat) : Array Nat :=
  let y := ysM[c]!
  let x := xOf y
  (Array.range 8330).map fun k0 => srchCnt x y k0 1

meta def v0M : Array Nat := vOf 0
meta def v1M : Array Nat := vOf 1
meta def x0M : Array Nat := xOf ysM[0]!
meta def x1M : Array Nat := xOf ysM[1]!
meta def y0M : Array Nat := ysM[0]!
meta def y1M : Array Nat := ysM[1]!

meta def rz0M : Array Nat × Array Nat := orbRZ x0M y0M
meta def rz1M : Array Nat × Array Nat := orbRZ x1M y1M
meta def r0M : Array Nat := rz0M.1
meta def z0M : Array Nat := rz0M.2
meta def r1M : Array Nat := rz1M.1
meta def z1M : Array Nat := rz1M.2

end CertificateChecks.KernelSporSch.HeThree

set_option Elab.async false

#ks_chars CertificateChecks.KernelSporSch.HeThree.XC
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.heS3CaseXHex
#kb3_hexarrs CertificateChecks.KernelSporSch.HeThree.XC
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.heS3CaseXHex 4 8330 14

#kss_perms CertificateChecks.KernelSporSch.HeThreeP 14 CertificateChecks.KernelSporSch.HeThree.permsM

#krowsw CertificateChecks.KernelSporSch.HeThreeRX0 14 CertificateChecks.KernelSporSch.HeThree.x0M
#krowsw CertificateChecks.KernelSporSch.HeThreeRX1 14 CertificateChecks.KernelSporSch.HeThree.x1M
#krowsw CertificateChecks.KernelSporSch.HeThreeRY0 14 CertificateChecks.KernelSporSch.HeThree.y0M
#krowsw CertificateChecks.KernelSporSch.HeThreeRY1 14 CertificateChecks.KernelSporSch.HeThree.y1M
#krowsw CertificateChecks.KernelSporSch.HeThreeV0 12 CertificateChecks.KernelSporSch.HeThree.v0M
#krowsw CertificateChecks.KernelSporSch.HeThreeV1 12 CertificateChecks.KernelSporSch.HeThree.v1M
#krowsw CertificateChecks.KernelSporSch.HeThreeR0 14 CertificateChecks.KernelSporSch.HeThree.r0M
#krowsw CertificateChecks.KernelSporSch.HeThreeZ0 80 CertificateChecks.KernelSporSch.HeThree.z0M
#krowsw CertificateChecks.KernelSporSch.HeThreeR1 14 CertificateChecks.KernelSporSch.HeThree.r1M
#krowsw CertificateChecks.KernelSporSch.HeThreeZ1 80 CertificateChecks.KernelSporSch.HeThree.z1M

#knatlist CertificateChecks.KernelSporSch.HeThree.nats CertificateChecks.KernelSporSch.HeThree.natsM

namespace CertificateChecks.KernelSporSch.HeThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch.HeCn CFSG.Sporadic.HeldB

@[expose] noncomputable def pick (c : Nat) (a b : Nat → Nat) : Nat → Nat :=
  Bool.rec (motive := fun _ => Nat → Nat) b a (Nat.beq c 0)

@[expose] noncomputable def RX (c : Nat) : Nat → Nat := pick c HeThreeRX0 HeThreeRX1

@[expose] noncomputable def RY (c : Nat) : Nat → Nat := pick c HeThreeRY0 HeThreeRY1

@[expose] noncomputable def X (c : Nat) : Nat := HeThreeP (Nat.mul 2 c)

@[expose] noncomputable def XI (c : Nat) : Nat := HeThreeP (Nat.add (Nat.mul 2 c) 1)

@[expose] noncomputable def F (c : Nat) : Nat := nats.getD c 0

@[expose] noncomputable def G (c : Nat) : Nat := nats.getD (Nat.add 2 c) 0

@[expose] noncomputable def V (c k : Nat) : Nat :=
  CFSG.KS.Row.rg 12 (mask 12) (pick c HeThreeV0 HeThreeV1) 0 k

@[expose] noncomputable def rx (c : Nat) : Bool :=
  bAnd(rbAll (RX c) (X c), bAnd(Nat.beq (pmR (RX c) 0) 0, Nat.beq (pmR (RX c) 1) 2))

@[expose] noncomputable def ry (c s : Nat) : Bool :=
  allN 170 (fun j => strictB (Nat.add (Nat.mul s 170) j) (fun x =>
    bAnd(Nat.beq (pmR (RY c) x) (pm (XC.F c) x), Nat.beq (pmR (RY c) x) (HeTc.nfp (G c) x))))

@[expose] noncomputable def cj (c s : Nat) : Bool := cjB (RX c) (RY c) (F c) s

@[expose] noncomputable def Rc (c k : Nat) : Nat :=
  CFSG.KS.Row.rg 14 (mask 14) (pick c HeThreeR0 HeThreeR1) 0 k

@[expose] noncomputable def Zc (c k : Nat) : Nat :=
  CFSG.KS.Row.rg 80 (mask 80) (pick c HeThreeZ0 HeThreeZ1) 0 k

@[expose] noncomputable def orc (c s : Nat) : Bool := orB (RX c) (RY c) (V c) (Rc c) (Zc c) 8330 s

@[expose] noncomputable def or0 (s : Nat) : Bool := orc 0 s

@[expose] noncomputable def or1 (s : Nat) : Bool := orc 1 s

end CertificateChecks.KernelSporSch.HeThree

end
