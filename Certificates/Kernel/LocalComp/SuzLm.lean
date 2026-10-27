module

public import Certificates.Kernel.LocalComp.B0SuzMat
public import Certificates.Data.Kernel.L34K
public import Certificates.Data.Kernel.HeAutK
public import Certificates.Data.SuzLmRank
meta import Certificates.Data.SuzLmRank
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

namespace CertificateChecks.KernelLC.SuzLm

meta def nineM : Array (Array Nat) :=
  let T := CFSG.ComponentClassification.AS81.SuzB0.matEnum.tabs
  let e := CFSG.PSL3Four.Native.idTab 64
  let c := CFSG.PSL3Four.Native.comp
  let k := ((List.range T.size).find? fun k =>
    let s := T[k]!
    let s3 := c 64 s (c 64 s s)
    !(s3 == e) && c 64 s3 (c 64 s3 s3) == e).getD 0
  #[#[k]]

end CertificateChecks.KernelLC.SuzLm

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelLC.LmW CertificateChecks.KernelLC.SuzLm.nineM 32

namespace CertificateChecks.KernelLC.SuzLm

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.L34K CertificateChecks.KernelLC
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 64 7 (mask 7) p q

@[expose] noncomputable def e : Nat := pidn 64 7

@[expose] noncomputable def fixCnt (p : Nat) : Nat :=
  CFSG.KC.HeAutK.cntR (fun j => Nat.beq (pg 7 (mask 7) (SuzB0M.T j) p) p) 0 25920

@[expose] noncomputable def centCnt (x : Nat) : Nat :=
  CFSG.KC.HeAutK.cntR (fun j => commPt 64 7 (SuzB0M.T j) x) 0 25920

@[expose] noncomputable def stabSl (s : Nat) : Bool :=
  allN 9 fun d => notB (Nat.beq (Nat.mod (fixCnt (Nat.succ (Nat.add (Nat.mul 9 s) d))) 27) 0)

@[expose] noncomputable def centPt (x : Nat) : Bool :=
  orB (notB (invPt 64 7 x)) (orB (Nat.beq x e) (notB (Nat.beq (Nat.mod (centCnt x) 27) 0)))

@[expose] noncomputable def centSl (s : Nat) : Bool :=
  allN 270 fun d => strictB (SuzB0M.T (Nat.add (Nat.mul 270 s) d)) centPt

theorem kCan : allN 25920 (fun j => canonK 64 7 (mask 7) (64 * 7) (SuzB0M.T j)) = true := by
  quickRfl

theorem kNine : strictB (SuzB0M.T (LmW 0)) (fun s => strictB (pc s (pc s s)) fun s3 =>
    andB (Nat.blt (LmW 0) 25920) (andB (notB (Nat.beq s3 e)) (Nat.beq (pc s3 (pc s3 s3)) e))) =
      true := by
  quickRfl

theorem kNeg : Nat.beq (Nat.mod (fixCnt 0) 27) 0 = true := by quickRfl

end CertificateChecks.KernelLC.SuzLm

#kon_slices CertificateChecks.KernelLC.SuzLm.stabSl 0 7
#kon_join CertificateChecks.KernelLC.SuzLm.stabAll CertificateChecks.KernelLC.SuzLm.stabSl 7

end
