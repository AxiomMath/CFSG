module

public import Certificates.Kernel.LocalComp.L34F946Data
public import Certificates.Kernel.LocalComp.L34NDefs
public import Certificates.Kernel.LocalComp.L34SChk
public import Certificates.Data.Kernel.L34SelWord
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34F946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Norm
open CFSG.KC.L34SelWord
open CFSG.KLie.CT (fget andB orB notB anyN)

@[expose] noncomputable def fK (j : Nat) : Nat := fget (KS (nat_lit 0)) j (nat_lit 32)

@[expose] noncomputable def predA (v : Nat) : Bool :=
  andB (Nat.beq (Nat.mod v (nat_lit 2)) (nat_lit 1)) (notB (Nat.beq (Nat.div v (nat_lit 8)) (nat_lit 0)))

@[expose] noncomputable def predZ (v : Nat) : Bool :=
  andB (Nat.beq (Nat.mod (Nat.div v (nat_lit 2)) (nat_lit 2)) (nat_lit 1))
    (notB (Nat.beq (Nat.div v (nat_lit 8)) (nat_lit 0)))

@[expose] noncomputable def inS (s x : Nat) : Bool :=
  andB (Nat.blt s (nat_lit 20160)) (Nat.beq (L34S.T s) x)

@[expose] noncomputable def okA (W : Nat → Nat) (m i : Nat) : Bool :=
  strictB (L34R.T i) fun x => orB (inS (fget (W m) (nat_lit 1) (nat_lit 32)) x)
    (strictB (fget (W m) (nat_lit 2) (nat_lit 32)) fun j => andB (Nat.blt j (nat_lit 20160))
      (strictB (L34S.T j) fun c => andB (commPt (nat_lit 42) (nat_lit 6) c x)
        (orB (notB (inPts (nat_lit 42) (nat_lit 6) (nat_lit 9) L34N.AP c (L34N.K (nat_lit 0))))
          (notB (inPts (nat_lit 42) (nat_lit 6) (nat_lit 9) L34N.AP c (L34N.K (nat_lit 1)))))))

@[expose] noncomputable def tgt (t x : Nat) : Nat :=
  nIf(Nat.beq t (nat_lit 0), L34N.K (nat_lit 2), nIf(Nat.beq t (nat_lit 1), x,
    nIf(Nat.beq t (nat_lit 2), pcomp (nat_lit 42) (nat_lit 6) (mask (nat_lit 6)) (L34N.K (nat_lit 2)) x,
      pcomp (nat_lit 42) (nat_lit 6) (mask (nat_lit 6))
        (pcomp (nat_lit 42) (nat_lit 6) (mask (nat_lit 6)) (L34N.K (nat_lit 2)) (L34N.K (nat_lit 2)))
        x)))

@[expose] noncomputable def wordsOK (W G : Nat → Nat) (m c0 c1 : Nat) : Bool :=
  allN (nat_lit 3) fun k => Nat.beq
    (wordK (nat_lit 42) (nat_lit 6) c0 c1 (fget (W m) (Nat.add (nat_lit 6) (Nat.mul (nat_lit 2) k)) (nat_lit 32))
      (fget (W m) (Nat.add (nat_lit 7) (Nat.mul (nat_lit 2) k)) (nat_lit 32)) (pidn (nat_lit 42) (nat_lit 6)))
    (G k)

@[expose] noncomputable def okZ (W G : Nat → Nat) (m i : Nat) : Bool :=
  strictB (L34R.T i) fun x => orB (inS (fget (W m) (nat_lit 1) (nat_lit 32)) x)
    (strictB (fget (W m) (nat_lit 2) (nat_lit 32)) fun j0 =>
      strictB (fget (W m) (nat_lit 4) (nat_lit 32)) fun j1 =>
        andB (andB (Nat.blt j0 (nat_lit 20160)) (Nat.blt j1 (nat_lit 20160)))
          (strictB (L34S.T j0) fun c0 => strictB (L34S.T j1) fun c1 =>
            andB (andB (commPt (nat_lit 42) (nat_lit 6) c0 (tgt (fget (W m) (nat_lit 3) (nat_lit 32)) x))
              (commPt (nat_lit 42) (nat_lit 6) c1 (tgt (fget (W m) (nat_lit 5) (nat_lit 32)) x)))
              (wordsOK W G m c0 c1)))

theorem kA : selK 7755 L34N.J predA 80 WA (okA WA) = true := by quickRfl

theorem kZ : selK 7755 L34N.J predZ 26 WZ (okZ WZ L34R.G) = true := by quickRfl

theorem kK : andB (andB (andB (inS (fK 0) (L34N.K 0)) (inS (fK 1) (L34N.K 1)))
    (andB (inS (fK 2) (L34N.K 2)) (o3Pt 42 6 (pidn 42 6) (L34N.K 0))))
    (andB (andB (o3Pt 42 6 (pidn 42 6) (L34N.K 1)) (o3Pt 42 6 (pidn 42 6) (L34N.K 2)))
      (andB (commPt 42 6 (L34N.K 0) (L34N.K 1))
        (allN 9 fun i => allN 9 fun j => orB (Nat.beq i j)
          (notB (Nat.beq (L34N.AP i) (L34N.AP j)))))) = true := by
  quickRfl

end CertificateChecks.KernelLC.L34F946

end
