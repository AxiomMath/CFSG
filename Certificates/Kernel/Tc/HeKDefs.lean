module

public import Certificates.Kernel.Tc.HeHex
public import Certificates.Kernel.Tc.HeTrees
public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Data.Kernel.HeLoc.Tree

public section

namespace CertificateChecks.KernelTc.He

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
  CertificateChecks.KernelLC.HeFix

@[expose] noncomputable def wOK (k : Nat) : Bool :=
  bAnd(wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 (heTcWs.getD k []) (HT k),
    invEqK 8330 14 (mask 14) (8330 * 14) (HT k) (HTI k))

@[expose] noncomputable def t (k x : Nat) : Nat := pg 14 (mask 14) (HT k) x

@[expose] noncomputable def ti (k x : Nat) : Nat := pg 14 (mask 14) (HTI k) x

@[expose] def bs : List Nat := [0, 1, 2, 3, 4]

@[expose] def q0 (_ : Nat) : Nat := 0

@[expose] noncomputable def cu (i x : Nat) : Nat := t (Nat.mul 2 i) x
@[expose] noncomputable def cv (i x : Nat) : Nat := t (Nat.add 1 (Nat.mul 2 i)) x
@[expose] noncomputable def cui (i x : Nat) : Nat := ti (Nat.mul 2 i) x
@[expose] noncomputable def cvi (i x : Nat) : Nat := ti (Nat.add 1 (Nat.mul 2 i)) x

@[expose] noncomputable def gq (i x : Nat) : Nat := cu i (cv i (cui i (cvi i x)))

@[expose] noncomputable def gk (l x : Nat) : Nat := nIf(Nat.beq l 2, t 14 x, t (Nat.add 4 l) x)

@[expose] noncomputable def gy (k x : Nat) : Nat := t (Nat.add 12 k) x

@[expose] noncomputable def rr (j x : Nat) : Nat := nIf(Nat.beq j 0, x, t (Nat.add 5 j) x)
@[expose] noncomputable def ri (j x : Nat) : Nat := nIf(Nat.beq j 0, x, ti (Nat.add 5 j) x)

@[expose] def sigF (i j : Nat) : Nat := (sig[i]!)[j]!

@[expose] noncomputable def EQ (i k : Nat) : Nat := fld(TQ.ER i, Nat.mul 16 k, 65535)
@[expose] noncomputable def EK (i k : Nat) : Nat := fld(TK.ER i, Nat.mul 16 k, 65535)
@[expose] noncomputable def EY (i k : Nat) : Nat := fld(TY.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def tq (i x : Nat) : Nat := trV gq TQ.P TQ.L 7560 i x
@[expose] noncomputable def tk (i x : Nat) : Nat := trV gk TK.P TK.L 1080 i x
@[expose] noncomputable def ty (i x : Nat) : Nat := trV gy TY.P TY.L 27 i x

@[expose] noncomputable def kq (i : Nat) : Nat := keyV 8330 CFSG.Sporadic.HeldB.heBase (tq i)
@[expose] noncomputable def kk (i : Nat) : Nat := keyV 8330 CFSG.Sporadic.HeldB.heBase (tk i)
@[expose] noncomputable def ky (i : Nat) : Nat := keyV 8330 CFSG.Sporadic.HeldB.heBase (ty i)

end CertificateChecks.KernelTc.He

end
