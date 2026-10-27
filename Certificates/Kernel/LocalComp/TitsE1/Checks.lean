module

public import Certificates.Kernel.LocalComp.TitsE1.Data
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.BfsPin
public import Certificates.Kernel.Sporadic.Tits.ChainD
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.TitsE1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 Certificates.CoreE1Perm

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def IDN : Nat := pidn 1755 11

@[expose] def nB (b : Bool) : Bool := bIf(b, false, true)

@[expose] def wd (k : Nat) : List Int :=
  if k = 0 then (titsE1Data ()).zW
  else if k < 5 then (titsE1Data ()).xWs.getD (k - 1) []
  else ((titsE1Data ()).es.getD ((k - 5) / 2) default).gWs.getD ((k - 5) % 2) []

@[expose] noncomputable def cenP (p : Nat) : Bool :=
  bAnd(Nat.beq (pc p (TitsE1S.G 0)) (pc (TitsE1S.G 0) p),
    bAnd(Nat.beq (pc p (TitsE1S.G 1)) (pc (TitsE1S.G 1) p),
      Nat.beq (pc p (TitsE1S.G 2)) (pc (TitsE1S.G 2) p)))

@[expose] noncomputable def inZP (p : Nat) : Bool :=
  bIf(Nat.beq p (ZX 36), true, bIf(Nat.beq p (ZX 37), true, Nat.beq p (ZX 38)))

@[expose] noncomputable def inEP (i p : Nat) : Bool :=
  nB (allN 9 fun k => nB (Nat.beq p (ZX (Nat.add (Nat.mul 9 i) k))))

theorem ckGens : allN 2 (fun k => bAnd(Nat.beq (GA k) (CertificateChecks.KernelSpor.TitsD.S k),
    permOK 1755 11 (mask 11) (1755 * 11) (GA k) (GI k))) = true := by
  decide +kernel

theorem ckWords0 : allN 5 (fun k => wordEqK 1755 11 (mask 11) IDN GA GI 2 (wd k) (W k)) = true := by
  decide +kernel

theorem ckWords1 : allN 8 (fun k => wordEqK 1755 11 (mask 11) IDN GA GI 2 (wd (Nat.add 5 k))
    (W (Nat.add 5 k))) = true := by
  decide +kernel

theorem ckS : allN 3 (fun k => wordEqK 1755 11 (mask 11) IDN GA GI 2
    ((titsE1Data ()).sW.getD k []) (TitsE1S.G k)) = true := by
  decide +kernel

theorem ckGI : allN 8 (fun k => permOK 1755 11 (mask 11) (1755 * 11) (W (Nat.add 5 k)) (WI k)) =
    true := by
  decide +kernel

theorem ckCanon : bAnd(allN 13 (fun k => canonK 1755 11 (mask 11) (1755 * 11) (W k)),
    bAnd(allN 39 (fun k => canonK 1755 11 (mask 11) (1755 * 11) (ZX k)),
      allN 12 (fun k => canonK 1755 11 (mask 11) (1755 * 11) (HC k)))) = true := by
  decide +kernel

theorem ckZX : bAnd(allN 36 (fun k => Nat.beq (pc (pw 1755 11 (W 0) (Nat.div (Nat.mod k 9) 3))
      (pw 1755 11 (W (Nat.add 1 (Nat.div k 9))) (Nat.mod k 3))) (ZX k)),
    allN 3 (fun a => Nat.beq (pw 1755 11 (W 0) a) (ZX (Nat.add 36 a)))) = true := by
  decide +kernel

theorem ckHC : allN 4 (fun i =>
    bAnd(wordEqK 1755 11 (mask 11) IDN (fun j => W (Nat.add (Nat.add 5 (Nat.mul 2 i)) j))
        (fun j => WI (Nat.add (Nat.mul 2 i) j)) 2 [1, 2] (HC (Nat.mul 3 i)),
      bAnd(permOK 1755 11 (mask 11) (1755 * 11) (HC (Nat.mul 3 i)) (HC (Nat.add (Nat.mul 3 i) 1)),
        Nat.beq (HC (Nat.add (Nat.mul 3 i) 2))
          (pc (W 0) (pc (pc (HC (Nat.mul 3 i)) (W 0)) (HC (Nat.add (Nat.mul 3 i) 1))))))) =
    true := by
  decide +kernel

theorem ckZ : bAnd(nB (Nat.beq (W 0) IDN), bAnd(Nat.beq (pw 1755 11 (W 0) 3) IDN,
    bAnd(cenP (W 0), nB (allN 27 fun i => nB (Nat.beq (TitsE1S.T i) (W 0)))))) = true := by
  decide +kernel

theorem ckZall : allN 27 (fun i => bIf(nB (cenP (TitsE1S.T i)), true, inZP (TitsE1S.T i))) = true := by
  decide +kernel

theorem ckX : allN 4 (fun i =>
    bAnd(nB (allN 27 fun t => nB (Nat.beq (TitsE1S.T t) (W (Nat.add i 1)))),
    bAnd(Nat.beq (pw 1755 11 (W (Nat.add i 1)) 3) IDN,
    bAnd(Nat.beq (pc (W (Nat.add i 1)) (W 0)) (pc (W 0) (W (Nat.add i 1))),
      nB (inZP (W (Nat.add i 1))))))) = true := by
  decide +kernel

theorem ckXall : allN 27 (fun t => nB (allN 4 fun i => nB (inEP i (TitsE1S.T t)))) = true := by
  decide +kernel

theorem ckNC : nB (Nat.beq (pc (TitsE1S.G 1) (TitsE1S.G 2)) (pc (TitsE1S.G 2) (TitsE1S.G 1))) =
    true := by
  decide +kernel

theorem ckEnt : allN 4 (fun i => bAnd(allN 2 (fun j =>
      strictB (ZX (Nat.add (Nat.add (Nat.mul 9 i)
        (Nat.mul 3 (((titsE1Data ()).es.getD i default).nd.getD j default).a))
        (((titsE1Data ()).es.getD i default).nd.getD j default).b)) fun u =>
      bAnd(nB (Nat.beq u IDN), Nat.beq (pc (W (Nat.add (Nat.add 5 (Nat.mul 2 i)) j)) u)
        (pc (pw 1755 11 u (((titsE1Data ()).es.getD i default).nd.getD j default).α)
          (W (Nat.add (Nat.add 5 (Nat.mul 2 i)) j))))),
    bAnd(nB (Nat.beq (HC (Nat.add (Nat.mul 3 i) 2)) IDN),
      Nat.beq (pw 1755 11 (HC (Nat.add (Nat.mul 3 i) 2)) 4) IDN))) = true := by
  decide +kernel

end CertificateChecks.KernelLC.TitsE1

end
