module

public import Certificates.Kernel.SporSch.Ru.RFacts
public import Certificates.Kernel.SporSch.Ru.F1920
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuSy

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Sporadic.RuSchreier
  CertificateChecks.KernelSporSch

@[expose] noncomputable def SFp (j : Nat) : Nat := RuT1920.L (Nat.add 7 j)

@[expose] noncomputable def SFI (j : Nat) : Nat := RuLI1920 (Nat.add 7 j)

@[expose] noncomputable def RFp (i : Nat) : Nat := RuT1920.L (Nat.add 34 i)

@[expose] noncomputable def siftR (G : Nat) : Bool :=
  strictB G (fun G => bAnd(Nat.beq (Nat.shiftRight G (1920 * 11)) 0,
    bAnd(allN 1920 (fun i => Nat.blt (pg 11 (mask 11) G i) 1920),
    siftK 1920 11 (mask 11) (1920 * 11) (pidn 1920 11) RuRS.LR RuRS.TRI RuRS.BP 2 0 G)))

@[expose] noncomputable def conjOK (k : Nat) : Bool :=
  strictB (Nat.div k 4) (fun i => strictB (Nat.mod k 4) (fun j =>
    siftR (pcomp 1920 11 (mask 11) (pcomp 1920 11 (mask 11) (SFp j) (RFp i)) (SFI j))))

@[expose] noncomputable def commOK (k : Nat) : Bool :=
  strictB (Nat.div k 4) (fun i => strictB (Nat.mod k 4) (fun j =>
    siftR (pcomp 1920 11 (mask 11) (pcomp 1920 11 (mask 11)
      (pcomp 1920 11 (mask 11) (SFp i) (SFp j)) (SFI i)) (SFI j))))

@[expose] noncomputable def sqOK (i : Nat) : Bool :=
  siftR (pcomp 1920 11 (mask 11) (SFp i) (SFp i))

@[expose] noncomputable def pS (G : Nat) : Bool :=
  bIf(allN 4 (fun j => Nat.beq (pcomp 1920 11 (mask 11) G (SFp j)) (pcomp 1920 11 (mask 11) (SFp j) G)),
    bIf(Nat.beq G (pidn 1920 11), true, Nat.beq G RuF.ZF), true)

@[expose] noncomputable def rowS (a : Nat) : Bool :=
  row2K 1920 11 (mask 11) (1920 * 11) RuSS1920.LR RuSS1920.TR pS a

@[expose] noncomputable def g2S (T0 T1 x : Nat) : Nat :=
  pg 11 (mask 11) T0 (pg 11 (mask 11) T1 x)

@[expose] noncomputable def cmS (T0 T1 S : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih =>
    bAnd(Nat.beq (g2S T0 T1 (pg 11 (mask 11) S x)) (pg 11 (mask 11) S (g2S T0 T1 x)), ih)) l

@[expose] noncomputable def cPtsS : List Nat := [100, 700, 1300]

@[expose] noncomputable def pSF (T0 T1 : Nat) : Bool :=
  bIf(cmS T0 T1 (SFp 0) cPtsS, pS (pcomp 1920 11 (mask 11) T0 T1), true)

@[expose] noncomputable def rowSF (a : Nat) : Bool :=
  strictB (RuSS1920.LR (nat_lit 0)) (fun R0 => strictB (RuSS1920.LR (nat_lit 1)) (fun R1 =>
  strictB (RuSS1920.TR (Nat.add (roff 1920 (1920 * 11) R0) a)) (fun T0 =>
  strictB (roff 1920 (1920 * 11) R1) (fun o1 =>
    allN (rcnt R1) (fun b => strictB (RuSS1920.TR (Nat.add o1 b)) (fun T1 => pSF T0 T1))))))

end CertificateChecks.KernelSporSch.RuSy

#kss_each CertificateChecks.KernelSporSch.RuSy.CJ CertificateChecks.KernelSporSch.RuSy.conjOK 20
#kss_each CertificateChecks.KernelSporSch.RuSy.CM CertificateChecks.KernelSporSch.RuSy.commOK 16
#kss_each CertificateChecks.KernelSporSch.RuSy.SQ CertificateChecks.KernelSporSch.RuSy.sqOK 4
#kss_each CertificateChecks.KernelSporSch.RuSy.RS CertificateChecks.KernelSporSch.RuSy.rowSF 1024

namespace CertificateChecks.KernelSporSch.RuSy

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Sporadic.RuSchreier
  CertificateChecks.KernelSporSch

theorem s1OK : siftR (SFp 1) = true := by quickRfl

theorem cntS : Nat.beq (rcnt (RuSS1920.LR 0)) 1024 = true := by quickRfl

theorem canS : allN 7 (fun j => bAnd(canonK 1920 11 (mask 11) (1920 * 11) (SFp j),
    bAnd(canonK 1920 11 (mask 11) (1920 * 11) (SFI j),
      canonK 1920 11 (mask 11) (1920 * 11) (RFp j)))) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuSy

end
