module

public import Certificates.Kernel.SporSch.Ru.EndData
public import Certificates.Kernel.SporSch.Ru.EndR
public import Certificates.Kernel.SporSch.Ru.Lines
public import Certificates.Kernel.SporSch.Ru.JChain
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import CFSG.Certificates.Kernel.SporSch.AnyN
public import Certificates.Data.Kernel.SporSch.MathieuOC
public import Certificates.Data.Kernel.Spor.Raw
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuEnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.SporSch.MOC
open CertificateChecks.KernelSporSch

@[expose] noncomputable def fv (P i : Nat) : Nat := pg 12 (mask 12) P i

@[expose] noncomputable def ne (a b : Nat) : Bool := bIf(Nat.beq a b, false, true)

@[expose] noncomputable def R : Nat := RuEndR.F 0

@[expose] noncomputable def A0 : Nat := RuT4060.L 0

@[expose] noncomputable def A0I : Nat := RuLI4060 0

@[expose] noncomputable def eK : Bool :=
  allN 4060 fun p => bAnd(Nat.beq (fv A0 (fv A0 p)) p, bAnd(Nat.beq (fv R (fv R p)) p,
    bAnd(Nat.beq (fv A0 (fv R p)) (fv R (fv A0 p)), bAnd(ne (fv A0 p) p,
      bAnd(ne (fv R p) p, ne (fv A0 (fv R p)) p)))))

@[expose] noncomputable def pK : Bool :=
  bAnd(permOK 4060 12 (mask 12) (4060 * 12) A0 A0I,
    bAnd(permOK 4060 12 (mask 12) (4060 * 12) B BI,
    bAnd(permOK 4060 12 (mask 12) (4060 * 12) R RI,
    bAnd(allN 8 (fun i => permOK 4060 12 (mask 12) (4060 * 12) (X i) (XI i)),
      allN 6 (fun i => permOK 4060 12 (mask 12) (4060 * 12) (Y i) (YI i))))))

@[expose] noncomputable def cB (E E' p : Nat) : Bool :=
  Nat.beq (fv E (fv BI (fv E' (fv B p)))) (fv BI (fv E' (fv B (fv E p))))

@[expose] noncomputable def bcK : Bool :=
  allN 4060 fun p => bAnd(cB A0 A0 p, bAnd(cB A0 R p, bAnd(cB R A0 p, cB R R p)))

@[expose] noncomputable def cC (p : Nat) : Nat := fv BI (fv A0 (fv B p))

@[expose] noncomputable def bnK : Bool :=
  bAnd(anyN 4060 (fun p => ne (cC p) p), bAnd(anyN 4060 (fun p => ne (cC p) (fv A0 p)),
    bAnd(anyN 4060 (fun p => ne (cC p) (fv R p)),
      anyN 4060 (fun p => ne (cC p) (fv A0 (fv R p))))))

@[expose] noncomputable def xcK : Bool :=
  allN 8 fun i => allN 4060 fun p => bAnd(Nat.beq (fv (X i) (fv A0 p)) (fv A0 (fv (X i) p)),
    Nat.beq (fv (X i) (fv R p)) (fv R (fv (X i) p)))

@[expose] noncomputable def cm (P Q PI QI p : Nat) : Nat := fv P (fv Q (fv PI (fv QI p)))

@[expose] noncomputable def trK : Bool :=
  allN 4060 fun p => bAnd(allN 4 (fun j => Nat.beq (fv (Y j) p)
      (cm (X (Nat.mul 2 j)) (X (Nat.add (Nat.mul 2 j) 1)) (XI (Nat.mul 2 j))
        (XI (Nat.add (Nat.mul 2 j) 1)) p)),
    bAnd(Nat.beq (fv (Y 4) p) (cm (Y 0) (Y 1) (YI 0) (YI 1) p),
      bAnd(Nat.beq (fv (Y 5) p) (cm (Y 2) (Y 3) (YI 2) (YI 3) p),
        Nat.beq (cm (Y 4) (Y 5) (YI 4) (YI 5) p) (fv A0 (cC p)))))

@[expose] noncomputable def siftP (G : Nat) : Bool :=
  siftK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) RuJS.LR RuJS.TRI RuJS.BP 4 0 G

@[expose] noncomputable def siftX (i : Nat) : Bool := siftP (X i)

@[expose] noncomputable def siftS (j : Nat) : Bool := siftP (RuES.S j)

@[expose] noncomputable def sigK (i a : Nat) : Nat :=
  pg 3 (nat_lit 7) (nat_lit 15479356527840) (Nat.add (Nat.mul i 5) a)

@[expose] noncomputable def lK : Bool := allN 4060 fun p => Nat.blt (fv LAB p) 5

@[expose] noncomputable def lsK : Bool :=
  allN 3 fun i => allN 4060 fun p =>
    Nat.beq (fv LAB (fv (RuT4060.L (Nat.add 39 i)) p)) (sigK i (fv LAB p))

@[expose] noncomputable def scK : Bool :=
  allN 5 fun j => allN 4060 fun p =>
    Nat.beq (fv (RuES.S j) (fv A0 p)) (fv A0 (fv (RuES.S j) p))

@[expose] noncomputable def elemOK (j : Nat) : Bool :=
  strictB (elemK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) RuES.LR RuES.TR 1 j) fun Z =>
    anyN 4060 fun p => bIf(Nat.beq (fv Z (fv Z p)) p,
      bIf(Nat.beq (fv LAB (fv Z p)) (fv LAB p), Nat.beq (fv Z p) p, true), true)

theorem eOK : eK = true := by quickRfl
theorem pOK : pK = true := by quickRfl
theorem bcOK : bcK = true := by quickRfl
theorem bnOK : bnK = true := by quickRfl
theorem xcOK : xcK = true := by quickRfl
theorem trOK : trK = true := by quickRfl
theorem lOK : lK = true := by quickRfl
theorem lsOK : lsK = true := by quickRfl
theorem scOK : scK = true := by quickRfl
theorem cntK : Nat.beq (rcnt (RuES.LR 0)) 256 = true := by quickRfl
theorem sA0 : siftP A0 = true := by quickRfl
theorem sR : siftP R = true := by quickRfl
theorem sB : siftP B = true := by quickRfl
theorem pL : allN 3 (fun i => permOK 4060 12 (mask 12) (4060 * 12) (RuT4060.L (Nat.add 39 i))
    (RuLI4060 (Nat.add 39 i))) = true := by quickRfl
theorem sJ : allN 18 (fun j => Nat.beq (RuJS.S j) (RuT4060.L (Nat.add 15 j))) = true := by
  quickRfl
theorem bJ : allN 4 (fun t => Nat.beq (CFSG.Sporadic.RuSchreier.ruBaseArr 4060
    CFSG.Sporadic.RuSchreier.ruJoinBase)[t]! (pg 12 (mask 12) RuJS.BP t)) = true := by quickRfl
theorem permJ : allN 18 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (RuJS.S j) (RuJS.SI j)) =
    true := by quickRfl

meta def swM : Array Nat := ((Array.range 4060).set! 0 1).set! 1 0

end CertificateChecks.KernelSporSch.RuEnd

#kss_each CertificateChecks.KernelSporSch.RuEndSX CertificateChecks.KernelSporSch.RuEnd.siftX 8
#kss_each CertificateChecks.KernelSporSch.RuEndSS CertificateChecks.KernelSporSch.RuEnd.siftS 5
#ks_perm CertificateChecks.KernelSporSch.RuEnd.SW 12 CertificateChecks.KernelSporSch.RuEnd.swM

namespace CertificateChecks.KernelSporSch.RuEnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch
open CertificateChecks.KernelSporSch

theorem negA0 : bIf(anyN 4060 fun p => bIf(Nat.beq (fv A0 (fv A0 p)) p, Nat.beq (fv A0 p) p, true),
    false, true) = true := by
  quickRfl

theorem negSig : bIf(allN 4060 fun p => Nat.beq (fv LAB (fv (RuT4060.L 39) p)) (fv LAB p),
    false, true) = true := by
  quickRfl

theorem negSift : bIf(siftP SW, false, true) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuEnd

end
