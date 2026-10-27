module

public import Certificates.Kernel.Fi22Guest.Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFi22AltData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Alt

open CFSG.KC.Enum CFSG.KS CertificateChecks.KernelFi22Guest CFSG.AGLEmbedding.KFactProofs.Fi22Alt

@[expose] noncomputable def xComp (i y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) y (fun s _ ih => strictN ih fun z => lmap s z)
    (List.getD xData i [])

@[expose] noncomputable def xM (i y : Nat) : Nat := xComp (Nat.pred i) y

@[expose] noncomputable def altSl (r : Nat) : Bool :=
  bIf(Nat.beq r 0, allN (nat_lit 3510) fun x => Nat.beq (iterK (xM 1) 3 x) x,
    bIf(Nat.blt r 7, allN (nat_lit 3510) fun x =>
        bAnd(Nat.beq (iterK (xM (Nat.succ r)) 2 x) x,
          Nat.beq (iterK (fun z => xM r (xM (Nat.succ r) z)) 3 x) x),
      bIf(Nat.blt (Nat.div (Nat.sub r 7) 8) 1, true,
        bIf(Nat.blt (Nat.mod (Nat.sub r 7) 8) (Nat.add (Nat.div (Nat.sub r 7) 8) 2), true,
          allN (nat_lit 3510) fun x => Nat.beq (iterK (fun z =>
            xM (Nat.div (Nat.sub r 7) 8) (xM (Nat.mod (Nat.sub r 7) 8) z)) 2 x) x))))

@[expose] noncomputable def altMv : Bool := movesK (xM 1)

end CertificateChecks.KernelFi22Alt

end
