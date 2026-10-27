
module

public import Certificates.Kernel.Misc.Tits.Cls7050D

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.Tits7050

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor
open CertificateChecks.KernelSporSch

@[expose] noncomputable def PSb (i j : Nat) : Nat := nIf(Nat.beq j 0, X, nIf(Nat.beq j 1, TitsT, R i))

@[expose] noncomputable def PSIb (i j : Nat) : Nat := pinvS 1755 11 (mask 11) (PSb i j)

@[expose] noncomputable def bw (i : Nat) : Nat :=
  wordK 1755 11 (mask 11) (pidn 1755 11) (PSb i) (PSIb i) (CFSG.Quasithin.RuRank3.titsBadWords.getD i [])

@[expose] noncomputable def neId (B : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true false (Nat.beq B (pidn 1755 11))

@[expose] noncomputable def badK (i : Nat) : Bool :=
  bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) (PSb i) (PSIb i) 3
      (CFSG.Quasithin.RuRank3.titsBadWords.getD i []) (bw i),
    strictB (bw i) fun B => bAnd(canonK 1755 11 (mask 11) (1755 * 11) B,
      bAnd(neId (pw B 12), bAnd(neId (pw B 13), neId (pw B 5)))))

theorem bad : allN 30 (fun i => bIf(CFSG.Quasithin.RuRank3.titsRepGood.getD i false, true, badK i)) =
    true := by decide +kernel

end CertificateChecks.KernelMisc.Tits7050

end
