module

public import Certificates.Kernel.Parrott.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
public import Certificates.Kernel.Misc.Tits.Text
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.P2004

open CFSG.KC.MiscCoset.Act CFSG.KC.Enum CFSG.KS

theorem all : allR (nat_lit 0) (nat_lit 1755) (pointOK A (nat_lit 12) (nat_lit 1755) rels) = true := by
  allR_blocks 16

theorem bind : allR 0 1755 (fun x => andB
    (Nat.beq (A (x * (12 + 12) + 2 * 0)) (pg 11 (mask 11) (CertificateChecks.KernelMisc.TitsText.F (18 + 0)) x))
    (Nat.beq (A (x * (12 + 12) + 2 * 1)) (pg 11 (mask 11) (CertificateChecks.KernelMisc.TitsText.F (18 + 1)) x))) =
    true := by
  quickRfl

theorem neg : notB (pointOK A 12 1755 (rels.map fun r => r.map fun c =>
    Nat.rec (motive := fun _ => Nat) 2 (fun k _ => Nat.rec (motive := fun _ => Nat) 3
      (fun k' _ => Nat.rec (motive := fun _ => Nat) 0 (fun k'' _ => Nat.rec (motive := fun _ => Nat)
        1 (fun j _ => j + 4) k'') k') k) c) 0) = true := by
  quickRfl

end CFSG.KAct.P2004

end
