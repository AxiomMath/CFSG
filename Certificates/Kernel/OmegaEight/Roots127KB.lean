module

public import Certificates.Kernel.OmegaEight.Roots127K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight

@[expose] noncomputable def r127Look (d : Nat) : Bool :=
  strictB (ycK saCodes yIdxT) fun YP => strictB (tyLK YP r127Ty 1) fun L1 =>
  strictB (tyLK YP r127Ty 2) fun L2 =>
  allN (nat_lit 38) fun k => strictB (saAtK YP k) fun s =>
    bAnd(bIf(Nat.beq (r127Ty k) (nat_lit 1), Nat.beq (lookL L1 s) (Nat.add k d), true),
      bIf(Nat.beq (r127Ty k) (nat_lit 2), Nat.beq (lookL L2 s) (Nat.add k d), true))

theorem kY127 : strictB (ycK saCodes yIdxT) (fun YP => allN (nat_lit 38) fun k =>
    Nat.beq (saAtK YP k) (saAtK saCodes (ix13 yIdxT k))) = true := by quickRfl

theorem kLook127 : r127Look 1 = true := by quickRfl

theorem neg127Look : Bool.not (r127Look 2) = true := by quickRfl

end CertificateChecks.KernelO8

end
