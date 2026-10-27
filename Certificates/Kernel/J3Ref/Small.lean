module

public import Certificates.Kernel.J3Ref.RecS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ3Ref

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.PEnumB
open CertificateChecks.KernelSpor

@[expose] noncomputable def tbI (i : Nat) : Nat :=
  nIf(Nat.beq i (nat_lit 0), J3CentI (nat_lit 9),
    nIf(Nat.blt i (nat_lit 11), J3ClsI (Nat.sub i (nat_lit 1)), J3CentI (Nat.sub i (nat_lit 1))))

@[expose] noncomputable def tbOK (i : Nat) : Bool :=
  bAnd(canonK 6156 13 (mask 13) (6156 * 13) (tbP i), bAnd(canonK 6156 13 (mask 13) (6156 * 13) (tbI i),
    invEqK 6156 13 (mask 13) (6156 * 13) (tbP i) (tbI i)))

theorem tbls_ok0 : allBlk 0 tbOK 8 = true := by quickRfl

theorem tbls_ok1 : allBlk 8 tbOK 8 = true := by quickRfl

theorem eb_ok : bAnd(ebL.all (sqB 13 (mask 13) bsJ), bAnd(ebL.all (fun b => ebL.all (commB 13 (mask 13) bsJ b)),
    allN 16 (fun c => bIf(Nat.beq c 0, true, !(spanEqB 13 (mask 13) bsJ ebL (pidn 6156 13) c))))) =
      true := by
  quickRfl

@[expose] noncomputable def masksB (g : Nat) (masks : List Nat) : Bool :=
  (ebL.zip masks).all fun p => spanCompB 13 (mask 13) bsJ ebL g p.1 g p.2

theorem masks_ok : bAnd(masksB (J3ClsP 3) [2, 3, 8, 12], bAnd(masksB (J3ClsP 5) [3, 1, 10, 15],
    masksB (J3ClsP 6) [10, 15, 3, 1])) = true := by
  quickRfl

@[expose] noncomputable def clsB (i : Nat) : Bool :=
  !(sqB 13 (mask 13) bsJ (J3RS.T i)) || anyMaskB 4 (spanEqB 13 (mask 13) bsJ ebL (J3RS.T i)) ||
    anyMaskB 4 (conjSpanB 13 (mask 13) bsJ ebL (J3ClsP 4) (J3RS.T i)) ||
    Nat.blt (cntBelowK J3RS.cnt (fun j => sqB 13 (mask 13) bsJ (J3RS.T j) &&
      commB 13 (mask 13) bsJ (J3RS.T j) (J3RS.T i)) 2) 16

theorem cls_ok0 : allBlk 0 clsB 64 = true := by quickRfl

theorem cls_ok1 : allBlk 64 clsB 64 = true := by quickRfl

end CertificateChecks.KernelJ3Ref

end
