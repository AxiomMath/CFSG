module

public import Certificates.Data.Kernel.SuzDc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.SuzDc2

open CFSG.KC.SLD2 CFSG.KC.SLDc

theorem glob : globOK C D = true := by
  quickRfl

theorem frest : fRestOK C D = true := by
  quickRfl

theorem rootIdx : rootIdxOK C D = true := by
  quickRfl

theorem rec2s : (List.range D.R1.length).all (rec2OK C D) = true := by
  quickRfl

theorem nbo : Nat.beq D.bo.length 4 = true := by
  quickRfl

theorem nR1 : Nat.beq D.R1.length 106 = true := by
  quickRfl

theorem nroots : Nat.beq D.roots.length 40 = true := by
  quickRfl

theorem shape : shapeOK = true := by
  quickRfl

theorem sepB : (D.sep == [0, 1, 2, 3, 4, 5]) = true := by
  quickRfl

theorem sbHead : (chunksOK SB.B SB.C && (SB.C.flatten.headD [] == [0, 1, 2, 3, 4, 5]) &&
    Nat.beq SB.rows.length 5) = true := by
  quickRfl

theorem sbRowLen :
    (List.range 5).all (fun l => Nat.beq (SB.rows.getD l []).length SB.C.flatten.length) =
      true := by
  quickRfl

theorem sbTreeLen : (Nat.beq SB.par.length SB.C.flatten.length &&
    Nat.beq SB.via.length SB.C.flatten.length) = true := by
  quickRfl

theorem sbOrd : (Nat.beq SB.ord.length SB.C.flatten.length &&
    SB.ord.all (fun i => Nat.blt i SB.C.flatten.length)) = true := by
  quickRfl

theorem sbSize : (SB.C.flatten.length == 8192) = true := by
  quickRfl

@[expose] def bo1 (i : Nat) : Bool := borbOK C D (D.bo.getD i default)

@[expose] def fr1 (i : Nat) : Bool := fRowOK C D i

@[expose] def rt1 (b : Nat) : Bool := rootsOK C D b

end CFSG.KD.SuzDc2

#lc_blocks CFSG.KD.SuzDc2.BOB CFSG.KD.SuzDc2.bo1 4 1

#lc_blocks CFSG.KD.SuzDc2.FRB CFSG.KD.SuzDc2.fr1 6 1

#lc_blocks CFSG.KD.SuzDc2.RTB CFSG.KD.SuzDc2.rt1 40 5

end
