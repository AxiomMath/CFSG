module

public import Certificates.Data.Kernel.U52.PtLn
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Kernel.U52.ChainX
public import Certificates.Kernel.Misc.Perm.CharsCat
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs3
public meta import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs3
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars_cat CFSG.KC.U52PL.PtsT CFSG.ASVolI.burnsideF48t_u52PtStr
#kmisc_hexflat CFSG.KC.U52PL.PtsT CFSG.ASVolI.burnsideF48t_u52PtStr 1 5 2 165
#kmisc_packarrs CFSG.KC.U52PL.LP CFSG.ASVolI.burnsideF48t_u52LnPts 8
#kmisc_packarrs CFSG.KC.U52PL.UP CFSG.ASVolI.burnsideF48t_u52U 2

namespace CFSG.KC.U52PL

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum CertificateChecks.KernelU52

@[expose] noncomputable def charsK (cs : List Char) : Bool :=
  bAnd(Nat.beq cs.length (nat_lit 825),
    List.rec (motive := fun _ => Bool) true
      (fun c _ ih => bAnd(Nat.blt (Char.toNat c) (nat_lit 58), ih)) cs)

theorem chars_ok : charsK PtsT.chars = true := by
  decide +kernel

theorem pts_ok : ptsK PtsT.F = true := by
  quickRfl

theorem lp_bind : allN 297 (fun l => arrBind burnsideF48t_u52LnPts[l]! 5 8 (LP l)) = true := by
  decide +kernel

theorem up_bind : allN 6 (fun k => arrBind burnsideF48t_u52U[k]! 5 2 (UP k)) = true := by
  decide +kernel

theorem lns_ok : lnsK LP = true := by
  quickRfl

theorem gens_ok : gensK CX.S UP PtsT.F LP = true := by
  quickRfl

theorem iso_ok : isoK UP = true := by
  decide +kernel

example : ptNorm (scK 2 (PtsT.F 5)) = false := by
  decide +kernel

example : ptsK (fun i => if i = 7 then PtsT.F 3 else PtsT.F i) = false := by
  decide +kernel

example : lnsK (fun l => if l = 9 then LP 4 else LP l) = false := by
  decide +kernel

example : allN 165 (fun i => genPt CX.S (fun k => if k = 0 then UP 1 else UP k) PtsT.F 0 i) =
    false := by
  decide +kernel

example : allN 297 (fun l => genLn CX.S (fun l => if l = 0 then LP 0 + 1 else LP l) 0 l) =
    false := by
  decide +kernel

example : isoK (fun k => if k = 2 then 1 else UP k) = false := by
  decide +kernel

end CFSG.KC.U52PL

end
