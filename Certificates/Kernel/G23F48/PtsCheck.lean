module

public import Certificates.Kernel.G23F48.A22Check
public import Certificates.Kernel.G23F48.FrameCheck
public import Certificates.Kernel.Misc.Perm.CharsCat
public import Certificates.Data.Kernel.G23F48.Pts
public meta import CFSG.Milestones.ASVolI.F48.Rest.G23Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars_cat CFSG.KC.G23F48.PtsT CFSG.ASVolI.burnsideF48t_g23PtsStr
#kmisc_hexflat CFSG.KC.G23F48.PtsT CFSG.ASVolI.burnsideF48t_g23PtsStr 1 14 2 728

namespace CFSG.KC.G23F48

open CFSG.ASVolI

meta def matsM : Array (Array Nat) := burnsideF48t_g23Mats ()

end CFSG.KC.G23F48

#kmisc_packarrs CFSG.KC.G23F48.MP CFSG.KC.G23F48.matsM 2

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum

theorem m_bind : allN 4 (fun k => arrBind (burnsideF48t_g23Mats ())[k]! 196 2 (MP k)) = true := by
  decide +kernel

theorem pts_ok : ptsK PtsT.F = true := by
  quickRfl

theorem gens_ok : gensK GP MP PtsT.F = true := by
  quickRfl

theorem frame_bind : allN 15 (fun i => arrBind frameVecs[i]! 14 2 (PtsT.F frameIdx[i]!)) = true := by
  decide +kernel

example : ptNormK (pmk 14 2 fun c => 2 * pg 2 (mask 2) (PtsT.F 5) c % 3) = false := by
  decide +kernel

example : ptsK (fun i => if i = 7 then PtsT.F 3 else PtsT.F i) = false := by
  decide +kernel

example : allN 728 (fun i => genK (GP 0) (MP 1) PtsT.F i) = false := by
  decide +kernel

end CFSG.KC.G23F48

end
