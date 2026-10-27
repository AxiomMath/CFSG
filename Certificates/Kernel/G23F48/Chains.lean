module

public import CFSG.Milestones.ASVolI.F48.Rest.G23Inputs
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.G23F48.Words
public meta import CFSG.Milestones.ASVolI.F48.Rest.G23Inputs
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Milestones.ASVolI.F48.Rest.G23Pres
public import CFSG.Milestones.ASVolI.F48.Rest.G23Pres
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.KC.G23F48

open CFSG.ASVolI

meta def s0S : Array (Array Nat) :=
  CFSG.Sporadic.HNOddCore.strongArrs 728 (burnsideF48t_g23S0Arr ()) burnsideF48t_g23WS0

meta def s0BA : Array Nat := (burnsideF48t_g23BaseS0.map Fin.val).toArray

@[expose] def s0D : List (List Int) :=
  (burnsideF48t_g23WS0.extract 3 burnsideF48t_g23WS0.size).toList

meta def kS : Array (Array Nat) :=
  CFSG.Sporadic.HNOddCore.strongArrs 728 (burnsideF48t_g23KArr ()) burnsideF48t_g23WK

meta def kBA : Array Nat := (burnsideF48t_g23BaseK.map Fin.val).toArray

@[expose] def kD : List (List Int) :=
  (burnsideF48t_g23WK.extract 2 burnsideF48t_g23WK.size).toList

meta def lInvM : Array (Array Nat) := burnsideF48t_g23LInv ()

end CFSG.KC.G23F48

end

set_option maxRecDepth 400000

#ks_rawchain CFSG.KC.G23F48.S0C 728 10 64 CFSG.KC.G23F48.s0S CFSG.KC.G23F48.s0BA 3
  CFSG.KC.G23F48.s0D

#ks_rawchain CFSG.KC.G23F48.KCh 728 10 64 CFSG.KC.G23F48.kS CFSG.KC.G23F48.kBA 2
  CFSG.KC.G23F48.kD

#kmisc_packarrs CFSG.KC.G23F48.LP CFSG.ASVolI.burnsideF48t_g23LArr 10
#kmisc_packarrs CFSG.KC.G23F48.LPI CFSG.KC.G23F48.lInvM 10

public section

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

theorem l_bind : allN 4 (fun i => arrBind burnsideF48t_g23LArr[i]! 728 10 (LP i)) = true := by
  decide +kernel

theorem l_perm : allN 4 (fun i => permOK 728 10 (mask 10) (728 * 10) (LP i) (LPI i)) = true := by
  quickRfl

theorem s0_words : allN 3 (fun j => Nat.beq (evP 728 10 LP LPI (burnsideF48t_g23SW.getD j []))
    (S0C.S j)) = true := by
  decide +kernel

theorem s0_base : allN 3 (fun t => Nat.beq (pg 10 (mask 10) S0C.BP t)
    ((burnsideF48t_g23BaseS0.map Fin.val).toArray[t]!)) = true := by
  decide +kernel

theorem s0_perm : allN 6 (fun j => permOK 728 10 (mask 10) (728 * 10) (S0C.S j) (S0C.SI j)) =
    true := by
  quickRfl

theorem s0_sizes : (List.range 3).map (fun i => rcnt (S0C.LR i)) = burnsideF48t_g23SizesS0 := by
  decide +kernel

theorem k_words : allN 2 (fun j => Nat.beq (evP 728 10 LP LPI (burnsideF48t_g23KW.getD j []))
    (KCh.S j)) = true := by
  decide +kernel

theorem k_base : allN 3 (fun t => Nat.beq (pg 10 (mask 10) KCh.BP t)
    ((burnsideF48t_g23BaseK.map Fin.val).toArray[t]!)) = true := by
  decide +kernel

theorem k_perm : allN 3 (fun j => permOK 728 10 (mask 10) (728 * 10) (KCh.S j) (KCh.SI j)) =
    true := by
  quickRfl

theorem k_sizes : (List.range 3).map (fun i => rcnt (KCh.LR i)) = burnsideF48t_g23SizesK := by
  decide +kernel

end CFSG.KC.G23F48

end
