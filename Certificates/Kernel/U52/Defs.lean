module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs

public section

namespace CertificateChecks.KernelU52

open CFSG.ASVolI CFSG.Sporadic.HNOddCore

@[expose] def u52LI : Array (Array Nat) := burnsideF48t_u52LInv ()

@[expose] def u52SX : Array (Array Nat) := strongArrs 462 (burnsideF48t_u52Gens ()) burnsideF48t_u52WX
@[expose] def u52SP1 : Array (Array Nat) := strongArrs 462 burnsideF48t_u52P1Arr burnsideF48t_u52WP1
@[expose] def u52SP2 : Array (Array Nat) := strongArrs 462 burnsideF48t_u52P2Arr burnsideF48t_u52WP2
@[expose] def u52SB : Array (Array Nat) := strongArrs 462 burnsideF48t_u52BArr burnsideF48t_u52WB
@[expose] def u52SS0 : Array (Array Nat) :=
  strongArrs 462 (burnsideF48t_u52S0Arr ()) burnsideF48t_u52WS0
@[expose] def u52SK : Array (Array Nat) := strongArrs 462 (burnsideF48t_u52KArr ()) burnsideF48t_u52WK

@[expose] def u52BX : Array Nat := (burnsideF48t_u52BaseX.map Fin.val).toArray
@[expose] def u52BP1 : Array Nat := (burnsideF48t_u52BaseP1.map Fin.val).toArray
@[expose] def u52BP2 : Array Nat := (burnsideF48t_u52BaseP2.map Fin.val).toArray
@[expose] def u52BB : Array Nat := (burnsideF48t_u52BaseB.map Fin.val).toArray
@[expose] def u52BS0 : Array Nat := (burnsideF48t_u52BaseS0.map Fin.val).toArray
@[expose] def u52BK : Array Nat := (burnsideF48t_u52BaseK.map Fin.val).toArray

@[expose] def u52DX : List (List Int) := burnsideF48t_u52WX.toList.drop 6
@[expose] def u52DP1 : List (List Int) := burnsideF48t_u52WP1.toList.drop 3
@[expose] def u52DP2 : List (List Int) := burnsideF48t_u52WP2.toList.drop 3
@[expose] def u52DB : List (List Int) := burnsideF48t_u52WB.toList.drop 2
@[expose] def u52DS0 : List (List Int) := burnsideF48t_u52WS0.toList.drop 4
@[expose] def u52DK : List (List Int) := burnsideF48t_u52WK.toList.drop 2

end CertificateChecks.KernelU52

end
