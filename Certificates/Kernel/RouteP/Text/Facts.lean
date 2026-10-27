module

public import Certificates.Kernel.RouteP.Text.Texts
public import CFSG.Certificates.Kernel.RouteP.Slp

public section

namespace CertificateChecks.KernelRouteP

open CFSG.KC.RouteP CFSG.KS.RouteP CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

theorem presLines_size : (slpLines presText ++ slpLines bridgeText).size = 37 := by
  rw [presLines_eq]
  decide +kernel

theorem presProg_ok :
    progOK (2 + (slpLines presText ++ slpLines bridgeText).size + 1)
      (compileSLP 2 (slpLines presText ++ slpLines bridgeText)) = true := by
  rw [presLines_eq]
  decide +kernel

theorem bridgeGensLines_size : (slpLines bridgeGensText).size = 4 := by
  rw [bridgeGensLines_eq]
  decide +kernel

theorem bridgeGensProg_ok :
    progOK (11 + (slpLines bridgeGensText).size + 1) (compileSLP 11 (slpLines bridgeGensText)) =
      true := by
  rw [bridgeGensLines_eq]
  decide +kernel

theorem objLines_size : (objLines ()).size = 56 := by
  rw [objLines_eq]
  decide +kernel

theorem objProg_ok : progOK 59 (objProg ()) = true := by
  unfold objProg
  rw [objLines_eq]
  decide +kernel

theorem y332Lines_size : (y332Lines ()).size = 110 := by
  rw [y332Lines_eq]
  decide +kernel

theorem y332Prog_ok : progOK 113 (y332Prog ()) = true := by
  unfold y332Prog
  rw [y332Lines_eq]
  decide +kernel

@[expose] def linesOKB (g : Nat) (ls : Array (List Int)) : Bool :=
  (List.range ls.size).all fun l =>
    (pairsOf ls[l]!).all fun p => decide (1 ≤ p.1) && decide (p.1 ≤ g + l)

theorem linesOK_of {g : Nat} {ls : Array (List Int)} (h : linesOKB g ls = true) :
    CFSG.KS.RouteP.LinesOK g ls := by
  intro l hl p hp
  have := List.all_eq_true.1 (List.all_eq_true.1 h l (List.mem_range.2 hl)) p hp
  simpa using this

theorem presLines_linesOK : CFSG.KS.RouteP.LinesOK 2 (slpLines presText ++ slpLines bridgeText) :=
  linesOK_of (by rw [presLines_eq]; decide +kernel)

theorem bridgeGensLines_linesOK : CFSG.KS.RouteP.LinesOK 11 (slpLines bridgeGensText) :=
  linesOK_of (by rw [bridgeGensLines_eq]; decide +kernel)

theorem objLines_linesOK : CFSG.KS.RouteP.LinesOK 2 (objLines ()) :=
  linesOK_of (by rw [objLines_eq]; decide +kernel)

theorem y332Lines_linesOK : CFSG.KS.RouteP.LinesOK 2 (y332Lines ()) :=
  linesOK_of (by rw [y332Lines_eq]; decide +kernel)

end CertificateChecks.KernelRouteP
