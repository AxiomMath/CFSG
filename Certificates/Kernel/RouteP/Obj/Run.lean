module

public import Certificates.Kernel.RouteP.Obj.Rep
public import Certificates.Kernel.RouteP.Lines.ObjL
public import Certificates.Kernel.RouteP.Link.Glue

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

#kc_forall_tree olckL_all (fun g => CFSG.KD.RouteP.olckL g = true) 1120 CFSG.KD.RouteP.ObjLC.o

theorem objW_eq : objLinesK = CFSG.KD.RouteP.ObjW.OL :=
  eq_of_beq (by decide +kernel : (objLinesK == CFSG.KD.RouteP.ObjW.OL) = true)

theorem olck_all : ∀ g < 1120, CFSG.KD.RouteP.olck g = true := by
  intro g hg
  unfold CFSG.KD.RouteP.olck
  rw [objW_eq]
  exact olckL_all g hg

theorem objLines_factors : ∀ ℓ < 56, ∀ z ∈ lineW 0 objLinesK.toArray[ℓ]!, z.natAbs - 1 < 58 := by
  decide +kernel

theorem objRun_rep : ∀ r < 58, Rep 920808 (objRun ()).1[r]! (gO r) :=
  objRep_of objLines_eq mTabs_O objProg_ok objLines_linesOK (by rw [← objLines_eq]; exact objLines_size)
    objLines_factors olck_all

end CertificateChecks.KernelRouteP

end
