module

public import Certificates.Kernel.GammaU.Census0Data
public import Certificates.Kernel.GammaU.Census1Data
public import Certificates.Data.Kernel.GammaUCensusBK
public import Certificates.Data.Kernel.GammaUSigmaK
public import CFSG.GF2Type.Smith1979.GammaU.StepCInputs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.GUCB

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KC.GUS CFSG.GF2Type.Smith1979.GammaU.StepA

theorem cb16966_gens : ∀ c < 32, ∀ l < 5, look CFSG.KD.GUC0.CG (5 * c + l) =
    bif c.testBit l then mulP (packR k0) (packR cBasis[l]!) else packR cBasis[l]! := by
  decide +kernel

theorem cb16966_th : CFSG.KD.GUC0.TH = packR theta0R := by decide +kernel

theorem cb16966_rows : rowsOK k0.toList = true ∧ (∀ l < 5, rowsOK cBasis[l]!.toList = true) ∧
    rowsOK theta0R.toList = true := by
  decide +kernel

theorem cb16966_cg : cgOK CFSG.KD.GUC0.CG = true := by decide +kernel

theorem cb16966_eq : (Nat.beq CFSG.KD.GUC1.CG CFSG.KD.GUC0.CG &&
    Nat.beq CFSG.KD.GUC1.CGI CFSG.KD.GUC0.CGI && Nat.beq CFSG.KD.GUC1.TH CFSG.KD.GUC0.TH) = true := by
  decide +kernel

end CFSG.KD.GUCB

end
