module

public import Certificates.Kernel.J2Dc.IdxGCheck
public import CFSG.Quasithin.Background.E2TwoProofSporJ2KInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public noncomputable section

namespace CFSG.KD.J2Dc

open CFSG.KC.SLDc CFSG.KC.IdxG CFSG.KC.LQT.PW CFSG.Quasithin.E2P.SporB.J2Lat

@[expose] noncomputable def OtD (j : Nat) : CFSG.QuasithinUnique.Ch1.SporLat.OmegaData (List (List Nat)) :=
  omL (J2K.Ot.getD j default)

@[expose] noncomputable def otOK (j : Nat) : Bool :=
  omOKG (fun l X => X.map (codeSetT 315 (sT.toArray.getD l #[]))) (Om j).lbl.toList 3 (OtD j)

@[expose] noncomputable def gensB (j jj : Nat) : Bool :=
  (J.mw.getD j []).all fun w => (Om jj).lbl.toList.contains (codeSetF 315 (imgW 9 (wW w)) Δc)

@[expose] noncomputable def nnB (j : Nat) : Bool :=
  (Om j).lbl.toList.any fun ℓ => sT.any fun s => !(codeSetT 315 s ℓ == ℓ)

theorem mw_eqD : J2K.mw = J.mw := rfl

theorem om_eqD : J2K.Om = J.Om := rfl

theorem ot_ok : (List.range 5).all otOK = true := by quickRfl

theorem gens13 : gensB 1 3 = true := by quickRfl

theorem gens42 : gensB 4 2 = true := by quickRfl

theorem nn4 : nnB 4 = true := by quickRfl

end CFSG.KD.J2Dc

end
