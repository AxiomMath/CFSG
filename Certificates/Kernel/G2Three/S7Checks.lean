module

public import Certificates.Data.Kernel.G2Three.S7
public import Certificates.Data.S7G23
public import Certificates.Kernel.G2Three.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three

open Certificates.S7G23

@[expose] noncomputable def s7CW : List (Nat × Nat) :=
  conjW.map fun w => (s7Word GA w, s7WordInv GA w)

theorem s7517003_ok :
    s7K (XO 0) (s7Word GA i1W) (s7Word GA j1W) (s7Word GA i2W) (s7Word GA j2W) s7CW
      ((List.range 64).map XS) ((List.range 576).map XX) = true := by quickRfl

end CFSG.KD.G2Three

end
