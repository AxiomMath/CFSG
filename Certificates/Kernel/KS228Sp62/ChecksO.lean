module

public import Certificates.Data.Kernel.Sp62Pk
public import Certificates.Data.Kernel.Sp62W.Defs
public import Certificates.Kernel.KS228Sp62.Rec
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp62

open CFSG.KD.Sp62W

@[expose] noncomputable def st12646 : Nat → Nat → Nat := conjSt (at2 R12646 6) (at2 R12646 8)

@[expose] noncomputable def o12646B (j : Nat) : Bool :=
  allSl 48383 (bBody st12646 (recX R12646 2943) (recF R12646 2943 0) (recF R12646 2943 1) 2) j

@[expose] noncomputable def o12646S (j : Nat) : Bool :=
  allSl 96768 (sBody st12646 (recX R12646 2943) (recF R12646 2943 0) (recF R12646 2943 1)
    (recC R12646 2943) (recPOS R12646 2943) 48384 2) j

@[expose] noncomputable def o12646T (j : Nat) : Bool :=
  allSl 48384 (tBody (recX R12646 2943) (recF R12646 2943 2) (recF R12646 2943 3) 48384) j

theorem c12646orbK0 : (Nat.beq (recX R12646 2943 0) (R12646 10) &&
    Nat.beq (recC R12646 2943 0) 1 && Nat.beq (recC R12646 2943 96768) 48384) = true := by
  quickRfl

#kc_each o12646B 0 12
#kc_each o12646S 0 24
#kc_each o12646T 0 12

end CFSG.KD.Sp62

end
