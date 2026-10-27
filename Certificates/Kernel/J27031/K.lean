module

public import Certificates.Kernel.J27031.M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.DcKN

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.J27031.CK

open CFSG.KC.DcK

@[expose] noncomputable def dSl (lo len : Nat) : Bool :=
  (List.range' lo len).all fun i => (List.range K.reps.size).all fun j =>
    decide (j ≤ i) || IV.getD i 0 != IV.getD j 0 || K.noHitKT xt xti i j (PN i j)

@[expose] noncomputable def hSl (lo len : Nat) : Bool :=
  (List.range' lo len).all fun j => K.hitT xt xti j == some (HitV.getD j 0)

theorem inv : K.invOK = true := by quickRfl
theorem basic : K.basicOK = true := by quickRfl
theorem lab : K.labOK = true := by quickRfl
theorem size : (K.reps.size == 63 && IV.length == 63 && HitV.length == 63) = true := by quickRfl
theorem invs : (List.range K.reps.size).all (fun j => K.inv j == IV.getD j 0) = true := by quickRfl
theorem t0 : K.tabsOK xt xti 0 21 = true := by quickRfl
theorem t1 : K.tabsOK xt xti 21 21 = true := by quickRfl
theorem t2 : K.tabsOK xt xti 42 21 = true := by quickRfl
theorem d0 : dSl 0 9 = true := by quickRfl
theorem d1 : dSl 9 9 = true := by quickRfl
theorem d2 : dSl 18 9 = true := by quickRfl
theorem d3 : dSl 27 9 = true := by quickRfl
theorem d4 : dSl 36 9 = true := by quickRfl
theorem d5 : dSl 45 9 = true := by quickRfl
theorem d6 : dSl 54 9 = true := by quickRfl
theorem edges : K.edgesOK = true := by quickRfl
theorem vs : K.vsOK = true := by quickRfl
theorem h0 : hSl 0 9 = true := by quickRfl
theorem h1 : hSl 9 9 = true := by quickRfl
theorem h2 : hSl 18 9 = true := by quickRfl
theorem h3 : hSl 27 9 = true := by quickRfl
theorem h4 : hSl 36 9 = true := by quickRfl
theorem h5 : hSl 45 9 = true := by quickRfl
theorem h6 : hSl 54 9 = true := by quickRfl
theorem mass : K.massOK HitV = true := by quickRfl

end CFSG.KD.J27031.CK

end
