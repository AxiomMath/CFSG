module

public import Certificates.Kernel.LocalQT.Small.C4035
public import CFSG.Certificates.Kernel.LocalQTM11Base
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11CheckInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadM11Inputs

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4035

open CFSG.KC.LQT.X6 CFSG.QuasithinUnique.A5.Aut6

theorem p0 : p4035 wordTab R LA LXs LY 167906369 4294817 0 = true := by quickRfl
theorem p1 : p4035 wordTab R LA LXs LY 167906369 4294817 1 = true := by quickRfl
theorem p2 : p4035 wordTab R LA LXs LY 167906369 4294817 2 = true := by quickRfl
theorem p3 : p4035 wordTab R LA LXs LY 167906369 4294817 3 = true := by quickRfl
theorem p4 : p4035 wordTab R LA LXs LY 167906369 4294817 4 = true := by quickRfl
theorem p5 : p4035 wordTab R LA LXs LY 167906369 4294817 5 = true := by quickRfl
theorem p6 : p4035 wordTab R LA LXs LY 167906369 4294817 6 = true := by quickRfl
theorem p7 : p4035 wordTab R LA LXs LY 167906369 4294817 7 = true := by quickRfl
theorem p8 : p4035 wordTab R LA LXs LY 167906369 4294817 8 = true := by quickRfl
theorem p9 : p4035 wordTab R LA LXs LY 167906369 4294817 9 = true := by quickRfl
theorem p10 : p4035 wordTab R LA LXs LY 167906369 4294817 10 = true := by quickRfl
theorem hp : ∀ i < LXs.length, p4035 wordTab R LA LXs LY 167906369 4294817 i = true :=
  CFSG.KC.LQT.M.forall_lt_11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10

end CFSG.KD.LQT.C4035

end
