module

public import Certificates.Data.Kernel.Fi23R.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23Pin13.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Pin13

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KD.Fi23K CFSG.KD.Fi23Pin13

theorem ch17403_y13 : eqB G (powW 13 wY) [] = true := by quickRfl

theorem ch17403_rel : eqB G (wG ++ wY) (powW 4 wY ++ wG) = true := by quickRfl

theorem ch17403_dy : eqB G (wY ++ [43]) ([43] ++ wY) = true := by quickRfl

theorem ch17403_d2 : eqB G [43, 43] [] = true := by quickRfl

theorem ch17403_mvY : Bool.not (Nat.beq (wa G wY 2) 2) = true := by quickRfl

theorem ch17403_mvD : Bool.not (Nat.beq (wa G [43] 2) 2) = true := by quickRfl

end CertificateChecks.KernelFi23Pin13

end
