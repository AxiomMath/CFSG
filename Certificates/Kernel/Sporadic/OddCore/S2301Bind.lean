
module

public import Certificates.Kernel.Sporadic.OddCore.S2301Data
public import Certificates.Kernel.Sporadic.OddCore.S2301Gens
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import Certificates.Data.Kernel.Suz2301
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2301

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.S2301 CFSG.KC.S2301
open CFSG.KS.Mathieu CertificateChecks.KernelSpor

theorem bind0 : bindK 1782 (GP 0) Suz2306.B0 = true := by quickRfl
theorem bind1 : bindK 1782 (GP 1) Suz2306.B1 = true := by quickRfl
theorem bind2 : bindK 1782 (GP 2) Suz2306.V = true := by quickRfl

theorem bindT0 : bindK 1782 (GP 3) (SuzTP 0) = true := by quickRfl
theorem bindT1 : bindK 1782 (GP 4) (SuzTP 1) = true := by quickRfl
theorem bindT2 : bindK 1782 (GP 5) (SuzTP 2) = true := by quickRfl
theorem bindT3 : bindK 1782 (GP 6) (SuzTP 3) = true := by quickRfl

theorem tlt0 : allN 1782 (fun v => Nat.blt (tg (GP 3) v) 1782) = true := by quickRfl
theorem tlt1 : allN 1782 (fun v => Nat.blt (tg (GP 4) v) 1782) = true := by quickRfl
theorem tlt2 : allN 1782 (fun v => Nat.blt (tg (GP 5) v) 1782) = true := by quickRfl
theorem tlt3 : allN 1782 (fun v => Nat.blt (tg (GP 6) v) 1782) = true := by quickRfl

theorem tp0 : Nat.beq (SuzTP 0) (SuzInvT0.F 0) = true := by quickRfl
theorem tp1 : Nat.beq (SuzTP 1) (SuzInvT1.F 0) = true := by quickRfl
theorem tp2 : Nat.beq (SuzTP 2) (SuzInvT2.F 0) = true := by quickRfl
theorem tp3 : Nat.beq (SuzTP 3) (SuzInvT3.F 0) = true := by quickRfl

theorem root : allN 416 (fun i => Nat.beq (rg (R 0) i) (nget invNeighbors i)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.S2301

end
