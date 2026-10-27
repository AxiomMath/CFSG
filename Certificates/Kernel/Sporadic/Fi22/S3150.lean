
module

public import Certificates.Kernel.Sporadic.Fi22.X2069P
public import Certificates.Kernel.Sporadic.Fi22.X2069Ext
public import Certificates.Kernel.Sporadic.Fi22.L3150M
public import Certificates.Kernel.Sporadic.Fi22.R3150M
public import Certificates.Kernel.Sporadic.Fi22.R3150T
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22S3150

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 3510 12 (mask 12) (3510 * 12) p

@[expose] noncomputable def siftP (G : Nat) : Bool :=
  siftK 3510 12 (mask 12) (3510 * 12) (pidn 3510 12) Fi22PC.LR Fi22PC.TRI Fi22PC.BP 6 0 G

theorem sM : allN 17 (fun j => Nat.beq (Fi22MR.S j) (Fi22M3.MS j)) = true := by quickRfl
theorem sT : allN 13 (fun j => Nat.beq (Fi22TR.S j) (Fi22X.TS j)) = true := by quickRfl
theorem baseM : allN 6 (fun t => Nat.beq (#[0, 1, 2, 6, 4, 3] : Array Nat)[t]!
    (pg 12 (mask 12) Fi22MR.BP t)) = true := by quickRfl
theorem baseT : allN 6 (fun t => Nat.beq (#[0, 1, 2, 3, 6, 4] : Array Nat)[t]!
    (pg 12 (mask 12) Fi22TR.BP t)) = true := by quickRfl
theorem cnM : allN 3 (fun k => cn (Fi22M3.MS k)) = true := by quickRfl
theorem cnT : allN 9 (fun k => cn (Fi22X.TS k)) = true := by quickRfl
theorem siftM : allN 3 (fun k => siftP (Fi22M3.MS k)) = true := by quickRfl
theorem siftT : allN 9 (fun k => siftP (Fi22X.TS k)) = true := by quickRfl
theorem fixM : allN 3 (fun k => Nat.beq (pg 12 (mask 12) (Fi22M3.MS k) 0) 0) = true := by quickRfl
theorem orbM : (List.range 6).map (fun i => rcnt (Fi22MR.LR i)) = [1, 2816, 567, 320, 18, 2] := by
  decide +kernel
theorem orbT : (List.range 6).map (fun i => rcnt (Fi22TR.LR i)) = [1024, 32, 4, 1, 1, 1] := by
  decide +kernel

end CertificateChecks.KernelSpor.Fi22S3150

end
