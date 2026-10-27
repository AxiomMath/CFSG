
module

public import Certificates.Kernel.Sporadic.OddCore.S2301Data
public import Certificates.Kernel.Sporadic.OddCore.S2301Gens
public import Certificates.Kernel.Sporadic.OddCore.S2301Rnd
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import Certificates.Data.Kernel.Suz2301
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2301Neg

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.S2301 CFSG.KC.S2301 CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.S2301

theorem n_mask : Bool.not (rowOK 1782 416 R (fun x => Nat.add (M x) 2) S 5) = true := by quickRfl
theorem n_spread : Bool.not (rowOK 1782 416 R M (fun x => Nat.add (S x) 1) 5) = true := by quickRfl
theorem n_row : Bool.not (rowOK 1782 416 (fun x => R (Nat.add x 1)) M S 5) = true := by quickRfl
theorem n_img : Bool.not (imgOK 1782 416 (GP 0) R (fun x => M (Nat.add x 1)) 7) = true := by
  quickRfl
theorem n_tree : Bool.not (treeOK 1782 2 GP (fun x => T (Nat.add x 1)) 9) = true := by quickRfl
theorem n_wmask : Bool.not (maskOK 416 R (fun x => W (Nat.add x 1)) 3) = true := by quickRfl
theorem n_round : Bool.not (roundOK 1782 (X 12) (Q 12) (X 14) (Q 14) (GP 3) (O 12) W) = true := by
  quickRfl
theorem n_roundT : Bool.not (roundOK 1782 (X 12) (Q 12) (X 13) (Q 13) (GP 4) (O 12) W) = true := by
  quickRfl
theorem n_roundO : Bool.not (ordOK 1782 (Q 12) (O 13)) = true := by quickRfl
theorem n_tab : Bool.not (tabOK 1782 (K 12) (X 13) (Q 13)) = true := by quickRfl
theorem n_ind : Bool.not (ind 15 638 3) = true := by quickRfl
theorem n_init : Bool.not (allN 1782 (initOK false (X 0) (Q 0) M (GP 3))) = true := by quickRfl
theorem n_bind : Bool.not (bindK 1782 (GP 1) Suz2306.B0) = true := by quickRfl
theorem n_inj : Bool.not (injOK 1782 (X 35) (Q 35) (O 35)) = true := by quickRfl

end CertificateChecks.KernelSpor.S2301Neg

end
