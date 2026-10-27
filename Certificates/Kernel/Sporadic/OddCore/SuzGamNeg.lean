module

public import Certificates.Kernel.Sporadic.OddCore.SuzGamS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore.SGam

open CFSG.KC.Enum CFSG.KC.G2294 CertificateChecks.KernelSpor

@[expose] noncomputable def rej (b : Bool) : Bool := bIf(b, false, true)

theorem neg_round : rej (roundOK 280 SuzGamR (SuzGamC 1) (SuzGamC 13) (Nat.add (SuzGamC 2) 1) 0) =
    true := by quickRfl

theorem neg_hash : rej (hashOK (SuzGamC 1) (Nat.add (SuzGamC 13) 1) 0) = true := by quickRfl

theorem neg_img : rej (imgOK 22880 280 (Nat.add (SuzGamG 0) 1) SuzGamR 0) = true := by quickRfl

theorem neg_row : rej (rowOK 22880 280 (fun x => Nat.lor (SuzGamR x) 65535) 7) = true := by
  quickRfl

theorem neg_tree : rej (treeOK 22880 2 SuzGamG (fun x => Nat.add (SuzGamT x) 1) 9) = true := by
  quickRfl

theorem neg_sym : rej (sym0OK (fun x => Nat.lor (SuzGamR x) 1) 0) = true := by quickRfl

theorem neg_init : rej (initOK (SuzGamC 3) 0) = true := by quickRfl

theorem neg_base : rej (allN 64 (baseOK (mv (SuzGamG 0) (SuzGamG 1) 1) (SuzGamC 7) (SuzGamC 3)
    (SuzGamC 8))) = true := by quickRfl

theorem neg_cell : rej (strictB (SuzGamC 4) fun C => Nat.ble (cellCnt 22880 C (cs C 1)) 8504) =
    true := by quickRfl

theorem neg_inj : rej (strictB (SuzGamC 9) fun C => strictB (SuzGamO 0) fun P => injK 22880 C P) =
    true := by quickRfl

end CertificateChecks.KernelSpor.OddCore.SGam

end
