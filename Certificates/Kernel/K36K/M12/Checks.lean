module

public import Certificates.Kernel.K36K.M12.Data
public import Certificates.Data.Kernel.K36K.Planes
public import Certificates.Data.Kernel.K36K.Exc
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.K36SporM12
public import Mathlib.Data.Fintype.Card
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 10

namespace CertificateChecks.KernelK36K.M12

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MaxD2 CFSG.KS.CoreD2K
  CFSG.KS.K36K
open Certificates.CoreD2Perm Certificates.K36Spor

abbrev mX0 : Exc := m12SData.exc.getD 0 default

abbrev mX1 : Exc := m12SData.exc.getD 1 default

theorem k_sz : szOK 12 4 = true := by quickRfl
theorem k_gp : allN 2 (fun j => permOK 12 4 (mask 4) (12 * 4) (GP j) (GPI j)) = true := by
  quickRfl
theorem k_gens : gensK 12 4 (vOf m12SData) GP GPI RE.G GT GTI = true := by quickRfl
theorem k_ek : Nat.beq RE.k m12SData.base.eW.length = true := by quickRfl
theorem k_eh : penumHdK (pidn 12 4) RE.cnt 27 RE.T RE.PL = true := by quickRfl
theorem k_ecnt : Nat.beq RE.cnt 27 = true := by quickRfl
theorem k_esl : penumSlK 12 4 (mask 4) (12 * 4) false RE.G RE.GI RE.k RE.cnt RE.T RE.PL RE.POS
    RE.SRT RE.SRI 0 27 = true := by quickRfl
theorem k_nab : nabK 12 4 m12SData.base.eW.length RE.G = true := by quickRfl
theorem k_cen : cenK 12 4 m12SData.base.p m12SData.base.eW.length RE.G = true := by quickRfl
theorem k_lines : linesK 12 4 m12SData.base.p (vOf m12SData) RE.G = true := by quickRfl
theorem k_cent : centSK 12 4 m12SData RE.G GT = true := by quickRfl
theorem k_words : wordsSK 12 4 m12SData GP GT GTI = true := by quickRfl

theorem k0_exc : excWK 12 4 m12SData mX0 RE.G GP GPI RN0.G RN0.GI (Y0 0) (Y0I 0) F0 FY0 =
    true := by quickRfl
theorem k0_nk : Nat.beq RN0.k mX0.cW.length = true := by quickRfl
theorem k0_h : penumHdK (pidn 12 4) RN0.cnt 432 RN0.T RN0.PL = true := by quickRfl
theorem k0_cnt : Nat.ble RN0.cnt 432 = true := by quickRfl
theorem k0_sl : penumSlK 12 4 (mask 4) (12 * 4) false RN0.G RN0.GI RN0.k RN0.cnt RN0.T RN0.PL
    RN0.POS RN0.SRT RN0.SRI 0 432 = true := by quickRfl
theorem k0_N : excNK 12 4 3 54 (RE.G 0) (RE.G (m12SData.ys.getD mX0.idx 0)) mX0.cW.length RN0.G
    RN0.cnt RN0.T = true := by quickRfl
theorem k0_fix3 : ∀ α < 3, ∀ β < 3, ¬(α = 0 ∧ β = 0) → (Finset.univ.filter fun x : Fin 12 =>
    pg 4 (mask 4) (pcomp 12 4 (mask 4) (pw 12 4 (RE.G 0) α)
      (pw 12 4 (RE.G (m12SData.ys.getD mX0.idx 0)) β)) x = (x : ℕ)).card = 3 := by
  decide +kernel
theorem k0_W : fixWK 12 4 2 F0 W.x0k0 W.x0o0 W.x0HW W.x0OL W.x0OW = true := by quickRfl
theorem k0_O : 5 ≤ (Finset.univ.filter fun x : Fin 12 => (x : ℕ) ∈ W.x0OL).card := by
  decide +kernel

theorem k1_exc : excWK 12 4 m12SData mX1 RE.G GP GPI RN1.G RN1.GI (Y1 0) (Y1I 0) F1 FY1 =
    true := by quickRfl
theorem k1_nk : Nat.beq RN1.k mX1.cW.length = true := by quickRfl
theorem k1_h : penumHdK (pidn 12 4) RN1.cnt 432 RN1.T RN1.PL = true := by quickRfl
theorem k1_cnt : Nat.ble RN1.cnt 432 = true := by quickRfl
theorem k1_sl : penumSlK 12 4 (mask 4) (12 * 4) false RN1.G RN1.GI RN1.k RN1.cnt RN1.T RN1.PL
    RN1.POS RN1.SRT RN1.SRI 0 432 = true := by quickRfl
theorem k1_N : excNK 12 4 3 54 (RE.G 0) (RE.G (m12SData.ys.getD mX1.idx 0)) mX1.cW.length RN1.G
    RN1.cnt RN1.T = true := by quickRfl
theorem k1_fix3 : ∀ α < 3, ∀ β < 3, ¬(α = 0 ∧ β = 0) → (Finset.univ.filter fun x : Fin 12 =>
    pg 4 (mask 4) (pcomp 12 4 (mask 4) (pw 12 4 (RE.G 0) α)
      (pw 12 4 (RE.G (m12SData.ys.getD mX1.idx 0)) β)) x = (x : ℕ)).card = 3 := by
  decide +kernel
theorem k1_W : fixWK 12 4 2 F1 W.x1k0 W.x1o0 W.x1HW W.x1OL W.x1OW = true := by quickRfl
theorem k1_O : 5 ≤ (Finset.univ.filter fun x : Fin 12 => (x : ℕ) ∈ W.x1OL).card := by
  decide +kernel

end CertificateChecks.KernelK36K.M12

end
