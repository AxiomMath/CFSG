module

public import Certificates.Data.Kernel.TwoM22.Check
public import Certificates.Data.Kernel.TwoM22.Data

public section

namespace CertificateChecks.TwoM22K

open CFSG.KC.Enum CFSG.KC.TwoM22 CFSG.KD.TwoM22

theorem perm_a : permOK 660 10 1023 6600 a ai = true := by decide +kernel
theorem perm_b : permOK 660 10 1023 6600 b bi = true := by decide +kernel
theorem perm_t : permOK 660 10 1023 6600 t t = true := by decide +kernel
theorem perm_a22 : permOK 22 5 31 110 a22 ai22 = true := by decide +kernel
theorem perm_b22 : permOK 22 5 31 110 b22 bi22 = true := by decide +kernel
theorem rel660 : relOK 660 10 1023 a b ai bi cover = true := by decide +kernel
theorem rel22 : relOK 22 5 31 a22 b22 ai22 bi22 cover = true := by decide +kernel

theorem zeta_zero : Nat.beq (wpt 10 1023 a b ai bi z11.1 z11.2 0) 635 = true := by decide +kernel
theorem zeta_635 : Nat.beq (wpt 10 1023 a b ai bi z11.1 z11.2 635) 0 = true := by decide +kernel
theorem zeta_sq : wordId 660 10 1023 a b ai bi z22.1 z22.2 = true := by decide +kernel
theorem zeta22 : wordId 22 5 31 a22 b22 ai22 bi22 z11.1 z11.2 = true := by decide +kernel

theorem conj_a : conjOK 660 10 1023 a b ai bi t a wa.1 wa.2 = true := by decide +kernel
theorem conj_b : conjOK 660 10 1023 a b ai bi t b wb.1 wb.2 = true := by decide +kernel
theorem conj_a22 : conjOK 22 5 31 a22 b22 ai22 bi22 t22 a22 wa.1 wa.2 = true := by decide +kernel
theorem conj_b22 : conjOK 22 5 31 a22 b22 ai22 bi22 t22 b22 wb.1 wb.2 = true := by decide +kernel

theorem tree660 : treeOK 660 10 1023 a b tr660 = true := by decide +kernel
theorem tree22 : treeOK 22 5 31 a22 b22 tr22 = true := by decide +kernel

theorem fix660 : fix2OK 660 10 1023 a b ai bi h660.1 h660.2 0 635 = true := by decide +kernel
theorem fix22 : fix1OK 22 5 31 a22 b22 ai22 bi22 k22 0 = true := by decide +kernel

theorem sgen660 : allN 4 (fun j => wordEqOK 660 10 1023 a b ai bi (g660.getD j 0)
    (sw.getD j (0, 0)).1 (sw.getD j (0, 0)).2) = true := by decide +kernel
theorem sgen22 : allN 4 (fun j => wordEqOK 22 5 31 a22 b22 ai22 bi22 (g22.getD j 0)
    (sw.getD j (0, 0)).1 (sw.getD j (0, 0)).2) = true := by decide +kernel
theorem t0_660 : wordMulOK 660 10 1023 a b ai bi (g660.getD 4 0) t0w.1 t0w.2 t = true := by
  decide +kernel
theorem t0_22 : wordMulOK 22 5 31 a22 b22 ai22 bi22 (g22.getD 4 0) t0w.1 t0w.2 t22 = true := by
  decide +kernel

theorem sId_ok : bAnd(Nat.blt sId 512, Nat.beq (rDep RT sId) 0) = true := by decide +kernel

end CertificateChecks.TwoM22K

end
