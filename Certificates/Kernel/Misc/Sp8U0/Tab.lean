module

public import Certificates.Kernel.Misc.Sp8U0.ChecksC
public import Certificates.Kernel.Misc.Sp8U0.ChecksB
public import Certificates.Kernel.Misc.Sp8U0.ChecksB2
public import Certificates.Kernel.Misc.Sp8U0.ChecksS
public import Certificates.Kernel.Misc.Sp8U0.ChecksS2
public import CFSG.Certificates.Kernel.Misc.BfsKWStepSound
public import CFSG.Certificates.Kernel.Misc.BfsKWWalkSound
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CFSG.KD.Sp8U0

open CFSG.KD.BfsK CFSG.KD.BfsKW CFSG.KD.Sp8Syl3
open CFSG.KD.Sp62 (buildG stepG)

#kc_forall_chunks u06_bss
  (fun j => (buildSlW REC (rst REC) 9 65536 5 j && sortSlW REC 9 65536 j) = true) 64
  CFSG.KD.Sp8U0.ch899106B 1

#kc_forall_chunks u06_steps (fun j => stepSlW REC (rst REC) 9 65536 5 j = true) 64
  CFSG.KD.Sp8U0.ch899106S 1

theorem u06_build :
    buildG (rst REC) (recX REC 9) (recFW REC 9 0) (recFW REC 9 1) 65536 5 1024 = true :=
  CFSG.KC.BfsKW.buildG_of_slW (S := 64) (by norm_num) fun j hj =>
    (Eq.mp (Bool.and_eq_true _ _) (u06_bss j hj)).1

theorem u06_sort :
    CFSG.KD.G2Three.sortK (recX REC 9) (recFW REC 9 2) (recFW REC 9 3) 65536 1024 = true :=
  CFSG.KC.BfsKW.sortK_of_slW (S := 64) (by norm_num) fun j hj =>
    (Eq.mp (Bool.and_eq_true _ _) (u06_bss j hj)).2

theorem u06_step : stepG (rst REC) (recX REC 9) (recFW REC 9 0) (recFW REC 9 1) (recCW REC 9 5)
    (recPOSW REC 9 5) 65536 5 5120 = true := by
  have hc := u06_counts
  rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at hc
  exact CFSG.KC.BfsKW.stepG_of_slW (by norm_num) hc.1 hc.2 (by norm_num) u06_steps

theorem u06_tab_ok : u0TabK REC 65536 = true := by
  simp only [u0TabK, tableKW, u06_start, u06_build, u06_step, u06_sort, Bool.and_self]

end CFSG.KD.Sp8U0

end
