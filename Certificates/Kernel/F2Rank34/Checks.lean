module

public import Certificates.Data.Kernel.F2Rank34.Defs

public section

namespace CFSG.KC.F2R34

open CFSG.Quasithin.B45Mat.M22

@[expose] noncomputable def colsA : List ℕ := [814, 496, 216, 530, 522, 460, 59, 644, 744, 330]

@[expose] noncomputable def rowsA : List ℕ := [64, 601, 161, 885, 78, 323, 806, 422, 547, 409]

@[expose] noncomputable def colsD : List ℕ := [914, 337, 876, 880, 720, 705, 80, 484, 305, 420]

@[expose] noncomputable def rowsD : List ℕ := [290, 1, 644, 4, 347, 908, 254, 689, 911, 61]

@[expose] noncomputable def colsR : List ℕ := [337, 920, 608, 635, 628, 421, 149, 133, 80, 484]

@[expose] noncomputable def rowsR : List ℕ := [233, 8, 752, 10, 347, 572, 797, 738, 547, 30]

theorem rankA : check34 w115HA colsA rowsA w115PARows w115QARows = true := by
  decide +kernel

theorem rankD : check34 w115HD colsD rowsD w115PDRows w115QDRows = true := by
  decide +kernel

theorem rankR : check34 w115HR colsR rowsR w115PRRows w115QRRows = true := by
  decide +kernel

end CFSG.KC.F2R34
