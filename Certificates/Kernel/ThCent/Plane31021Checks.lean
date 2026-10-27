module

public import Certificates.Kernel.ThCent.LDefs
public import Certificates.Data.Kernel.ThCent.Plane31021
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneSporPlaneThData

public section

namespace CFSG.KD.ThCent.L

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCent CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

@[expose] noncomputable def conjRow31021 (i : Nat) : Bool := strictF C5 fun C =>
  (List.range 5).all fun j => Bool.or (Nat.beq (i + j) 0)
    (conj31021 ThS.c ThS.rm ThS.ONE V5 (V5 94) (V5 105) C (thPlaneConj ())[5 * i + j]! i j)

theorem p31021_eig : (thPlaneEig ()).all
    (fun e => strictF C5 fun C => eig31021 ThS.c ThS.rm ThS.ONE V5 (V5 94) (V5 105) C e) = true := by
  decide +kernel

theorem p31021_wA : Nat.beq (wordR ThS.c ThS.rm ThS.ONE V5 (thPlaneWordA ())) (ThS.RBf 1) = true := by
  decide +kernel

theorem p31021_wB : Nat.beq (wordR ThS.c ThS.rm ThS.ONE V5 (thPlaneWordB ())) (ThS.RBf 2) = true := by
  decide +kernel

theorem p31021_conj0 : conjRow31021 0 = true := by decide +kernel
theorem p31021_conj1 : conjRow31021 1 = true := by decide +kernel
theorem p31021_conj2 : conjRow31021 2 = true := by decide +kernel
theorem p31021_conj3 : conjRow31021 3 = true := by decide +kernel
theorem p31021_conj4 : conjRow31021 4 = true := by decide +kernel

end CFSG.KD.ThCent.L

end
