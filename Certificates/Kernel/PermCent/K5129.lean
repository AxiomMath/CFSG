module

public import Certificates.Data.Kernel.PermCent.Sz8DC

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5129

open CFSG.GH74.KGroups CFSG.GH74.KGroups.Sz8 CFSG.GH74.KGroups.Sz8D CFSG.Certificates.Kernel.PkEnum

@[expose] def Mt : Fin 3 → Fin 3 → ZMod 2 := ![![1, 0, 1], ![1, 1, 0], ![0, 1, 0]]

@[expose] def Wt : Fin 3 → Fin 3 → ZMod 2 := ![![0, 0, 0], ![0, 0, 1], ![1, 1, 0]]

@[expose] def Nt : Fin 3 → Fin 3 → ZMod 2 := ![![1, 1, 1], ![1, 0, 1], ![1, 0, 0]]

@[expose] def Ms : Fin 3 → Fin 3 → ZMod 2 := ![![0, 0, 1], ![1, 1, 0], ![1, 0, 1]]

@[expose] def Ws : Fin 3 → Fin 3 → ZMod 2 := ![![1, 1, 1], ![0, 1, 0], ![1, 0, 0]]

@[expose] def Ns : Fin 3 → Fin 3 → ZMod 2 := ![![1, 0, 0], ![0, 1, 1], ![0, 1, 0]]

@[expose] def qv : List (Fin 3 → ZMod 2) :=
  [![0, 0, 0], ![1, 1, 0], ![1, 0, 0], ![0, 1, 1], ![0, 0, 1], ![0, 1, 0], ![1, 1, 1], ![1, 0, 1]]

theorem kQS : schP QS = true ∧ orderV QS = 64 := by constructor <;> decide +kernel

theorem kSift : (List.finRange 3).all (fun i => siftC QS (xsC i) 0) = true ∧
    (List.finRange 3).all (fun j => siftC QS (ysC j) 0) = true := by
  constructor <;> decide +kernel

theorem kSyP : syC.all (fun c => siftC QP c 0) = true := by decide +kernel

theorem kOrb : orbOK 37 40 = true ∧ img 65 (cOf pa).1 37 = 40 := by
  constructor <;> decide +kernel

theorem kCent : ysCentOK = true ∧ commOK = true := by constructor <;> decide +kernel

theorem kNc : ncOK = true := by decide +kernel

theorem kDec : decOK = true := by decide +kernel

theorem kTt : normSOK (cOf tt) = true ∧ powOneC (cOf tt) 7 = true ∧ powOneC (cOf tt) 1 = false ∧
    siftC QP (cOf tt) 0 = true ∧ img 65 (cOf tt).1 37 = 37 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem kSig : img 65 sig0.1 37 = 37 := by decide +kernel

theorem kConj : conjOK (cOf tt) Mt Wt Nt = true ∧ conjOK sig0 Ms Ws Ns = true := by
  constructor <;> decide +kernel

theorem kSq : sqOK qv = true := by decide +kernel

theorem kAlg : kAlgB Mt Nt Ms Ns qv = true := by decide +kernel

theorem kYs : ysC 0 ≠ 1 := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5129
