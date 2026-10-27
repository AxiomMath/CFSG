module

public import Certificates.Kernel.Sporadic.SuzK.LaneDefs

public section

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.F3.Native CFSG.KS.F3L CFSG.KS.PEnum CFSG.Sporadic.Suz.Native CFSG.Sporadic.Th.Native

@[expose] noncomputable def tabList (F : Nat → Nat) : Nat → Nat → List UInt32
  | _, 0 => []
  | j, c + 1 => UInt32.ofNat (r32 F j) :: tabList F (j + 1) c

@[expose] noncomputable def tabOf (F : Nat → Nat) : Table := ⟨tabList F 0 22880⟩

@[expose] noncomputable def keyW (k : Nat) : Array W := (unlane 64 (laneK k)).map ofV

@[expose] noncomputable def keysLit : Array (Array W) := Array.ofFn (n := 22880) fun k => keyW k.val

@[expose] noncomputable def orbLit : WOrbit := ⟨keysLit, tabOf AL, tabOf BE, tabOf PA, tabOf LB⟩

end CertificateChecks.KernelSpor.SuzK

end
