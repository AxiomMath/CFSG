module

public import Certificates.Kernel.LocalComp.Q47Data
public import Certificates.Kernel.LocalComp.Q47Enum
public import Certificates.Kernel.LocalComp.Step44Check
public import CFSG.Certificates.Kernel.Q47KSound

public section

namespace CertificateChecks.KernelLC.Q47

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Q47K
open CFSG.ComponentClassification.AS81.Q47 CFSG.ComponentClassification.AS81.HeSylow
open CertificateChecks.KernelLC

@[expose] noncomputable def PK (L : List (Array Nat)) (w k : Nat) : Nat := packA w (L.getD k #[]).toList

@[expose] noncomputable def bndK (n w : Nat) (gs : List (Array Nat)) (G : Nat → Nat) : Bool :=
  allN gs.length fun k => (Nat.beq gs[k]!.size n && bindListFromK gs[k]!.toList w (G k) 0) &&
    permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k))

theorem bound_of_bndK {n w : Nat} {gs : List (Array Nat)} {G : Nat → Nat}
    (h : bndK n w gs G = true) : Bound n w gs G := fun k hk => by
  have h' := allN_spec h k hk
  rw [Bool.and_eq_true] at h'
  exact ⟨Step44Check.bindA_eq h'.1, h'.2⟩

@[expose] noncomputable def kList (KE KF : List (List (Array Nat))) (i : Nat) : List (Array Nat) :=
  Bool.rec (motive := fun _ => List (Array Nat)) (KF.getD (i - 2) []) (KE.getD i []) (decide (i < 2))

@[expose] noncomputable def K16 : ModelK :=
  ⟨PK q47Rep16 5, packA 5 heSylZ16.toList, HeSylX.G, HeSylX.N, HeSylX.T, HeSylX.E, HeSylX.S,
    HeSylQ.G, HeSylQ.N, HeSylQ.T, HeSylQ.E, HeSylQ.S, HeSylE.G, HeSylE.N, HeSylE.T, HeSylE.E, HeSylE.S,
    HeSylF.G, HeSylF.N, HeSylF.T, HeSylF.E, HeSylF.S, HeSylX.G, HeSylX.N, HeSylX.T, HeSylX.E, HeSylX.S,
    PK q47D16 7, PK q47Eb16 7, PK q47Fb16 7, fun i => PK (kList q47KE16 q47KF16 i) 7, PK q47C16 7,
    HeSylX.ng⟩

@[expose] noncomputable def K32 : ModelK :=
  ⟨PK q47Rep32 6, packA 6 heAutZ32.toList, HeAutY.G, HeAutY.N, HeAutY.T, HeAutY.E, HeAutY.S,
    HeAutQ.G, HeAutQ.N, HeAutQ.T, HeAutQ.E, HeAutQ.S, HeAutE.G, HeAutE.N, HeAutE.T, HeAutE.E, HeAutE.S,
    HeAutF.G, HeAutF.N, HeAutF.T, HeAutF.E, HeAutF.S, Q47NE.G, Q47NE.N, Q47NE.T, Q47NE.E, Q47NE.S,
    PK q47D32 7, PK q47Eb32 7, PK q47Fb32 7, fun i => PK (kList q47KE32 q47KF32 i) 7, PK q47C32 7,
    HeAutY.ng⟩

@[expose] noncomputable def CS : List Cls :=
  [clsOf q47M16 K16 false, clsOf q47M16 K16 true, clsOf q47M32 K32 false, clsOf q47M32 K32 true]

@[expose] noncomputable def ob (s : Nat) : Bool :=
  Nat.beq (oBlock SZ TR q47W1 q47W2 q47L30 CS s) (BC s)

end CertificateChecks.KernelLC.Q47

end
