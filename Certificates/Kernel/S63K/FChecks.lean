module

public import Certificates.Kernel.S63K.FData
public import Certificates.Kernel.S63K.GData
public import Certificates.Kernel.S63K.HBind
public import Certificates.Data.Kernel.S63K.OrbRun
public import Certificates.Data.D4HexF48Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS63.FK

open CFSG.KC.S63K CFSG.KC.Enum CFSG.KS CFSG.D4Hex CertificateChecks.KernelS63

@[expose] noncomputable def tb (t i : Nat) : Nat := pg 12 (mask 12) (FD.D t) i
@[expose] noncomputable def O (i : Nat) : Nat := tb 0 i
@[expose] noncomputable def Pa (i : Nat) : Nat := tb 1 i
@[expose] noncomputable def La (i : Nat) : Nat := tb 2 i
@[expose] noncomputable def Ps (i : Nat) : Nat := tb 3 i
@[expose] noncomputable def W (i : Nat) : Nat := tb 4 i
@[expose] noncomputable def X (i : Nat) : Nat := tb 5 i
@[expose] noncomputable def C (i : Nat) : Nat := tb 6 i
@[expose] noncomputable def L0 (x : Nat) : Nat := pg 12 (mask 12) (GD.G 2) x
@[expose] noncomputable def LP (i : Nat) : Nat := pg 12 (mask 12) HD.LT i

@[expose] noncomputable def nw (x : Nat) : Nat := HD.ptW f48NWord x
@[expose] noncomputable def qw (x : Nat) : Nat := HD.ptW f48QWord x
@[expose] noncomputable def fw (j x : Nat) : Nat := HD.ptW (f48FWords.getD j []) x
@[expose] noncomputable def bw (j x : Nat) : Nat := HD.ptW (f48BWords.getD j []) x

@[expose] noncomputable def sg (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => k)
    (fun _ ih i => nIf(Nat.beq i 0, k, fw (La i) (ih (Pa i))))

@[expose] noncomputable def aF (k y : Nat) : Nat := nIf(Nat.blt (Ps y) 512, sg k 512 (Ps y), y)
@[expose] noncomputable def mF (k y : Nat) : Nat := nw (aF k y)
@[expose] noncomputable def gF (k y : Nat) : Nat := mF k (qw y)
@[expose] noncomputable def gIt (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x) (fun _ ih x => gF k (ih x))

@[expose] noncomputable def mapsF (f : Nat → Nat) : Bool := f48OnL0 (f 0) && f48OnL0 (f 1) && f48OnL0 (f 5)
@[expose] noncomputable def inBF (f : Nat → Nat) : Bool := f 0 == 0 && mapsF f

@[expose] noncomputable def has0F (l : Nat) : Bool :=
  LP (3 * l + 0) == 0 || LP (3 * l + 1) == 0 || LP (3 * l + 2) == 0
@[expose] noncomputable def lineInF (l a b c : Nat) : Bool :=
  f48In3 (LP (3 * l + 0)) a b c && f48In3 (LP (3 * l + 1)) a b c && f48In3 (LP (3 * l + 2)) a b c

@[expose] noncomputable def pwOK (M i : Nat) : Bool :=
  i == 0 || C i == 0 ||
    (Nat.blt (X i) 819 && gIt (O i) (C i) (X i) == X i && !(gIt (O i) (M % C i) (X i) == X i))

theorem ch4236R : bAnd(Nat.beq (O 0) 71, bAnd(Nat.beq (Pa 0) 0, bAnd(Nat.beq (La 0) 0,
    orbConsK 819 512 O Ps))) = true := by
  quickRfl

theorem ch4236Run : Nat.beq (orbRunK W Pa La 2 513 0 1) 512 = true := by quickRfl

theorem ch4236A : (allN 512 fun h => allN 2 fun j => Nat.beq (fw j (O h)) (O (W (2 * h + j)))) =
    true := by
  quickRfl

theorem ch4236L0 : Nat.beq (L0 71) 6 = true := by quickRfl

theorem ch4236L : (allN 819 fun x => bAnd(decide (L0 x ≤ 4) || L0 x == 6,
    bIf(Nat.beq (L0 x) 6, Nat.blt (Ps x) 512, true))) = true := by
  quickRfl

theorem ch4236LO : (allN 512 fun i => Nat.beq (L0 (O i)) 6) = true := by quickRfl

theorem ch4236NN : (allN 819 fun x => Nat.beq (nw (nw x)) x) = true := by quickRfl

theorem ch4236N : bAnd(nw 0 == 0, bAnd(!mapsF nw, bAnd(mapsF qw,
    bAnd(allN 2 fun j => inBF (fw j) && inBF (fun x => nw (fw j (nw x))),
      allN 8 fun j => inBF (bw j))))) = true := by
  quickRfl

theorem ch4236Ln : (allN 2457 fun l => !has0F l || lineInF l 0 1 5 ||
    (List.range 8).any fun j => lineInF l (bw j (nw 0)) (bw j (nw 1)) (bw j (nw 5))) = true := by
  quickRfl

theorem ch4236X : (allN 819 fun x => x == 0 || !(fw 0 x == x && fw 1 x == x)) = true := by
  quickRfl

theorem ch4236S : (allN 512 fun i => i == 0 || !(C i == 0) ||
    (Nat.blt (X i) 819 && !(mF (O i) (mF (O i) (X i)) == X i))) = true := by
  quickRfl

theorem ch4236P : (allN 512 fun i => pwOK 211341312 i) = true := by quickRfl

theorem ch4236P3 : (allN 512 fun i => pwOK 634023936 i) = true := by quickRfl

end CertificateChecks.KernelS63.FK

end
