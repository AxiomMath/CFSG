module

public import Certificates.Kernel.ONSeven.Defs
public import CFSG.Certificates.Kernel.Spor.CBCoset
public import CFSG.RankThree.Native.ONSevenData

public section

namespace CertificateChecks.KernelSpor.ONS

open CFSG.KC.Enum CFSG.KS.CB CFSG.RankThree.Native
open CertificateChecks.KernelSpor.ON (TT UU stepF invF PARf LABf)
open CFSG.KS.ON (tab)

@[expose] def invL (w : List Int) : List Int := w.reverse.map fun l => -l

@[expose] def tw (r : Nat) : List Int := onSevenConjWords.getD r []

@[expose] def xw (r : Nat) : List Int := onSevenLineWords.getD (onSevenRepIdx.getD r 0) []

@[expose] def cw (r : Nat) : List Int := tw r ++ xw r ++ invL (tw r)

@[expose] def bd (r : Nat) : List (Nat × List Int) := (onSevenBadData.getD r #[]).toList

@[expose] def uw (r i : Nat) : List Int := ((bd r).getD i (0, [])).2

@[expose] def bw (r i : Nat) : List Int := invL (uw r i) ++ cw r ++ uw r i

@[expose] def badB (r q : Nat) : Bool := (bd r).any fun b => Nat.beq b.1 q

@[expose] noncomputable def stepO1 (j x : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 5),
    nIf(Nat.blt j (nat_lit 2), nIf(Nat.beq j (nat_lit 0), tab ONV.T2 x, tab ONV.T3 x),
      nIf(Nat.beq j (nat_lit 2), tab ONV.T4 x, nIf(Nat.beq j (nat_lit 3), tab ONV.T5 x, tab ONV.T6 x))),
    nIf(Nat.blt j (nat_lit 10),
      nIf(Nat.blt j (nat_lit 7), nIf(Nat.beq j (nat_lit 5), tab ONV.U2 x, tab ONV.U3 x),
        nIf(Nat.beq j (nat_lit 7), tab ONV.U4 x, nIf(Nat.beq j (nat_lit 8), tab ONV.U5 x, tab ONV.U6 x))),
      stepF 1 j x))

@[expose] noncomputable def invO1 (j x : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 5),
    nIf(Nat.blt j (nat_lit 2), nIf(Nat.beq j (nat_lit 0), tab ONV.U2 x, tab ONV.U3 x),
      nIf(Nat.beq j (nat_lit 2), tab ONV.U4 x, nIf(Nat.beq j (nat_lit 3), tab ONV.U5 x, tab ONV.U6 x))),
    nIf(Nat.blt j (nat_lit 10),
      nIf(Nat.blt j (nat_lit 7), nIf(Nat.beq j (nat_lit 5), tab ONV.T2 x, tab ONV.T3 x),
        nIf(Nat.beq j (nat_lit 7), tab ONV.T4 x, nIf(Nat.beq j (nat_lit 8), tab ONV.T5 x, tab ONV.T6 x))),
      invF 1 j x))

@[expose] noncomputable def stepO2 (j x : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 2), nIf(Nat.beq j (nat_lit 0), tab ONV.T5 x, tab ONV.T6 x),
    nIf(Nat.blt j (nat_lit 4), nIf(Nat.beq j (nat_lit 2), tab ONV.U5 x, tab ONV.U6 x), stepF 2 j x))

theorem stepO1_eq : stepO1 = stepF 1 := by
  funext j x
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;> rfl

theorem invO1_eq : invO1 = invF 1 := by
  funext j x
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;> rfl

theorem stepO2_eq : stepO2 = stepF 2 := by
  funext j x
  rcases j with _ | _ | _ | _ | j <;> rfl

@[expose] noncomputable def ccZo (Z A : Nat → Nat) (k : Nat) : Nat :=
  ccF Z A stepO1 invO1 (PARf 1) (LABf 1) (nat_lit 52136) stepO2 (PARf 2) (LABf 2)
    (nat_lit 36) (nat_lit 227759) (nat_lit 100817) k

theorem ccZo_eq : ccZo = ccZ := by
  funext Z A k
  unfold ccZo ccZ
  rw [stepO1_eq, invO1_eq, stepO2_eq]

@[expose] noncomputable def ccS (Z A V : Nat → Nat) (s : Nat) : Bool :=
  Nat.beq (sumR2 (ccZo Z A) (Nat.mul (nat_lit 2048) s) (nat_lit 32)) (V s)

@[expose] noncomputable def cfT (U Ui X A : Nat → Nat) (k₁ : Nat) : Bool :=
  cfK U Ui X A stepO1 invO1 (PARf 1) (LABf 1) (nat_lit 52136) stepO2 (PARf 2) (LABf 2)
    (nat_lit 36) (nat_lit 227759) (nat_lit 100817) k₁

@[expose] noncomputable def cfS (U Ui X A : Nat → Nat) (s : Nat) : Bool :=
  allN (nat_lit 2048) fun d => strictB (Nat.add (Nat.mul (nat_lit 2048) s) d) fun k =>
    bIf(Nat.blt k (nat_lit 52136), cfT U Ui X A k, true)

@[expose] noncomputable def fxT (x t : Nat → Nat) (bad : Nat → Bool) (p : Nat) : Nat :=
  nIf(Nat.blt p (nat_lit 245520),
    nIf(Nat.beq (x p) p, nIf(bad (t p), nat_lit 0, nat_lit 1), nat_lit 0), nat_lit 0)

@[expose] noncomputable def fxS (x t : Nat → Nat) (bad : Nat → Bool) (V : Nat → Nat) (s : Nat) :
    Bool :=
  Nat.beq (sumR2 (fxT x t bad) (Nat.mul (nat_lit 30720) s) (nat_lit 480)) (V s)

end CertificateChecks.KernelSpor.ONS

end
