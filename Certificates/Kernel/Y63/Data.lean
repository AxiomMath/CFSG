module

public import Certificates.Kernel.Y63.D

public section

namespace CertificateChecks.KernelY63

open CFSG.KC.Enum CFSG.KS CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk

@[expose] noncomputable def f9 (R i : Nat) : Nat := pg 9 (mask 9) R i

@[expose] noncomputable def f10 (R i : Nat) : Nat := pg 10 (mask 10) R i

@[expose] noncomputable def cnt (i : Nat) : Nat := pg 16 (mask 16) (LNT 0) i

@[expose] noncomputable def cjK (i j : Nat) : Nat × Nat :=
  match (List.range (cnt 1)).find? fun t =>
      Nat.beq (f9 (CJT 0) (4 * t)) i && Nat.beq (f9 (CJT 0) (4 * t + 1)) j with
  | some t => (f9 (CJT 0) (4 * t + 2), f9 (CJT 0) (4 * t + 3))
  | none => (4, 0)

@[expose] noncomputable def dK : Data where
  T x c := f9 (TT x) c
  W y := (List.range (f9 (WT y) 0)).map fun i => f9 (WT y) (i + 1)
  mt x y := f9 (MT x) y
  iv x := f9 (IVT 0) x
  m0 := (List.range 64).map fun i => f9 (M0T 0) i
  reps := (List.range (cnt 0)).map fun i => f9 (M0T 1) i
  sk k := (List.range 64).map fun i => f9 (SKT k) i
  cj := cjK
  tau k x := f9 (TAUT k) x
  z := 165
  u0 k := (List.range 128).map fun i => f10 (U0T k) i
  cw k := (List.range (cnt (2 + k))).map fun i =>
    ⟨f10 (CWT k) (4 * i), f10 (CWT k) (4 * i + 1), f10 (CWT k) (4 * i + 2), f10 (CWT k) (4 * i + 3)⟩

end CertificateChecks.KernelY63

end
