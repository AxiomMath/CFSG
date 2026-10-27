module

public import Certificates.Kernel.LyGlue.Data
public import Certificates.Kernel.LyGlue.Hex
public import CFSG.Sporadic.Recognition.LyonsAmalgamGlueInputs
public import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LyGlue.Defs
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_ktree CertificateChecks.KernelLy TB
  "Certificates/Kernel/LyGlue/data/TABS.bin" 9467 1 2414085 2879657477213763002
#kc_select CertificateChecks.KernelLy TS TB.L 255

namespace CertificateChecks.KernelLy

open CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Recognition CFSG.KC.LyGlue CFSG.KC.Enum
  CFSG.KS

@[expose] noncomputable def tl (t a : Nat) : Nat :=
  nIf(Nat.beq t 0, a, nIf(Nat.beq t 1, cL a, nIf(Nat.beq t 2, dL a,
    pg 17 (mask 17) (TS (Nat.add (Nat.mul 15 (Nat.sub t 3)) (Nat.div a 4455))) (Nat.mod a 4455))))

@[expose] def piecesR (k : Nat) : Nat → List Nat → List (List Nat)
  | 0, L => [L]
  | f + 1, L => if L.length ≤ k then [L] else
      piecesR k f (L.take (L.length - k)) ++ [L.drop (L.length - k)]

@[expose] def chainSteps : List (List Nat) → Nat → Nat → List (Nat × Nat × List Nat) × Nat × Nat
  | [], nx, inp => ([], nx, inp)
  | p :: ps, nx, inp =>
    let r := chainSteps ps (nx + 1) nx
    ((nx, inp, p) :: r.1, r.2.1, r.2.2)

@[expose] def build (st : List (Nat × Nat × List Nat) × Nat) (lets : List Nat) :
    (List (Nat × Nat × List Nat) × Nat) × Nat :=
  let r := chainSteps (piecesR 40 lets.length lets).reverse st.2 0
  ((st.1 ++ r.1, r.2.1), r.2.2)

@[expose] def cdIdx (l : Int) : List Nat :=
  if l = 1 ∨ l = -1 then [1] else if l = 2 then [2] else [2, 2]

@[expose] def uIdx (u2 u3 u4 : Nat) (l : Int) : Nat :=
  if l = 1 then 1 else if l = 2 then u2 else if l = 3 then u3 else u4

@[expose] def progIdx : List (Nat × Nat × List Nat) × List Nat :=
  let cd := fun (w : List Int) => w.flatMap cdIdx
  let r1 := build ([], 3) (cd Ly0.wordU2)
  let r2 := build r1.1 (cd Ly0.wordU3)
  let r3 := build r2.1 (cd Ly0.wordU4)
  let uu := fun (w : List Int) => w.map (uIdx r1.2 r2.2 r3.2)
  let r4 := build r3.1 (uu yU)
  let r5 := build r4.1 (uu xU)
  let r6 := build r5.1 (cd Ly0.wordConj)
  let r7 := build r6.1 (cd (McLMultiplier.invW Ly0.wordConj))
  let r8 := build r7.1 [r4.2, r4.2]
  let r9 := build r8.1 [r6.2, r8.2, r7.2]
  let r10 := build r9.1 [r5.2, r5.2]
  let r11 := build r10.1 [r9.2, r9.2]
  let r12 := build r11.1 (cd (Glue.txWords.getD 0 []))
  let r13 := build r12.1 (cd (Glue.txWords.getD 1 []))
  let r14 := build r13.1 (cd (Glue.txWords.getD 2 []))
  let r15 := build r14.1 (cd (Glue.txWords.getD 3 []))
  (r15.1.1, [r1.2, r2.2, r3.2, r4.2, r5.2, r6.2, r7.2, r8.2, r9.2, r10.2, r11.2, r12.2,
    r13.2, r14.2, r15.2])

@[expose] def prog : List (Nat × Nat × List Nat) := progIdx.1

@[expose] def tIdx (j : Nat) : Nat := progIdx.2.getD j 0

theorem tIdx_vals : progIdx.2 = [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 19] := by
  decide +kernel

@[expose] def conjList : List (Nat × Nat × Nat × Nat) :=
  [(8, 3, 3, 8),
   (11, 4, 4, 11), (11, 3, 10, 11), (11, 8, 3, 11),
   (12, 4, 9, 12), (12, 3, 7, 12), (12, 8, 10, 12),
   (13, 4, 9, 13), (13, 3, 7, 13), (13, 8, 10, 13),
   (14, 4, 9, 14), (14, 3, 10, 14), (14, 8, 7, 14)]

@[expose] noncomputable def conjK (j : Nat) : Bool :=
  let q := conjList.getD j (0, 0, 0, 0)
  allN 66825 (fun a => Nat.beq (tl (tIdx q.1) (tl (tIdx q.2.1) a))
    (tl (tIdx q.2.2.1) (tl (tIdx q.2.2.2) a)))

end CertificateChecks.KernelLy

end
