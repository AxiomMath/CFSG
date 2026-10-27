module

public import Certificates.Kernel.SporSch.Ly.BSData
public import Certificates.Kernel.SporSch.Ly.GenCover
public import CFSG.Sporadic.Schreier.LyCheckCover
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kly_cover CertificateChecks.KernelSporSch.LyCv

namespace CertificateChecks.KernelSporSch.LyCv

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.Th.Native
open CertificateChecks.KernelSporSch.LyBS

@[expose] noncomputable def TTk (i y : Nat) : Nat :=
  nIf(bAnd(Nat.blt i 11, Nat.blt y 11), TT (Nat.add (Nat.mul 11 i) y), ONE)

@[expose] noncomputable def TTIk (i y : Nat) : Nat :=
  nIf(bAnd(Nat.blt i 11, Nat.blt y 11), TTI (Nat.add (Nat.mul 11 i) y), ONE)

@[expose] noncomputable def stripK (st : Array Nat × Nat) (l : Nat) : Array Nat × Nat :=
  (compP (invP (tPArr l (st.1[l]!))) st.1, mul (TTIk l (st.1[l]!)) st.2)

@[expose] noncomputable def resK (i x j : Nat) : Array Nat × Nat :=
  ((List.range 11).filter fun l => decide (i < l)).foldl stripK
    (compP (invP (tPArr i ((pArr j)[x]!))) (compP (pArr j) (tPArr i x)),
      mul (TTIk i ((pArr j)[x]!)) (mul (CFx 12 j) (TTk i x)))

@[expose] noncomputable def relJ (i x j : Nat) : Bool :=
  !fixesBelow j i || Prod.rec (motive := fun _ => Bool) (fun P X => strictB X (fun X' =>
    P == id11 && (Nat.beq X' ONE || Nat.beq X' A))) (resK i x j)

@[expose] def orbAt (i k : Nat) : Nat := (chainOrbits[i]!)[k]!

@[expose] noncomputable def relQ (q : Nat) : Bool :=
  bIf(Nat.blt ((q / 12) % 11) (chainOrbits[q / 132]!).length,
    relJ (q / 132) (orbAt (q / 132) ((q / 12) % 11)) (q % 12), true)

end CertificateChecks.KernelSporSch.LyCv

#kly_rels CertificateChecks.KernelSporSch.LyCv CertificateChecks.KernelSporSch.LyCv.relQ

namespace CertificateChecks.KernelSporSch.LyCv

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.Th.Native
open CertificateChecks.KernelSporSch.LyBS

@[expose] noncomputable def ttOK (q : Nat) : Bool :=
  Nat.beq ((twWord (q / 11) (q % 11)).foldl (fun X j => mul X (CFx 12 j)) ONE) (TT q)

@[expose] noncomputable def ttiOK (q : Nat) : Bool :=
  Nat.beq ((twWord (q / 11) (q % 11)).reverse.foldl (fun X j => mul X (CIx 12 j)) ONE) (TTI q)

theorem tt0 : allBlk 0 ttOK 11 = true := by quickRfl
theorem tt1 : allBlk 11 ttOK 11 = true := by quickRfl
theorem tt2 : allBlk 22 ttOK 11 = true := by quickRfl
theorem tt3 : allBlk 33 ttOK 11 = true := by quickRfl
theorem tt4 : allBlk 44 ttOK 11 = true := by quickRfl
theorem tt5 : allBlk 55 ttOK 11 = true := by quickRfl
theorem tt6 : allBlk 66 ttOK 11 = true := by quickRfl
theorem tt7 : allBlk 77 ttOK 11 = true := by quickRfl
theorem tt8 : allBlk 88 ttOK 11 = true := by quickRfl
theorem tt9 : allBlk 99 ttOK 11 = true := by quickRfl
theorem tt10 : allBlk 110 ttOK 11 = true := by quickRfl

theorem tti0 : allBlk 0 ttiOK 11 = true := by quickRfl
theorem tti1 : allBlk 11 ttiOK 11 = true := by quickRfl
theorem tti2 : allBlk 22 ttiOK 11 = true := by quickRfl
theorem tti3 : allBlk 33 ttiOK 11 = true := by quickRfl
theorem tti4 : allBlk 44 ttiOK 11 = true := by quickRfl
theorem tti5 : allBlk 55 ttiOK 11 = true := by quickRfl
theorem tti6 : allBlk 66 ttiOK 11 = true := by quickRfl
theorem tti7 : allBlk 77 ttiOK 11 = true := by quickRfl
theorem tti8 : allBlk 88 ttiOK 11 = true := by quickRfl
theorem tti9 : allBlk 99 ttiOK 11 = true := by quickRfl
theorem tti10 : allBlk 110 ttiOK 11 = true := by quickRfl

theorem vT : allN 121 (fun q => bAnd(vld (TT q), vld (TTI q))) = true := by quickRfl

theorem bB : Nat.beq (mul B B4) ONE = true := by quickRfl

theorem c0A : Nat.beq (mul A (CF 0)) (mul (CF 0) A) = true := by quickRfl
theorem c1A : Nat.beq (mul A (CF 1)) (mul (CF 1) A) = true := by quickRfl
theorem c0n1 : Bool.not (Nat.beq (CF 0) ONE) = true := by quickRfl
theorem c0nA : Bool.not (Nat.beq (CF 0) A) = true := by quickRfl

theorem r010 : Prod.rec (motive := fun _ => Bool) (fun _ X => Nat.beq X A) (resK 0 1 0) = true := by
  quickRfl

theorem transInv : transInvOK = true := by decide +kernel

end CertificateChecks.KernelSporSch.LyCv

end
