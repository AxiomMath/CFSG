module

public import Certificates.Kernel.PlusFactors.Data
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.Misc.PermWit
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import CFSG.Certificates.Kernel.Lie.CT.Core
public import CFSG.Certificates.Kernel.Spor.RawSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPlusF

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
  CFSG.KC.PermWit
open CFSG.KLie.CT (anyN)

@[expose] noncomputable def I : ℕ := pidn 60 6

@[expose] noncomputable def cmp (p q : ℕ) : ℕ := pcomp 60 6 (mask 6) p q

@[expose] noncomputable def iv (p : ℕ) : ℕ := pinvS 60 6 (mask 6) p

@[expose] noncomputable def cmt (g h : ℕ) : ℕ := cmp (cmp g h) (cmp (iv g) (iv h))

@[expose] noncomputable def cj (g y : ℕ) : ℕ := cmp g (cmp y (iv g))

@[expose] noncomputable def memT (N : ℕ) (T : ℕ → ℕ) (p : ℕ) : Bool :=
  anyN N fun j => Nat.beq p (T j)

@[expose] noncomputable def gOK (G : ℕ → ℕ) (k : ℕ) : Bool :=
  permOK 60 6 (mask 6) (Nat.mul 60 6) (G k) (iv (G k))

@[expose] noncomputable def invPt (R : ℕ → ℕ) (k : ℕ) : Bool :=
  let x := PE.T k
  let c := R k
  (Nat.beq c 0 && (!Nat.beq (cmp x x) I || Nat.beq x I)) ||
  (Nat.ble 1 c && Nat.ble c 60 && Nat.beq (PE.G (c - 1)) x) ||
  (Nat.ble 61 c && Nat.blt c 3661 &&
    (!Nat.beq ((c - 61) % 60) ((c - 61) / 60) &&
      Nat.beq (pg 6 (mask 6) (PE.G ((c - 61) % 60)) ((c - 61) / 60)) ((c - 61) / 60) &&
      Nat.beq (cmp (PE.G ((c - 61) % 60)) (PE.G ((c - 61) / 60))) x)) ||
  (Nat.ble 3661 c && (memT 60 PA.T x || memT 60 PB.T x))

@[expose] noncomputable def invOK (lo len : ℕ) : Bool := allN len fun i => invPt IE (Nat.add lo i)

@[expose] noncomputable def skE : List ℕ := (List.range 7200).map KE
@[expose] noncomputable def skA : List ℕ := (List.range 60).map KA
@[expose] noncomputable def skB : List ℕ := (List.range 60).map KB

theorem kNums : (Nat.beq PE.ng 60 && Nat.beq PE.N 7200 && Nat.beq PA.ng 2 && Nat.beq PA.N 60 &&
    Nat.beq PB.ng 2 && Nat.beq PB.N 60) = true := by decide +kernel

theorem kBindE : (Nat.beq plusTable.size 60 &&
    allN 60 fun k => bindArrK plusTable[k]! 60 6 (PE.G k)) = true := by decide +kernel

theorem kBindA : (Nat.beq plusFactorsAgens.size 2 &&
    allN 2 fun k => bindArrK plusFactorsAgens[k]! 60 6 (PA.G k)) = true := by decide +kernel

theorem kBindB : (Nat.beq plusFactorsBgens.size 2 &&
    allN 2 fun k => bindArrK plusFactorsBgens[k]! 60 6 (PB.G k)) = true := by decide +kernel

theorem kPerm : (allN 60 (gOK PE.G) && allN 2 (gOK PA.G) && allN 2 (gOK PB.G)) = true := by
  decide +kernel

theorem kPermT : (allN 60 (gOK PA.T) && allN 60 (gOK PB.T)) = true := by decide +kernel

theorem kKE : keysSK 60 6 plusBase PE.N PE.T skE = true := by decide +kernel
theorem kKA : keysSK 60 6 plusBase PA.N PA.T skA = true := by decide +kernel
theorem kKB : keysSK 60 6 plusBase PB.N PB.T skB = true := by decide +kernel

theorem kTreeA : allN 60 (fun k => Nat.beq (PA.T k) I ||
    allN 60 (ctreePt 60 6 60 k PA.T (WA k))) = true := by decide +kernel

theorem kTreeB : allN 60 (fun k => Nat.beq (PB.T k) I ||
    allN 60 (ctreePt 60 6 60 k PB.T (WB k))) = true := by decide +kernel

theorem kT0 : (Nat.beq (PA.T 0) I && Nat.beq (PB.T 0) I) = true := by decide +kernel

theorem kMem : (allN 2 (fun k => memT PE.N PE.T (PA.G k)) &&
    allN 2 (fun k => memT PE.N PE.T (PB.G k))) = true := by decide +kernel

theorem kComm : allN 2 (fun i => allN 2 fun j => Nat.beq (cmt (PA.G i) (PB.G j)) I) = true := by
  decide +kernel

theorem kDisj : allN 60 (fun i => allN 60 fun j =>
    !Nat.beq (PA.T i) (PB.T j) || Nat.beq (PA.T i) I) = true := by decide +kernel

theorem kConj : allN 60 (fun i =>
    allN 2 (fun k => memT 60 PB.T (cj (PE.G i) (PA.G k))) &&
    allN 2 (fun k => memT 60 PA.T (cj (PE.G i) (PB.G k)))) = true := by decide +kernel

theorem kNonab : (!Nat.beq (cmt (PA.G 0) (PA.G 1)) I) = true := by decide +kernel

theorem ch1383003i_0 : invOK 0 600 = true := by decide +kernel
theorem ch1383003i_1 : invOK 600 600 = true := by decide +kernel
theorem ch1383003i_2 : invOK 1200 600 = true := by decide +kernel
theorem ch1383003i_3 : invOK 1800 600 = true := by decide +kernel
theorem ch1383003i_4 : invOK 2400 600 = true := by decide +kernel
theorem ch1383003i_5 : invOK 3000 600 = true := by decide +kernel
theorem ch1383003i_6 : invOK 3600 600 = true := by decide +kernel
theorem ch1383003i_7 : invOK 4200 600 = true := by decide +kernel
theorem ch1383003i_8 : invOK 4800 600 = true := by decide +kernel
theorem ch1383003i_9 : invOK 5400 600 = true := by decide +kernel
theorem ch1383003i_10 : invOK 6000 600 = true := by decide +kernel
theorem ch1383003i_11 : invOK 6600 600 = true := by decide +kernel

end CertificateChecks.KernelPlusF
