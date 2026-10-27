module

public import Certificates.Kernel.SporE81.SuzQData
public import Certificates.Kernel.SporE81.SuzDData
public import Certificates.Kernel.Sporadic.Suz.Text2306
public import Certificates.Data.Kernel.E81IK
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE81

@[expose] noncomputable def S9D0.SK : List Nat := (List.range 243).map S9D0.SKT
@[expose] noncomputable def S9D1.SK : List Nat := (List.range 81).map S9D1.SKT
@[expose] noncomputable def S9D2.SK : List Nat := (List.range 81).map S9D2.SKT
@[expose] noncomputable def S9D3.SK : List Nat := (List.range 81).map S9D3.SKT
@[expose] noncomputable def S9D4.SK : List Nat := (List.range 81).map S9D4.SKT
@[expose] noncomputable def S9D5.SK : List Nat := (List.range 81).map S9D5.SKT
@[expose] noncomputable def S9D6.SK : List Nat := (List.range 81).map S9D6.SKT
@[expose] noncomputable def S9D7.SK : List Nat := (List.range 81).map S9D7.SKT
@[expose] noncomputable def S9D8.SK : List Nat := (List.range 81).map S9D8.SKT
@[expose] noncomputable def S9D9.SK : List Nat := (List.range 81).map S9D9.SKT

end CertificateChecks.KernelE81

namespace CertificateChecks.KernelE81.SuzK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum
open CFSG.KC.E81IK
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CertificateChecks.KernelE81 CertificateChecks.KernelSpor

@[expose] noncomputable def pm (p q : Nat) : Nat := pcomp 1782 11 (mask 11) p q

@[expose] noncomputable def PG (j : Nat) : Nat :=
  match j with
  | 0 => Suz2306.B0
  | _ => Suz2306.B1

@[expose] noncomputable def dNg (t : Nat) : Nat :=
  match t with
  | 0 => S9D0.ng | 1 => S9D1.ng | 2 => S9D2.ng | 3 => S9D3.ng | 4 => S9D4.ng
  | 5 => S9D5.ng | 6 => S9D6.ng | 7 => S9D7.ng | 8 => S9D8.ng | _ => S9D9.ng

@[expose] noncomputable def dG (t : Nat) : Nat → Nat :=
  match t with
  | 0 => S9D0.G | 1 => S9D1.G | 2 => S9D2.G | 3 => S9D3.G | 4 => S9D4.G
  | 5 => S9D5.G | 6 => S9D6.G | 7 => S9D7.G | 8 => S9D8.G | _ => S9D9.G

@[expose] noncomputable def dN (t : Nat) : Nat :=
  match t with
  | 0 => S9D0.N | 1 => S9D1.N | 2 => S9D2.N | 3 => S9D3.N | 4 => S9D4.N
  | 5 => S9D5.N | 6 => S9D6.N | 7 => S9D7.N | 8 => S9D8.N | _ => S9D9.N

@[expose] noncomputable def dT (t : Nat) : Nat → Nat :=
  match t with
  | 0 => S9D0.T | 1 => S9D1.T | 2 => S9D2.T | 3 => S9D3.T | 4 => S9D4.T
  | 5 => S9D5.T | 6 => S9D6.T | 7 => S9D7.T | 8 => S9D8.T | _ => S9D9.T

theorem perm : (permB 1782 11 Suz2306.B0 && permB 1782 11 Suz2306.B1) = true := by quickRfl

theorem permZ : permB 1782 11 (S9Z 0) = true := by quickRfl

theorem keysQ : keysSK 1782 11 suzE81.qKeys S9Q.N S9Q.T S9Q.SK = true := by quickRfl

theorem keysD0 : keysSK 1782 11 suzE81.dKeys S9D0.N S9D0.T S9D0.SK = true := by quickRfl
theorem keysD1 : keysSK 1782 11 suzE81.dKeys S9D1.N S9D1.T S9D1.SK = true := by quickRfl
theorem keysD2 : keysSK 1782 11 suzE81.dKeys S9D2.N S9D2.T S9D2.SK = true := by quickRfl
theorem keysD3 : keysSK 1782 11 suzE81.dKeys S9D3.N S9D3.T S9D3.SK = true := by quickRfl
theorem keysD4 : keysSK 1782 11 suzE81.dKeys S9D4.N S9D4.T S9D4.SK = true := by quickRfl
theorem keysD5 : keysSK 1782 11 suzE81.dKeys S9D5.N S9D5.T S9D5.SK = true := by quickRfl
theorem keysD6 : keysSK 1782 11 suzE81.dKeys S9D6.N S9D6.T S9D6.SK = true := by quickRfl
theorem keysD7 : keysSK 1782 11 suzE81.dKeys S9D7.N S9D7.T S9D7.SK = true := by quickRfl
theorem keysD8 : keysSK 1782 11 suzE81.dKeys S9D8.N S9D8.T S9D8.SK = true := by quickRfl
theorem keysD9 : keysSK 1782 11 suzE81.dKeys S9D9.N S9D9.T S9D9.SK = true := by quickRfl

theorem lettersQ : (suzE81.qW.toList.all fun w => w.all fun l => decide (l < 2)) = true := by
  simp only [suzE81, Array.toList_map]
  decide +kernel

theorem lettersH : (suzE81.hW.toList.all fun w => w.all fun l => decide (l < 2)) = true := by
  simp only [suzE81, Array.toList_map]
  decide +kernel

theorem lettersZ : suzE81.zW.all (fun l => decide (l < 3)) = true := by
  simp only [suzE81]
  decide +kernel

theorem lettersR : (suzE81.rW.toList.all fun w => w.all fun l => decide (l < 3)) = true := by
  simp only [suzE81, Array.toList_map]
  decide +kernel

theorem lettersD : (suzE81.dW.toList.all fun ws => ws.toList.all fun w => w.all fun l =>
    decide (l < 3)) = true := by
  simp only [suzE81, List.toList_toArray, List.all_cons, List.all_nil, Array.toList_map]
  decide +kernel

theorem wordsQ : suzE81.qW.toList.map (posWordK 1782 11 PG) = (List.range 3).map S9Q.G := by
  simp only [suzE81, Array.toList_map]
  decide +kernel

theorem wordsR : suzE81.rW.toList.map (posWordK 1782 11 S9Q.G) = (List.range 3).map S9Q.G := by
  simp only [suzE81, Array.toList_map]
  decide +kernel

theorem wordsD : ∀ t < 10,
    suzE81.dW[t]!.toList.map (posWordK 1782 11 S9Q.G) = (List.range (dNg t)).map (dG t) := by
  simp only [suzE81]
  decide +kernel

theorem wordsH : suzE81.hW.toList.map (posWordK 1782 11 PG) =
    (List.range 1).map (fun _ => pidn 1782 11) := by
  simp only [suzE81, Array.toList_map]
  decide +kernel

theorem wordZ : posWordK 1782 11 S9Q.G suzE81.zW = S9Z 0 := by
  simp only [suzE81]
  decide +kernel

theorem zOK : (Nat.beq (pm (S9Z 0) (pm (S9Z 0) (S9Z 0))) (pidn 1782 11) &&
    !Nat.beq (S9Z 0) (pidn 1782 11) && Nat.beq (pm (S9Z 0) (S9Z 0)) (S9Z 1) &&
    allN 3 (fun k => Nat.beq (pm (S9Z 0) (S9Q.G k)) (pm (S9Q.G k) (S9Z 0)))) = true := by
  quickRfl

theorem dSize : allN 10 (fun t => Nat.ble 81 (dN t) && Nat.ble (dN t) 245) = true := by
  quickRfl

theorem elem : allN 10 (fun t => allN (dNg t) fun a =>
    Nat.beq (pm (dG t a) (pm (dG t a) (dG t a))) (pidn 1782 11) &&
      allN (dNg t) fun b => Nat.beq (pm (dG t a) (dG t b)) (pm (dG t b) (dG t a))) = true := by
  quickRfl

theorem cov : allN 2187 (fun k => covIK 1782 11 10 dN dT (S9Z 0) (S9Z 1) S9ZW (S9CW k)
    (S9Q.T k)) = true := by
  quickRfl

end CertificateChecks.KernelE81.SuzK

end
