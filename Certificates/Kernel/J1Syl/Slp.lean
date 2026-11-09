module

public import Certificates.Kernel.J1Syl.Defs
public import Certificates.Kernel.Sporadic.ON.Gen
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public meta import Certificates.Data.CFSGNative.J1.Certificate
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ1Syl

open CFSG.Sporadic.J1.Native

meta def slpRules : Array Nat := #[3, 1, 4, 1, 5, 6, 7, 7, 7, 5, 6, 9, 5, 8, 11, 10, 8, 10, 9, 3, 7, 6,
  15, 11, 16, 14, 17, 11, 5, 12, 7, 10, 20, 19, 12, 13, 18, 8, 23, 6, 8, 21, 9, 5, 22, 5, 24, 7, 13,
  3, 24, 3, 30, 13, 22, 3, 25, 26, 18, 9, 34, 4, 35, 6, 36, 21, 25, 14, 31, 29, 1, 38, 11, 21, 13, 5,
  1, 32, 1, 18, 44, 13, 37, 14, 1, 27, 37, 26, 19, 29, 32, 33, 31, 42, 1, 39, 5, 39, 41, 26, 41, 14,
  1, 46, 38, 28, 1, 28, 5, 28, 19, 42, 40, 28, 40, 27, 5, 46, 45, 32, 1, 33, 3, 3, 58, 3, 1, 48, 1,
  51, 47, 3, 43, 28, 43, 33, 43, 27, 3, 54, 5, 48, 5, 51, 55, 28, 55, 27, 49, 28, 49, 33, 49, 27, 45,
  33, 45, 27, 56, 28, 56, 27, 52, 28, 52, 33, 52, 27, 61, 3, 40, 48, 40, 51, 62, 3, 47, 59, 47, 54,
  47, 60, 43, 48, 43, 57, 43, 50, 63, 28, 63, 27, 53, 28, 53, 33, 53, 27, 55, 48, 49, 57, 49, 50, 45,
  57, 64, 28, 45, 50, 64, 27, 56, 51, 52, 50, 40, 46, 113, 27, 40, 39, 115, 27, 53, 50, 2, 4, 2, 3,
  119, 118, 120, 120, 118, 120, 122, 119, 121, 118, 123, 124, 123, 121, 4, 122, 119, 120, 124, 128,
  127, 129, 124, 130, 125, 118, 123, 120, 132, 133, 126, 125, 121, 131, 119, 136, 134, 121, 118,
  122, 118, 135, 120, 137, 4, 126, 4, 137, 126, 143, 4, 135, 139, 138, 122, 131, 3, 147, 119, 148,
  134, 149, 127, 138, 142, 144, 151, 2, 134, 124, 118, 126, 145, 2, 131, 2, 126, 157, 127, 150, 140,
  2, 139, 150, 142, 132, 146, 145, 155, 144, 152, 2, 152, 118, 139, 154, 127, 154, 159, 2, 141, 151,
  141, 2, 141, 118, 155, 132, 141, 153, 140, 153, 159, 118, 145, 158, 146, 2, 4, 4, 4, 171, 161, 2,
  164, 2, 4, 160, 141, 156, 146, 156, 140, 156, 167, 4, 161, 118, 164, 118, 141, 168, 140, 168, 141,
  162, 146, 162, 140, 162, 146, 158, 140, 158, 141, 169, 140, 169, 141, 165, 146, 165, 140, 165, 4,
  174, 161, 153, 164, 153, 4, 175, 172, 160, 167, 160, 173, 160, 161, 156, 170, 156, 163, 156, 141,
  176, 140, 176, 141, 166, 146, 166, 140, 166, 161, 168, 170, 162, 163, 162, 170, 158, 141, 177,
  163, 158, 140, 177, 164, 169, 163, 165, 159, 153, 140, 226, 152, 153, 140, 228, 163, 166]

meta def slpWords : Array Nat := #[0, 3, 58, 65, 47, 66, 59, 54, 60, 67, 68, 69, 61, 62, 70, 71, 72,
  73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
  98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 114, 116, 117, 0, 4, 171,
  178, 160, 179, 172, 167, 173, 180, 181, 182, 174, 175, 183, 184, 185, 186, 187, 188, 189, 190,
  191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209,
  210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 227, 229, 230]

meta def slpInv (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 1540 0
  for i in [0:1540] do
    r := r.set! t[i]! i
  return r

meta def slpTabs : Array (Array Nat) := Id.run do
  let al : Array Nat := (orbitData ()).alpha.map (·.toNat)
  let be : Array Nat := (orbitData ()).beta.map (·.toNat)
  let mut ts : Array (Array Nat) := #[(List.range 1540).toArray, al, slpInv al, be, slpInv be]
  for k in [0:slpRules.size / 2] do
    let a := ts[slpRules[2 * k]!]!
    let b := ts[slpRules[2 * k + 1]!]!
    ts := ts.push (b.map fun x => a[x]!)
  return ts

meta def slpTabM : Array Nat := (slpTabs.extract 5 slpTabs.size).flatten

end CertificateChecks.KernelJ1Syl

#krows CertificateChecks.KernelJ1Syl.RU CertificateChecks.KernelJ1Syl.slpRules
#krows CertificateChecks.KernelJ1Syl.WSY CertificateChecks.KernelJ1Syl.slpWords
#krows CertificateChecks.KernelJ1Syl.SLT CertificateChecks.KernelJ1Syl.slpTabM

namespace CertificateChecks.KernelJ1Syl

open CFSG.KC.Enum CFSG.KS.PEnum CFSG.Sporadic.J1.Sylow.Native CertificateChecks.KernelSpor.J1K

@[expose] noncomputable def tabS (s x : Nat) : Nat :=
  nIf(Nat.blt s (nat_lit 5),
    nIf(Nat.beq s (nat_lit 0), x, nIf(Nat.beq s (nat_lit 1), r32 AL x,
      nIf(Nat.beq s (nat_lit 2), r32 AI x, nIf(Nat.beq s (nat_lit 3), r32 BE x, r32 BI x)))),
    r32 SLT (Nat.add (Nat.mul (Nat.sub s (nat_lit 5)) (nat_lit 1540)) x))

@[expose] noncomputable def lW (s : Nat) : List Int :=
  Bool.rec (motive := fun _ => List Int)
    (Bool.rec (motive := fun _ => List Int)
      (Bool.rec (motive := fun _ => List Int)
        (Bool.rec (motive := fun _ => List Int) [-2] [2] (Nat.beq s (nat_lit 3)))
        [-1] (Nat.beq s (nat_lit 2)))
      [1] (Nat.beq s (nat_lit 1)))
    [] (Nat.beq s (nat_lit 0))

@[expose] noncomputable def ruA (k : Nat) : Nat := r32 RU (Nat.mul (nat_lit 2) k)

@[expose] noncomputable def ruB (k : Nat) : Nat := r32 RU (Nat.add (Nat.mul (nat_lit 2) k) (nat_lit 1))

@[expose] noncomputable def wsV (i : Nat) : Nat := r32 WSY i

@[expose] noncomputable def wsI (i : Nat) : Nat := r32 WSY (Nat.add i (nat_lit 60))

@[expose] noncomputable def expK (n : Nat) : Nat → List Int :=
  Nat.rec (motive := fun _ => Nat → List Int) lW
    (fun _ ih s => Bool.rec (motive := fun _ => List Int)
      (List.append (ih (ruA (Nat.sub s (nat_lit 5)))) (ih (ruB (Nat.sub s (nat_lit 5)))))
      (lW s) (Nat.blt s (nat_lit 5))) n

@[expose] noncomputable def ruleOK (k : Nat) : Bool :=
  strictB (ruA k) fun a =>
    strictB (ruB k) fun b =>
      bAnd(Nat.blt a (Nat.add k (nat_lit 5)), bAnd(Nat.blt b (Nat.add k (nat_lit 5)),
        allN (nat_lit 1540) fun x => strictB (tabS b x) fun y =>
          bAnd(Nat.blt y (nat_lit 1540), Nat.beq (tabS (Nat.add k (nat_lit 5)) x) (tabS a y))))

@[expose] noncomputable def ruleSl (q : Nat) : Bool := slice (nat_lit 29) (nat_lit 226) q ruleOK

@[expose] noncomputable def wordsOK : Bool :=
  allN (nat_lit 60) fun i => strictB (wsV i) fun s => strictB (wsI i) fun t =>
    bAnd(Nat.blt s (nat_lit 231), bAnd(Nat.blt t (nat_lit 231),
      bAnd(expK (nat_lit 300) s == NWL.getD i [],
        expK (nat_lit 300) t == invWord (NWL.getD i []))))

@[expose] noncomputable def normAtK (s t e : Nat) : Bool :=
  allN (nat_lit 1540) fun x => Nat.beq (tabS s (r32 BE (tabS t x)))
    (nIf(Nat.beq e (nat_lit 1), r32 BE x, r32 BE (r32 BE x)))

@[expose] noncomputable def normK (i : Nat) : Bool :=
  strictB (wsV i) fun s => strictB (wsI i) fun t =>
    bIf(normAtK s t (nat_lit 1), true, normAtK s t (nat_lit 2))

@[expose] noncomputable def normSl (q : Nat) : Bool := slice (nat_lit 15) (nat_lit 60) q normK

end CertificateChecks.KernelJ1Syl

#kon_slices CertificateChecks.KernelJ1Syl.ruleSl 0 8
#kon_slices CertificateChecks.KernelJ1Syl.normSl 0 4

namespace CertificateChecks.KernelJ1Syl

theorem wordsOK_ok : wordsOK = true := by quickRfl

end CertificateChecks.KernelJ1Syl

end
