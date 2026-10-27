module

public meta import CFSG.RankThree.Native.ONSevenArrays
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.NativeSchreierCard
public meta import CFSG.Sporadic.Schreier.ONCheckChain
public import Certificates.Kernel.Sporadic.RawGen
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CertificateChecks.KernelSpor.ONR.Gen

open CFSG.RankThree.Native CFSG.KS.RawGen

meta def pows (n w : Nat) (t : Array Nat) (o : Nat) : Array Nat := Id.run do
  let mut p := Array.range n
  let mut r : Array Nat := #[]
  for _ in [0:o + 1] do
    r := r.push (pack w p)
    p := comp n t p
  return r

meta def cArrs (r : Nat) : Array (Array Nat) :=
  (onSevenCArrs r).push (onSevenRepArr r) ++ (if r < 3 then onSevenFArrs r else #[])

meta def kb : Array Nat := #[0, 1, 2]
meta def qR : Array Nat := onSevenQR
meta def qA : Array (Array Nat) := onSevenQArrs ++ onSevenLineArrs
meta def qT : Array (Array Nat) := onSevenQTabs
meta def qL : Array Nat := onSevenLineTabs.flatMap fun t => pows onSevenQR.size 10 t 7
meta def c0R : Array Nat := onSevenCR 0
meta def c1R : Array Nat := onSevenCR 1
meta def c2R : Array Nat := onSevenCR 2
meta def c3R : Array Nat := onSevenCR 3
meta def c4R : Array Nat := onSevenCR 4
meta def c0A : Array (Array Nat) := cArrs 0
meta def c1A : Array (Array Nat) := cArrs 1
meta def c2A : Array (Array Nat) := cArrs 2
meta def c3A : Array (Array Nat) := cArrs 3
meta def c4A : Array (Array Nat) := cArrs 4
meta def c0T : Array (Array Nat) := onSevenCTabs 0
meta def c1T : Array (Array Nat) := onSevenCTabs 1
meta def c2T : Array (Array Nat) := onSevenCTabs 2
meta def c3T : Array (Array Nat) := onSevenCTabs 3
meta def c4T : Array (Array Nat) := onSevenCTabs 4
meta def f0T : Array (Array Nat) := onSevenFTabs 0
meta def f1T : Array (Array Nat) := onSevenFTabs 1
meta def f2T : Array (Array Nat) := onSevenFTabs 2
meta def x0P : Array Nat := pows (onSevenCR 0).size 12 (onSevenRepTab 0) 7
meta def x1P : Array Nat := pows (onSevenCR 1).size 12 (onSevenRepTab 1) 7
meta def x2P : Array Nat := pows (onSevenCR 2).size 12 (onSevenRepTab 2) 7

end CertificateChecks.KernelSpor.ONR.Gen

end
