module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import Certificates.Data.Kernel.Spor.PSlp
public meta import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.SuzCheck

public section

namespace CertificateChecks.KernelSpor.S129061

open CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

meta def wordsM : Array (List ℤ × List ℤ) :=
  #[suzGenWords0, suzGenWords1, suzGenWords2, suzGenWords3]

meta def progsM : Array (List (ℕ × ℕ)) :=
  #[suzProg suzGenHex0, suzProg suzGenHex1, suzProg suzGenHex2, suzProg suzGenHex3]

meta def rootsM : Array (ℕ × ℕ) := #[suzGenRoots0, suzGenRoots1, suzGenRoots2, suzGenRoots3]

meta def wM (w : List ℤ) : Array Nat := wordA 1782 bTriple bTripleInv w

meta def gM : Array (Array Nat) := (wordsM.map fun p =>
  #[wM p.1, invCand 1782 (wM p.1), wM p.2, invCand 1782 (wM p.2)]).flatten

meta def distM (prog : List (ℕ × ℕ)) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut m := 3
  for p in prog do
    out := (out.push (m - p.1)).push (m - p.2)
    m := m + 1
  return out

meta def pM : Array (Array Nat) := progsM.map distM

meta def rM : Array (Array Nat) := (List.range 4).toArray.map fun i =>
  let n := progsM[i]!.length
  #[n, 3 + n - rootsM[i]!.1, 3 + n - rootsM[i]!.2]

end CertificateChecks.KernelSpor.S129061

#kmisc_packarrs CertificateChecks.KernelSpor.S1291G CertificateChecks.KernelSpor.S129061.gM 11

#kmisc_packarrs CertificateChecks.KernelSpor.S1291P CertificateChecks.KernelSpor.S129061.pM 12

#kmisc_packarrs CertificateChecks.KernelSpor.S1291R CertificateChecks.KernelSpor.S129061.rM 16

namespace CertificateChecks.KernelSpor.S129061

open CFSG.KC.Enum CFSG.KS CFSG.KC.PSlp CertificateChecks.KernelSpor

@[expose] noncomputable def endK (D : Nat) (R : List Nat) (a b : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x xs _ => bAnd(Nat.beq (nthD (List.cons x xs) a D) Suz2306.B0,
      Nat.beq (nthD (List.cons x xs) b D) Suz2306.B1)) R

@[expose] noncomputable def genK (T G GI H HI P c a b : Nat) : Bool :=
  bAnd(permOK 1782 11 (mask 11) (1782 * 11) G GI,
  bAnd(permOK 1782 11 (mask 11) (1782 * 11) H HI,
  bAnd(Suz2306.sift G, bAnd(Suz2306.sift H,
    strictB T fun T =>
    strictB (pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) G T) GI) fun X =>
    strictB (pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) H T) HI) fun Y =>
      endK T (slpGo 1782 11 12 T c P (List.cons Y (List.cons X (List.cons T List.nil)))) a b))))

@[expose] noncomputable def rf (i k : Nat) : Nat := pg 16 (mask 16) (S1291R i) k

@[expose] noncomputable def classK (i : Nat) : Bool :=
  genK (SuzTP i) (S1291G (Nat.mul 4 i)) (S1291G (Nat.add (Nat.mul 4 i) 1))
    (S1291G (Nat.add (Nat.mul 4 i) 2)) (S1291G (Nat.add (Nat.mul 4 i) 3)) (S1291P i)
    (rf i 0) (rf i 1) (rf i 2)

end CertificateChecks.KernelSpor.S129061

end
