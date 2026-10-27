module

public import Certificates.Data.Kernel.Spor.ConjRun
public import Certificates.Data.Kernel.Spor.MulHF
public import Certificates.Kernel.Sporadic.OddCore.J3BetaA5
public import Certificates.Kernel.SporSch.PairJ3.Chain
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Sporadic.OddCore.C24602D
meta import Certificates.Kernel.Sporadic.OddCore.C24602D
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#krows CertificateChecks.KernelSpor.C2462PL CertificateChecks.KernelSpor.C24602D.pl

namespace CertificateChecks.KernelSpor.C24602

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 6156
meta def invA (a : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 6156 a
meta def strongM : Array (Array Nat) := CFSG.Sporadic.Schreier.j3StrongArrs
meta def letM (z : Int) : Array Nat :=
  if 0 < z then strongM[z.toNat - 1]! else invA strongM[(-z).toNat - 1]!
meta def wordM (w : List Int) : Array Nat := w.foldl (fun g z => comp 6156 g (letM z)) idM
meta def subM (ws : List (List Int)) : Array (Array Nat) := ws.toArray.map wordM
meta def sub8M : Array (Array Nat) := subM C24602D.w8
meta def sub27M : Array (Array Nat) := subM C24602D.w27
meta def sub5M : Array (Array Nat) := subM C24602D.w5
meta def ids (k : Nat) : Array (Array Nat) := Array.replicate k idM
meta def ids1M : Array (Array Nat) := ids 1
meta def ids2M : Array (Array Nat) := ids 2
meta def ids3M : Array (Array Nat) := ids 3
meta def recM (gs : Array (Array Nat)) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 6156 idM gs[j]! t) gs.size idM 40).tabs
meta def clM (gs : Array (Array Nat)) : Array (Array Nat) :=
  ((recM gs).map fun x => (gs ++ gs.map invA).map fun g => comp 6156 x g).flatten
meta def rec8M : Array (Array Nat) := recM sub8M
meta def rec27M : Array (Array Nat) := recM sub27M
meta def rec5M : Array (Array Nat) := recM sub5M
meta def cl8M : Array (Array Nat) := clM sub8M
meta def cl27M : Array (Array Nat) := clM sub27M
meta def cl5M : Array (Array Nat) := clM sub5M
meta def inv8M : Array (Array Nat) := sub8M.map invA
meta def inv27M : Array (Array Nat) := sub27M.map invA
meta def inv5M : Array (Array Nat) := sub5M.map invA

end CertificateChecks.KernelSpor.C24602

open CertificateChecks.KernelSpor.C24602 in
#kmulh CertificateChecks.KernelSpor.C2462S8 6156 13 ids2M sub8M idM 40
open CertificateChecks.KernelSpor.C24602 in
#kmulh CertificateChecks.KernelSpor.C2462S27 6156 13 ids3M sub27M idM 40
open CertificateChecks.KernelSpor.C24602 in
#kmulh CertificateChecks.KernelSpor.C2462S5 6156 13 ids1M sub5M idM 40
open CertificateChecks.KernelSpor.C24602 in
#kmisc_packarrs CertificateChecks.KernelSpor.C2462S8I inv8M 13
open CertificateChecks.KernelSpor.C24602 in
#kmisc_packarrs CertificateChecks.KernelSpor.C2462S27I inv27M 13
open CertificateChecks.KernelSpor.C24602 in
#kmisc_packarrs CertificateChecks.KernelSpor.C2462S5I inv5M 13
open CertificateChecks.KernelSpor.C24602 in
#kfind CertificateChecks.KernelSpor.C2462S8Cl rec8M cl8M
open CertificateChecks.KernelSpor.C24602 in
#kfind CertificateChecks.KernelSpor.C2462S27Cl rec27M cl27M
open CertificateChecks.KernelSpor.C24602 in
#kfind CertificateChecks.KernelSpor.C2462S5Cl rec5M cl5M

namespace CertificateChecks.KernelSpor.C24602

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.ConjRun
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 6156 13 (mask 13) (6156 * 13) p

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 6156 13 (mask 13) p q

@[expose] noncomputable def bK : Nat := J3BetaP 7

@[expose] noncomputable def c24602run (s : Nat) : Bool :=
  runK 6156 13 (mask 13) 5 C24602D.root bK PJ3.S PJ3.SI C2462PL 8 4 C24602D.N
    (Nat.mul s 4096) 4096

@[expose] noncomputable def subGensK (k : Nat) (G GI GJ : Nat → Nat) (ws : List (List Int)) :
    Bool :=
  allN k (fun j => bAnd(Nat.beq (G j) (pidn 6156 13), bAnd(cK (GI j), bAnd(cK (GJ j),
    bAnd(invEqK 6156 13 (mask 13) (6156 * 13) (GI j) (GJ j),
    bAnd(wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 (ws.getD j []) (GI j),
      Nat.beq (pc bK (GI j)) (pc (GI j) bK)))))))

theorem k_base : bAnd(cK bK, bAnd(cK (J3BetaI 1),
    bAnd(invEqK 6156 13 (mask 13) (6156 * 13) bK (J3BetaI 1),
    bAnd(Nat.beq C24602D.N 46512, bAnd(Nat.blt C24602D.root C24602D.N,
    bAnd(subGensK 2 C2462S8.G C2462S8.GI C2462S8I C24602D.w8, bAnd(Nat.beq C2462S8.cnt 8,
    bAnd(penumHdK (pidn 6156 13) C2462S8.cnt 40 C2462S8.T C2462S8.PL,
    bAnd(subGensK 3 C2462S27.G C2462S27.GI C2462S27I C24602D.w27, bAnd(Nat.beq C2462S27.cnt 27,
    bAnd(penumHdK (pidn 6156 13) C2462S27.cnt 40 C2462S27.T C2462S27.PL,
    bAnd(subGensK 1 C2462S5.G C2462S5.GI C2462S5I C24602D.w5, bAnd(Nat.beq C2462S5.cnt 5,
    penumHdK (pidn 6156 13) C2462S5.cnt 40 C2462S5.T C2462S5.PL))))))))))))) = true := by
  quickRfl

#kc_each CertificateChecks.KernelSpor.C24602.c24602run 0 12

theorem s8E : penumSlK 6156 13 (mask 13) (6156 * 13) true C2462S8.G C2462S8.GI 2 C2462S8.cnt
    C2462S8.T C2462S8.PL C2462S8.POS C2462S8.SRT C2462S8.SRI 0 C2462S8.cnt = true := by quickRfl
theorem s8HF : slK C2462S8.cnt (hsortPtKF 6156 13 (mask 13) C2462S8.cnt C2462S8.T C2462S8.HS
    C2462S8.HSI) 0 C2462S8.cnt = true := by quickRfl
theorem s8Cl : slK (Nat.mul C2462S8.cnt 4)
    (findPtK C2462S8.cnt C2462S8.T
      (prodQK 6156 13 (mask 13) 4 C2462S8.T (bothK 2 C2462S8.GI C2462S8I)) C2462S8Cl) 0
      (Nat.mul C2462S8.cnt 4) = true := by quickRfl

theorem s27E : penumSlK 6156 13 (mask 13) (6156 * 13) true C2462S27.G C2462S27.GI 3
    C2462S27.cnt C2462S27.T C2462S27.PL C2462S27.POS C2462S27.SRT C2462S27.SRI 0 C2462S27.cnt =
      true := by quickRfl
theorem s27HF : slK C2462S27.cnt (hsortPtKF 6156 13 (mask 13) C2462S27.cnt C2462S27.T
    C2462S27.HS C2462S27.HSI) 0 C2462S27.cnt = true := by quickRfl
theorem s27Cl : slK (Nat.mul C2462S27.cnt 6)
    (findPtK C2462S27.cnt C2462S27.T
      (prodQK 6156 13 (mask 13) 6 C2462S27.T (bothK 3 C2462S27.GI C2462S27I)) C2462S27Cl) 0
      (Nat.mul C2462S27.cnt 6) = true := by quickRfl

theorem s5E : penumSlK 6156 13 (mask 13) (6156 * 13) true C2462S5.G C2462S5.GI 1 C2462S5.cnt
    C2462S5.T C2462S5.PL C2462S5.POS C2462S5.SRT C2462S5.SRI 0 C2462S5.cnt = true := by quickRfl
theorem s5HF : slK C2462S5.cnt (hsortPtKF 6156 13 (mask 13) C2462S5.cnt C2462S5.T C2462S5.HS
    C2462S5.HSI) 0 C2462S5.cnt = true := by quickRfl
theorem s5Cl : slK (Nat.mul C2462S5.cnt 2)
    (findPtK C2462S5.cnt C2462S5.T
      (prodQK 6156 13 (mask 13) 2 C2462S5.T (bothK 1 C2462S5.GI C2462S5I)) C2462S5Cl) 0
      (Nat.mul C2462S5.cnt 2) = true := by quickRfl

theorem s27HF_neg :
    hsortPtKF 6156 13 (mask 13) C2462S27.cnt (fun _ => 0) C2462S27.HS C2462S27.HSI 0 = false := by
  decide +kernel

end CertificateChecks.KernelSpor.C24602

end
