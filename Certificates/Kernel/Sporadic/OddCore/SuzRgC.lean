module

public import Certificates.Kernel.Sporadic.OddCore.SuzRgK0
public import Certificates.Kernel.Sporadic.OddCore.SuzRgK1
public import Certificates.Kernel.Sporadic.OddCore.SuzRgP
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.SuzRg.cellSlAll CertificateChecks.KernelSpor.SuzRg.cellSl 128
#kon_join CertificateChecks.KernelSpor.SuzRg.ptSlAll CertificateChecks.KernelSpor.SuzRg.ptSl 16
#kon_join CertificateChecks.KernelSpor.SuzRg.ucSlAll CertificateChecks.KernelSpor.SuzRg.ucSl 16
#kon_join CertificateChecks.KernelSpor.SuzRg.bfSlAll CertificateChecks.KernelSpor.SuzRg.bfSl 81
#kon_join CertificateChecks.KernelSpor.SuzRg.irKAll CertificateChecks.KernelSpor.SuzRg.irK 64

namespace CertificateChecks.KernelSpor.SuzRg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Sporadic.SuzRecog.RigidL2
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzMGF
  CertificateChecks.KernelSpor.SuzC1EG

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "Id" => pidn 1782 11
local notation "W" => SuzFb.W
local notation "QE" => KernelLC.SuzB0QE
local notation "nget" => CFSG.KS.Mathieu.nget

@[expose] noncomputable def genK (i : Nat) : Bool :=
  strictB (cWK (gen i).2.1) fun C => strictB (SuzRgT i) fun R =>
    bAnd(Nat.blt (gen i).1 2, bAnd(SuzFb.lettersK (gen i).2.1,
      bAnd(Nat.beq (pc C W) (pc W C), bAnd(Nat.beq (pc R W) (pc W R),
        Nat.beq (pc C (SK (gen i).1)) (pc R C)))))

@[expose] noncomputable def commK (i k : Nat) : Bool :=
  strictB (nget SuzRgCQ (Nat.add (Nat.mul 8 i) k)) fun q => bAnd(Nat.blt q 4,
    Nat.beq (pc (SuzRgT i) (SuzRgT k)) (pc (QE q) (pc (SuzRgT k) (SuzRgT i))))

@[expose] noncomputable def gamK (s g : Nat) : Bool :=
  strictB (SuzRgV (Nat.add 3 (Nat.add (Nat.mul 2 s) g))) fun G => strictB (SK s) fun S =>
    bAnd(SuzFb.lettersK (gam s g), bAnd(Nat.beq (pc G W) (pc W G),
      strictB (nget SuzRgGV (Nat.add (Nat.mul 2 s) g)) fun i => bAnd(Nat.blt i 4,
        Nat.beq (pc G S) (pc (QE i) (pc S G)))))

@[expose] noncomputable def seedK (s : Nat) : Bool :=
  strictB (SK s) fun S => bAnd(Nat.beq (pc S W) (pc W S),
    strictB (nget SuzRgSQ s) fun i => bAnd(Nat.blt i 4, Nat.beq (SuzRgV (Nat.add 1 s)) (QE i)))

theorem kU : allN 16 (fun c => bAnd(SuzFb.lettersK (rigUWords.getD c []),
    Nat.beq (SuzRgU c) (utK c))) = true := by quickRfl

theorem kT : allN 8 (fun i => bAnd(Nat.blt (gen i).2.2.1 16, bAnd(Nat.blt (gen i).2.2.2 128,
    Nat.beq (SuzRgT i) (pc (SuzRgU (gen i).2.2.1) (QE (gen i).2.2.2))))) = true := by quickRfl

theorem kV0 : Nat.beq (SuzRgV 0) (cWK rigX1) = true := by quickRfl

theorem kVS : allN 2 (fun s => Nat.beq (SuzRgV (Nat.add 1 s)) (pc (SK s) (SK s))) = true := by
  quickRfl

theorem kVG : allN 2 (fun s => allN 2 fun g =>
    Nat.beq (SuzRgV (Nat.add 3 (Nat.add (Nat.mul 2 s) g))) (cWK (gam s g))) = true := by quickRfl

theorem kGen : allN 8 genK = true := by quickRfl

theorem kComm : allN 8 (fun i => allN 8 fun k => commK i k) = true := by quickRfl

theorem kSeed : allN 2 (fun s => bAnd(seedK s, allN 2 fun g => gamK s g)) = true := by quickRfl

theorem kX1 : bAnd(Nat.beq (pc (SuzRgV 0) W) (pc W (SuzRgV 0)),
    Nat.beq (cWK (rigX1 ++ rigX1 ++ rigX1 ++ rigX1 ++ rigX1)) Id) = true := by quickRfl

theorem kX2 : bAnd(SuzFb.lettersK rigX2, bAnd(Nat.beq (pc (cWK rigX2) W) (pc W (cWK rigX2)),
    uTestK (SuzFb.mWK (rigX2 ++ rigX2 ++ rigX2)))) = true := by quickRfl

theorem kLift : allN 16 (fun c => bAnd(Nat.beq (pc (SuzRgU c) W) (pc W (SuzRgU c)),
    bAnd(uTestK (SuzFb.mWK (rigUWords.getD c [])),
      bIf(Nat.beq (rigUFix.getD c 0) 0, true, Nat.beq (rigUFix.getD c 0) 1)))) = true := by
  quickRfl

theorem kUP : allN 16 (fun c => bAnd(Nat.blt (nget SuzRgUP c) 25920,
    Nat.beq (SuzFbE.T (nget SuzRgUP c)) (SuzFb.mWK (rigUWords.getD c [])))) = true := by quickRfl

theorem kUPLen : SuzRgUP.length = 16 := by decide +kernel

theorem kM : allN 60 (fun k => bAnd(SuzFb.lettersK (rigExpand (rigBfs.getD k [])),
    Nat.beq (SuzRgM k) (SuzFb.mWK (rigExpand (rigBfs.getD k []))))) = true := by quickRfl

theorem kN : allN 64 (fun v => perpK v == (rigBil v == 0)) = true := by quickRfl

theorem kIrr : rigIrrWords = (List.range 8).map fun k => rigBfs.getD k [] := by decide +kernel

theorem negCell : Bool.not (cellR 0 5 (Nat.xor (pg 256 (mask 256) (SuzRgE 0) 5) 1)) = true := by
  quickRfl

theorem negCell2 : Bool.not (cellR 3 70 (Nat.xor (pg 256 (mask 256) (SuzRgE 3) 70) 1)) = true := by
  quickRfl

theorem negT : Bool.not (allN 8 fun i => Nat.beq (SuzRgT i)
    (pc (SuzRgU (gen i).2.2.1) (QE (Nat.xor (gen i).2.2.2 1)))) = true := by quickRfl

theorem negUP : Bool.not (allN 1620 fun i =>
    bIf(uTestK (SuzFbE.T i), SuzFb.memK SuzRgUP.tail i, true)) = true := by quickRfl

theorem negIrr : Bool.not (allN 64 fun u =>
    bIf(perpK u, rigXor (bvec 2) 0 == u, true)) = true := by quickRfl

theorem negSeed : Bool.not (Nat.beq (SuzRgV 1) (QE (Nat.xor (nget SuzRgSQ 0) 1))) = true := by
  quickRfl

theorem negPT : Bool.not (Nat.beq (SuzRgPT 255) (ptK 127)) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzRg

end
