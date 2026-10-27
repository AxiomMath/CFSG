module

public import Certificates.Kernel.Sporadic.OddCore.SuzFamF
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzFamD

open CFSG.KC.Enum CFSG.KS CFSG.KS.TBfs CFSG.KS.Mathieu CertificateChecks.KernelSpor.Suz2306
open CertificateChecks.KernelSpor.OddCore

set_option Elab.async false

theorem neg_pi : Bool.not (strictB (FAM 5) (fun A => strictB (FAM (pg 11 (mask 11) B0 5)) (fun E =>
    strictB (PI 11) (fun P => allN 2080 (fun j =>
      Nat.beq (ak 0 (fld(A, Nat.mul 15 j, mask 15)))
        (fld(E, Nat.mul 15 (fld(P, Nat.mul 12 j, mask 12)), mask 15))))))) = true := by quickRfl

theorem neg_gen : Bool.not (strictB (FAM 7) (fun A => strictB (FAM (pg 11 (mask 11) B0 7)) (fun E =>
    strictB (PI 15) (fun P => allN 2080 (fun j =>
      Nat.beq (ak 1 (fld(A, Nat.mul 15 j, mask 15)))
        (fld(E, Nat.mul 15 (fld(P, Nat.mul 12 j, mask 12)), mask 15))))))) = true := by quickRfl

theorem neg_inc : Bool.not (Nat.blt (fe 3 1) (fe 3 0)) = true := by quickRfl

theorem neg_rank : Bool.not (Nat.blt (RK 9) (RK 9)) = true := by quickRfl

theorem neg_seed : Bool.not (Nat.beq (SuzSeedT.F 0) (FAM 1)) = true := by quickRfl

theorem neg_tree : Bool.not (tbfsSlK 1782 ST.cnt 4 (fun l x => sL (nIf(Nat.beq l 0, 2,
    nIf(Nat.beq l 2, 0, l))) x) (nget [0, 1, 2, 3]) ST.PTS ST.POS ST.PAR ST.LAB ST.TI 0 1782) =
    true := by quickRfl

end CertificateChecks.KernelSpor.SuzFamD

end
