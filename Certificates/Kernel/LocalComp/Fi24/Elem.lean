module

public import Certificates.Kernel.LocalComp.Fi24.Parts
public import CFSG.Certificates.Kernel.LocalCompElemPartsSound
public import CFSG.Certificates.Kernel.LocalCompOps3Sound
import all CFSG.Blueprint.NativeSporadic

public section

namespace CertificateChecks.KernelLC.F24

open CFSG.KC.LQT CFSG.KC.LocalComp.ElemParts CFSG.KC.LocalComp.Replay CFSG.SectionRank.Native
open CFSG.KD.LC.F24 (lay V P N)

theorem elem : elemOK lay V N TO (fun _ => 0) 4 = true := by
  refine elemOK_of_parts (SQ := sqI) (CU := cuI) (PP := ppI) (NS := 8) (CH := 10) (by decide)
    CFSG.KD.LC.F24.steps (fun i hi => ?_) (fun i hi j hj => ?_) (fun s hs => ?_) (by norm_num)
  · match i, hi with
    | 0, _ => exact kCube0
    | 1, _ => exact kCube1
    | 2, _ => exact kCube2
    | 3, _ => exact kCube3
  · match i, hi, j, hj with
    | 1, _, 0, _ => exact kPair10
    | 2, _, 0, _ => exact kPair20
    | 2, _, 1, _ => exact kPair21
    | 3, _, 0, _ => exact kPair30
    | 3, _, 1, _ => exact kPair31
    | 3, _, 2, _ => exact kPair32
  · match s, hs with
    | 0, _ => exact kKer0
    | 1, _ => exact kKer1
    | 2, _ => exact kKer2
    | 3, _ => exact kKer3
    | 4, _ => exact kKer4
    | 5, _ => exact kKer5
    | 6, _ => exact kKer6
    | 7, _ => exact kKer7

theorem check : (ops3 781).check fi24primeData = true :=
  ops3_check_of_K CFSG.KD.LC.F24.lay_ok rfl rfl
    ((rfl : fi24primeData.seedA = CFSG.Blueprint.NativeSporadic.Fi24primeSeed1).trans
      CFSG.KD.LC.F24.LA_eq)
    ((rfl : fi24primeData.seedB = CFSG.Blueprint.NativeSporadic.Fi24primeSeed2).trans
      CFSG.KD.LC.F24.LB_eq)
    CFSG.KD.LC.F24.decA CFSG.KD.LC.F24.decB CFSG.KD.LC.F24.one CFSG.KD.LC.F24.steps kReplay elem

end CertificateChecks.KernelLC.F24
