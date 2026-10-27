module

public import Certificates.Kernel.OmegaEight.PlusWitData
public import Certificates.Kernel.OmegaEight.EnumCP
public import Certificates.Kernel.OmegaEight.EnumT
public import Certificates.Kernel.OmegaEight.EnumPSmall
public import Certificates.Kernel.OmegaEight.EnumS4
public import Certificates.Kernel.OmegaEight.EnumS5
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2PlusW

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.KLie.CT CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.Stage2.Plus CFSG.EvenSmallLie.OmegaEight.Stage2.PlusW

@[expose] noncomputable def wP : Wit where
  cE := decE EnCP.D EnCP.m
  tcE := decE EnTP.D EnTP.m
  uE := decE EnU.D EnU.m
  c2E := decE EnC2.D EnC2.m
  p3E := decE EnP3.D EnP3.m
  sE4 := decE EnS4.D EnS4.m
  mE4 := decE EnM4.D EnM4.m
  sE5 := decE EnS5.D EnS5.m
  mE5 := decE EnM5.D EnM5.m
  uB i := unpackL (fget PwUB i 200)
  imgX v := fget PwIX v 12
  lin := PwLin
  sB4 i := unpackL (fget PwSB4 i 200)
  sY4 i := fget PwSY4 i 14
  sB5 i := unpackL (fget PwSB5 i 200)
  sY5 i := fget PwSY5 i 14

theorem cE_ok : enumOK cGensPlus wP.cE = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnCP.head
    EnCP.blocks
  rwa [genPairsK_eq (gs := cGensPlus) (by decide +kernel) (by decide +kernel)] at h

theorem tcE_ok : enumOK tGensPlus wP.tcE = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnTP.head
    EnTP.blocks
  rwa [genPairsK_eq (gs := tGensPlus) (by decide +kernel) (by decide +kernel)] at h

theorem uE_ok : enumOK uGens wP.uE = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnU.head
    EnU.blocks
  rwa [genPairsK_eq (gs := uGens) (by decide +kernel) (by decide +kernel)] at h

theorem c2E_ok : enumOK c2Gens wP.c2E = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnC2.head
    EnC2.blocks
  rwa [genPairsK_eq (gs := c2Gens) (by decide +kernel) (by decide +kernel)] at h

theorem p3E_ok : enumOK p3Gens wP.p3E = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnP3.head
    EnP3.blocks
  rwa [genPairsK_eq (gs := p3Gens) (by decide +kernel) (by decide +kernel)] at h

theorem mE4_ok : enumOK mGens4 wP.mE4 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnM4.head
    EnM4.blocks
  rwa [genPairsK_eq (gs := mGens4) (by decide +kernel) (by decide +kernel)] at h

theorem mE5_ok : enumOK mGens5 wP.mE5 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnM5.head
    EnM5.blocks
  rwa [genPairsK_eq (gs := mGens5) (by decide +kernel) (by decide +kernel)] at h

end CertificateChecks.KernelO8
