module

public import Certificates.Kernel.OmegaEight.MinusWitData
public import Certificates.Kernel.OmegaEight.EnumCM
public import Certificates.Kernel.OmegaEight.EnumT
public import Certificates.Kernel.OmegaEight.EnumMSmall
public import Certificates.Kernel.OmegaEight.EnumS0M
public import Certificates.Kernel.OmegaEight.EnumS1M
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2MinusW
public import CFSG.Certificates.Kernel.O8PlusSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.KLie.CT CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.Stage2.Minus CFSG.EvenSmallLie.OmegaEight.Stage2.MinusW

@[expose] noncomputable def wM : Wit where
  cE := decE EnCM.D EnCM.m
  tcE := decE EnTM.D EnTM.m
  uE := decE EnUM.D EnUM.m
  c2E := decE EnC2M.D EnC2M.m
  p3E := decE EnP3M.D EnP3M.m
  sE0 := decE EnS0.D EnS0.m
  mE0 := decE EnM0.D EnM0.m
  sE1 := decE EnS1.D EnS1.m
  mE1 := decE EnM1.D EnM1.m
  sE7 := decE EnS7.D EnS7.m
  mE7 := decE EnM7.D EnM7.m
  uB i := unpackL (fget MwUB i 200)
  imgX v := fget MwIX v 12
  lin := MwLin
  sB0 i := unpackL (fget MwSB0 i 200)
  sY0 i := fget MwSY0 i 14
  sB1 i := unpackL (fget MwSB1 i 200)
  sY1 i := fget MwSY1 i 14
  sB7 i := unpackL (fget MwSB7 i 200)
  sY7 i := fget MwSY7 i 14
  sZ7 i := fget MwSZ7 i 14
  mB7 i := unpackL (fget MwMB7 i 200)

theorem cE_okM : enumOK cGensMinus wM.cE = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnCM.head
    EnCM.blocks
  rwa [genPairsK_eq (gs := cGensMinus) (by decide +kernel) (by decide +kernel)] at h

theorem tcE_okM : enumOK tGensMinus wM.tcE = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnTM.head
    EnTM.blocks
  rwa [genPairsK_eq (gs := tGensMinus) (by decide +kernel) (by decide +kernel)] at h

theorem uE_okM : enumOK uGens wM.uE = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnUM.head
    EnUM.blocks
  rwa [genPairsK_eq (gs := uGens) (by decide +kernel) (by decide +kernel)] at h

theorem c2E_okM : enumOK c2Gens wM.c2E = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnC2M.head
    EnC2M.blocks
  rwa [genPairsK_eq (gs := c2Gens) (by decide +kernel) (by decide +kernel)] at h

theorem p3E_okM : enumOK p3Gens wM.p3E = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnP3M.head
    EnP3M.blocks
  rwa [genPairsK_eq (gs := p3Gens) (by decide +kernel) (by decide +kernel)] at h

theorem mE0_okM : enumOK mGens0 wM.mE0 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnM0.head
    EnM0.blocks
  rwa [genPairsK_eq (gs := mGens0) (by decide +kernel) (by decide +kernel)] at h

theorem mE1_okM : enumOK mGens1 wM.mE1 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnM1.head
    EnM1.blocks
  rwa [genPairsK_eq (gs := mGens1) (by decide +kernel) (by decide +kernel)] at h

theorem mE7_okM : enumOK mGens7 wM.mE7 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnM7.head
    EnM7.blocks
  rwa [genPairsK_eq (gs := mGens7) (by decide +kernel) (by decide +kernel)] at h

theorem sE0_okM : enumOK sGens0 wM.sE0 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnS0.head
    EnS0.blocks
  rwa [genPairsK_eq (gs := sGens0)
    (by simp only [sGens0, slpGens, runK_eq, fpowK_eq]; decide +kernel)
    (by simp only [sGens0, slpGens, runK_eq, fpowK_eq]; decide +kernel)] at h

theorem sE1_okM : enumOK sGens1 wM.sE1 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnS1.head
    EnS1.blocks
  rwa [genPairsK_eq (gs := sGens1)
    (by simp only [sGens1, slpGens, runK_eq, fpowK_eq]; decide +kernel)
    (by simp only [sGens1, slpGens, runK_eq, fpowK_eq]; decide +kernel)] at h

theorem sE7_okM : enumOK sGens7 wM.sE7 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnS7.head
    EnS7.blocks
  rwa [genPairsK_eq (gs := sGens7)
    (by simp only [sGens7, slpGens, runK_eq, fpowK_eq]; decide +kernel)
    (by simp only [sGens7, slpGens, runK_eq, fpowK_eq]; decide +kernel)] at h

end CertificateChecks.KernelO8
