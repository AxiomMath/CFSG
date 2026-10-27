module

public import Certificates.Kernel.OmegaEight.N3MinusWitData
public import Certificates.Kernel.OmegaEight.N3MinusClsData
public import Certificates.Kernel.OmegaEight.EnumN3MC
public import Certificates.Kernel.OmegaEight.EnumN3MSmall
public import Certificates.Kernel.OmegaEight.EnumN3MS0
public import Certificates.Kernel.OmegaEight.EnumN3MS1
public import Certificates.Kernel.OmegaEight.EnumN3MS2
public import Certificates.Kernel.OmegaEight.N3PW
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitMinusW

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.KLie.CT CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split CFSG.EvenSmallLie.OmegaEight.N3Split.Minus
  CFSG.EvenSmallLie.OmegaEight.N3Split.MinusW

@[expose] noncomputable def wN3M : Wit where
  cE := decE EnN3MC.D EnN3MC.m
  tcE := decE EnN3MT.D EnN3MT.m
  ukE := decE EnN3MUK.D EnN3MUK.m
  c2E := decE EnN3MC2.D EnN3MC2.m
  p3E := decE EnN3MP3.D EnN3MP3.m
  sE0 := decE EnN3MS0.D EnN3MS0.m
  mE0 := decE EnN3MM0.D EnN3MM0.m
  s2E := decE EnN3MS2.D EnN3MS2.m
  m2E := decE EnN3MM2.D EnN3MM2.m
  sE1 := decE EnN3MS1.D EnN3MS1.m
  mE1 := decE EnN3MM1.D EnN3MM1.m
  sE3 := decE EnN3MS3.D EnN3MS3.m
  mE3 := decE EnN3MM3.D EnN3MM3.m
  imgX v := fget N3mIX v 12
  lin := N3mLin
  ncLin := N3mNC
  cls0 := (fun i => unpackL (chunkAt N3mB0 200 i), chunkAt N3mR0 16, chunkAt N3mY0 16)
  cls2 := (fun i => unpackL (chunkAt N3mB2 200 i), chunkAt N3mR2 16, chunkAt N3mY2 16)
  cls1 := (fun i => unpackL (chunkAt N3mB1 200 i), chunkAt N3mR1 16, chunkAt N3mY1 16)
  maxY i := N3mMaxY.getD i 0

theorem cE_okN3M : enumOK cGens wN3M.cE = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3MC.head
    EnN3MC.blocks
  rwa [genPairsK_eq (gs := cGens)
    (by simp only [cGens, splitCGens, kronK_eq]; decide +kernel)
    (by simp only [cGens, splitCGens, kronK_eq]; decide +kernel)] at h

theorem tcE_okN3M : enumOK tGens wN3M.tcE = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3MT.head
    EnN3MT.blocks
  rwa [genPairsK_eq (gs := tGens)
    (by simp only [tGens, splitTGens, kronK_eq]; decide +kernel)
    (by simp only [tGens, splitTGens, kronK_eq]; decide +kernel)] at h

theorem ukE_okN3M : enumOK ukGens wN3M.ukE = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3MUK.head
    EnN3MUK.blocks
  rwa [genPairsK_eq (gs := ukGens)
    (by simp only [ukGens, tGens, splitTGens, kronK_eq]; decide +kernel)
    (by simp only [ukGens, tGens, splitTGens, kronK_eq]; decide +kernel)] at h

theorem c2E_okN3M : enumOK c2Gens wN3M.c2E = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3MC2.head
    EnN3MC2.blocks
  rwa [genPairsK_eq (gs := c2Gens) (by decide +kernel) (by decide +kernel)] at h

theorem p3E_okN3M : enumOK p3Gens wN3M.p3E = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3MP3.head
    EnN3MP3.blocks
  rwa [genPairsK_eq (gs := p3Gens) (by decide +kernel) (by decide +kernel)] at h

theorem mE0_okN3M : enumOK mGens0 wN3M.mE0 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3MM0.head
    EnN3MM0.blocks
  rwa [genPairsK_eq (gs := mGens0) (by decide +kernel) (by decide +kernel)] at h

theorem mE1_okN3M : enumOK mGens1 wN3M.mE1 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3MM1.head
    EnN3MM1.blocks
  rwa [genPairsK_eq (gs := mGens1) (by decide +kernel) (by decide +kernel)] at h

theorem m2E_okN3M : enumOK m2Gens wN3M.m2E = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3MM2.head
    EnN3MM2.blocks
  rwa [genPairsK_eq (gs := m2Gens) (by decide +kernel) (by decide +kernel)] at h

theorem mE3_okN3M : enumOK mGens3 wN3M.mE3 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3MM3.head
    EnN3MM3.blocks
  rwa [genPairsK_eq (gs := mGens3) (by decide +kernel) (by decide +kernel)] at h

theorem sE0_okN3M : enumOK sGens0 wN3M.sE0 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3MS0.head
    EnN3MS0.blocks
  rwa [genPairsK_eq (gs := sGens0)
    (by simp only [sGens0, slpGens, base, cGens, tGens, splitCGens, splitTGens, kronK_eq,
      runK_eq, fpowK_eq]; decide +kernel)
    (by simp only [sGens0, slpGens, base, cGens, tGens, splitCGens, splitTGens, kronK_eq,
      runK_eq, fpowK_eq]; decide +kernel)] at h

theorem sE1_okN3M : enumOK sGens1 wN3M.sE1 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3MS1.head
    EnN3MS1.blocks
  rwa [genPairsK_eq (gs := sGens1)
    (by simp only [sGens1, slpGens, base, cGens, tGens, splitCGens, splitTGens, kronK_eq,
      runK_eq, fpowK_eq]; decide +kernel)
    (by simp only [sGens1, slpGens, base, cGens, tGens, splitCGens, splitTGens, kronK_eq,
      runK_eq, fpowK_eq]; decide +kernel)] at h

theorem sE3_okN3M : enumOK sGens3 wN3M.sE3 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3MS3.head
    EnN3MS3.blocks
  rwa [genPairsK_eq (gs := sGens3)
    (by simp only [sGens3, slpGens, base, cGens, tGens, splitCGens, splitTGens, kronK_eq,
      runK_eq, fpowK_eq]; decide +kernel)
    (by simp only [sGens3, slpGens, base, cGens, tGens, splitCGens, splitTGens, kronK_eq,
      runK_eq, fpowK_eq]; decide +kernel)] at h

theorem s2E_okN3M : enumOK s2Gens wN3M.s2E = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3MS2.head
    EnN3MS2.blocks
  rwa [genPairsK_eq (gs := s2Gens)
    (by simp only [s2Gens, sGens0, slpGens, base, cGens, tGens, splitCGens, splitTGens,
      kronK_eq, runK_eq, fpowK_eq]; decide +kernel)
    (by simp only [s2Gens, sGens0, slpGens, base, cGens, tGens, splitCGens, splitTGens,
      kronK_eq, runK_eq, fpowK_eq]; decide +kernel)] at h

end CertificateChecks.KernelO8
