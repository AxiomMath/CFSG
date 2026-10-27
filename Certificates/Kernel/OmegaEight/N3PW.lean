module

public import Certificates.Kernel.OmegaEight.N3PlusWitData
public import Certificates.Kernel.OmegaEight.N3PlusClsData
public import Certificates.Kernel.OmegaEight.EnumN3PC
public import Certificates.Kernel.OmegaEight.EnumN3PSmall
public import Certificates.Kernel.OmegaEight.EnumN3PS0
public import Certificates.Kernel.OmegaEight.EnumN3PS1
public import Certificates.Kernel.OmegaEight.EnumN3PS2
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitPlusW
public import CFSG.Certificates.Kernel.O8PlusSound
public import CFSG.Certificates.Kernel.O8BridgeSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.KLie.CT CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split CFSG.EvenSmallLie.OmegaEight.N3Split.Plus
  CFSG.EvenSmallLie.OmegaEight.N3Split.PlusW

@[expose] noncomputable def chunkAt (T : List ℕ) (w i : ℕ) : ℕ :=
  fget (T.getD (Nat.div i 256) 0) (Nat.mod i 256) w

@[expose] noncomputable def wN3P : Wit where
  cE := decE EnN3PC.D EnN3PC.m
  tcE := decE EnN3PT.D EnN3PT.m
  ukE := decE EnN3PUK.D EnN3PUK.m
  c2E := decE EnN3PC2.D EnN3PC2.m
  p3E := decE EnN3PP3.D EnN3PP3.m
  sE0 := decE EnN3PS0.D EnN3PS0.m
  mE0 := decE EnN3PM0.D EnN3PM0.m
  s2E := decE EnN3PS2.D EnN3PS2.m
  m2E := decE EnN3PM2.D EnN3PM2.m
  sE1 := decE EnN3PS1.D EnN3PS1.m
  mE1 := decE EnN3PM1.D EnN3PM1.m
  imgX v := fget N3pIX v 12
  lin := N3pLin
  ncLin := N3pNC
  cls0 := (fun i => unpackL (chunkAt N3pB0 200 i), chunkAt N3pR0 16, chunkAt N3pY0 16)
  cls2 := (fun i => unpackL (chunkAt N3pB2 200 i), chunkAt N3pR2 16, chunkAt N3pY2 16)
  cls1 := (fun i => unpackL (chunkAt N3pB1 200 i), chunkAt N3pR1 16, chunkAt N3pY1 16)

theorem cE_okN3P : enumOK cGens wN3P.cE = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3PC.head
    EnN3PC.blocks
  rwa [genPairsK_eq (gs := cGens)
    (by simp only [cGens, splitCGens, kronK_eq]; decide +kernel)
    (by simp only [cGens, splitCGens, kronK_eq]; decide +kernel)] at h

theorem tcE_okN3P : enumOK tGens wN3P.tcE = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3PT.head
    EnN3PT.blocks
  rwa [genPairsK_eq (gs := tGens)
    (by simp only [tGens, splitTGens, kronK_eq]; decide +kernel)
    (by simp only [tGens, splitTGens, kronK_eq]; decide +kernel)] at h

theorem ukE_okN3P : enumOK ukGens wN3P.ukE = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3PUK.head
    EnN3PUK.blocks
  rwa [genPairsK_eq (gs := ukGens)
    (by simp only [ukGens, tGens, splitTGens, kronK_eq]; decide +kernel)
    (by simp only [ukGens, tGens, splitTGens, kronK_eq]; decide +kernel)] at h

theorem c2E_okN3P : enumOK c2Gens wN3P.c2E = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3PC2.head
    EnN3PC2.blocks
  rwa [genPairsK_eq (gs := c2Gens) (by decide +kernel) (by decide +kernel)] at h

theorem p3E_okN3P : enumOK p3Gens wN3P.p3E = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3PP3.head
    EnN3PP3.blocks
  rwa [genPairsK_eq (gs := p3Gens) (by decide +kernel) (by decide +kernel)] at h

theorem mE0_okN3P : enumOK mGens0 wN3P.mE0 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3PM0.head
    EnN3PM0.blocks
  rwa [genPairsK_eq (gs := mGens0) (by decide +kernel) (by decide +kernel)] at h

theorem mE1_okN3P : enumOK mGens1 wN3P.mE1 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3PM1.head
    EnN3PM1.blocks
  rwa [genPairsK_eq (gs := mGens1) (by decide +kernel) (by decide +kernel)] at h

theorem m2E_okN3P : enumOK m2Gens wN3P.m2E = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3PM2.head
    EnN3PM2.blocks
  rwa [genPairsK_eq (gs := m2Gens) (by decide +kernel) (by decide +kernel)] at h

theorem sE0_okN3P : enumOK sGens0 wN3P.sE0 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3PS0.head
    EnN3PS0.blocks
  rwa [genPairsK_eq (gs := sGens0)
    (by simp only [sGens0, slpGens, base, cGens, tGens, splitCGens, splitTGens, kronK_eq,
      runK_eq, fpowK_eq]; decide +kernel)
    (by simp only [sGens0, slpGens, base, cGens, tGens, splitCGens, splitTGens, kronK_eq,
      runK_eq, fpowK_eq]; decide +kernel)] at h

theorem sE1_okN3P : enumOK sGens1 wN3P.sE1 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3PS1.head
    EnN3PS1.blocks
  rwa [genPairsK_eq (gs := sGens1)
    (by simp only [sGens1, slpGens, base, cGens, tGens, splitCGens, splitTGens, kronK_eq,
      runK_eq, fpowK_eq]; decide +kernel)
    (by simp only [sGens1, slpGens, base, cGens, tGens, splitCGens, splitTGens, kronK_eq,
      runK_eq, fpowK_eq]; decide +kernel)] at h

theorem s2E_okN3P : enumOK s2Gens wN3P.s2E = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnN3PS2.head
    EnN3PS2.blocks
  rwa [genPairsK_eq (gs := s2Gens)
    (by simp only [s2Gens, sGens0, slpGens, base, cGens, tGens, splitCGens, splitTGens,
      kronK_eq, runK_eq, fpowK_eq]; decide +kernel)
    (by simp only [s2Gens, sGens0, slpGens, base, cGens, tGens, splitCGens, splitTGens,
      kronK_eq, runK_eq, fpowK_eq]; decide +kernel)] at h

end CertificateChecks.KernelO8
