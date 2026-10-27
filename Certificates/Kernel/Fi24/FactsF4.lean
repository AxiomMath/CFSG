module

public import CFSG.Certificates.Kernel.Fi24.Slices.F4
public import CFSG.Certificates.Kernel.Fi24.Slices.F5
public import CFSG.Certificates.Kernel.Fi24.Slices.F6
public import CFSG.Certificates.Kernel.Fi24.Slices.F7
public import CFSG.Certificates.Kernel.Fi24.Slices.F8
public import CFSG.Certificates.Kernel.Fi24.Slices.F9
public import CFSG.Certificates.Kernel.Fi24.Slices.F10
public import CFSG.Certificates.Kernel.Fi24.Slices.F11
import Certificates.Kernel.LceSTab.Chain

public section

namespace CertificateChecks.KernelFi24

open CFSG.KC CFSG.KC.LceSeg

theorem F4facts : Nat.beq (LceS.runFacts CFSG.KD.F4.blk CFSG.KD.F4.selWT CFSG.KD.F4.INV CFSG.KD.F4.nC
    (nat_lit 16) (seg CFSG.KD.F4.JF (Nat.sub (CFSG.KD.F4.loF 1) (CFSG.KD.F4.loF 0)) (CFSG.KD.F4.loF 0))
    (CFSG.KD.F4.accF 0)) (CFSG.KD.F4.accF 1) = true :=
  facts_chain _ _ _ _ (nat_lit 16) CFSG.KD.F4.JF CFSG.KD.F4.loF CFSG.KD.F4.accF 1 CFSG.KD.F4.okW_all

theorem F4cover : Nat.beq (LceS.runCover CFSG.KD.F4.blk CFSG.KD.F4.LVs (nat_lit 960) (nat_lit 16)
    (seg CFSG.KD.F4.JV (Nat.sub (CFSG.KD.F4.loC 1) (CFSG.KD.F4.loC 0)) (CFSG.KD.F4.loC 0))
    (CFSG.KD.F4.accC 0)) (CFSG.KD.F4.accC 1) = true :=
  cover_chain _ _ (nat_lit 960) (nat_lit 16) CFSG.KD.F4.JV CFSG.KD.F4.loC CFSG.KD.F4.accC 1
    CFSG.KD.F4.okC_all

theorem F5facts : Nat.beq (LceS.runFacts CFSG.KD.F5.blk CFSG.KD.F5.selWT CFSG.KD.F5.INV CFSG.KD.F5.nC
    (nat_lit 14) (seg CFSG.KD.F5.JF (Nat.sub (CFSG.KD.F5.loF 1) (CFSG.KD.F5.loF 0)) (CFSG.KD.F5.loF 0))
    (CFSG.KD.F5.accF 0)) (CFSG.KD.F5.accF 1) = true :=
  facts_chain _ _ _ _ (nat_lit 14) CFSG.KD.F5.JF CFSG.KD.F5.loF CFSG.KD.F5.accF 1 CFSG.KD.F5.okW_all

theorem F5cover : Nat.beq (LceS.runCover CFSG.KD.F5.blk CFSG.KD.F5.LVs (nat_lit 392) (nat_lit 14)
    (seg CFSG.KD.F5.JV (Nat.sub (CFSG.KD.F5.loC 1) (CFSG.KD.F5.loC 0)) (CFSG.KD.F5.loC 0))
    (CFSG.KD.F5.accC 0)) (CFSG.KD.F5.accC 1) = true :=
  cover_chain _ _ (nat_lit 392) (nat_lit 14) CFSG.KD.F5.JV CFSG.KD.F5.loC CFSG.KD.F5.accC 1
    CFSG.KD.F5.okC_all

theorem F6facts : Nat.beq (LceS.runFacts CFSG.KD.F6.blk CFSG.KD.F6.selWT CFSG.KD.F6.INV CFSG.KD.F6.nC
    (nat_lit 12) (seg CFSG.KD.F6.JF (Nat.sub (CFSG.KD.F6.loF 1) (CFSG.KD.F6.loF 0)) (CFSG.KD.F6.loF 0))
    (CFSG.KD.F6.accF 0)) (CFSG.KD.F6.accF 1) = true :=
  facts_chain _ _ _ _ (nat_lit 12) CFSG.KD.F6.JF CFSG.KD.F6.loF CFSG.KD.F6.accF 1 CFSG.KD.F6.okW_all

theorem F6cover : Nat.beq (LceS.runCover CFSG.KD.F6.blk CFSG.KD.F6.LVs (nat_lit 162) (nat_lit 12)
    (seg CFSG.KD.F6.JV (Nat.sub (CFSG.KD.F6.loC 1) (CFSG.KD.F6.loC 0)) (CFSG.KD.F6.loC 0))
    (CFSG.KD.F6.accC 0)) (CFSG.KD.F6.accC 1) = true :=
  cover_chain _ _ (nat_lit 162) (nat_lit 12) CFSG.KD.F6.JV CFSG.KD.F6.loC CFSG.KD.F6.accC 1
    CFSG.KD.F6.okC_all

theorem F7facts : Nat.beq (LceS.runFacts CFSG.KD.F7.blk CFSG.KD.F7.selWT CFSG.KD.F7.INV CFSG.KD.F7.nC
    (nat_lit 10) (seg CFSG.KD.F7.JF (Nat.sub (CFSG.KD.F7.loF 1) (CFSG.KD.F7.loF 0)) (CFSG.KD.F7.loF 0))
    (CFSG.KD.F7.accF 0)) (CFSG.KD.F7.accF 1) = true :=
  facts_chain _ _ _ _ (nat_lit 10) CFSG.KD.F7.JF CFSG.KD.F7.loF CFSG.KD.F7.accF 1 CFSG.KD.F7.okW_all

theorem F7cover : Nat.beq (LceS.runCover CFSG.KD.F7.blk CFSG.KD.F7.LVs (nat_lit 50) (nat_lit 10)
    (seg CFSG.KD.F7.JV (Nat.sub (CFSG.KD.F7.loC 1) (CFSG.KD.F7.loC 0)) (CFSG.KD.F7.loC 0))
    (CFSG.KD.F7.accC 0)) (CFSG.KD.F7.accC 1) = true :=
  cover_chain _ _ (nat_lit 50) (nat_lit 10) CFSG.KD.F7.JV CFSG.KD.F7.loC CFSG.KD.F7.accC 1
    CFSG.KD.F7.okC_all

theorem F8facts : Nat.beq (LceS.runFacts CFSG.KD.F8.blk CFSG.KD.F8.selWT CFSG.KD.F8.INV CFSG.KD.F8.nC
    (nat_lit 8) (seg CFSG.KD.F8.JF (Nat.sub (CFSG.KD.F8.loF 1) (CFSG.KD.F8.loF 0)) (CFSG.KD.F8.loF 0))
    (CFSG.KD.F8.accF 0)) (CFSG.KD.F8.accF 1) = true :=
  facts_chain _ _ _ _ (nat_lit 8) CFSG.KD.F8.JF CFSG.KD.F8.loF CFSG.KD.F8.accF 1 CFSG.KD.F8.okW_all

theorem F8cover : Nat.beq (LceS.runCover CFSG.KD.F8.blk CFSG.KD.F8.LVs (nat_lit 32) (nat_lit 8)
    (seg CFSG.KD.F8.JV (Nat.sub (CFSG.KD.F8.loC 1) (CFSG.KD.F8.loC 0)) (CFSG.KD.F8.loC 0))
    (CFSG.KD.F8.accC 0)) (CFSG.KD.F8.accC 1) = true :=
  cover_chain _ _ (nat_lit 32) (nat_lit 8) CFSG.KD.F8.JV CFSG.KD.F8.loC CFSG.KD.F8.accC 1
    CFSG.KD.F8.okC_all

theorem F9facts : Nat.beq (LceS.runFacts CFSG.KD.F9.blk CFSG.KD.F9.selWT CFSG.KD.F9.INV CFSG.KD.F9.nC
    (nat_lit 6) (seg CFSG.KD.F9.JF (Nat.sub (CFSG.KD.F9.loF 1) (CFSG.KD.F9.loF 0)) (CFSG.KD.F9.loF 0))
    (CFSG.KD.F9.accF 0)) (CFSG.KD.F9.accF 1) = true :=
  facts_chain _ _ _ _ (nat_lit 6) CFSG.KD.F9.JF CFSG.KD.F9.loF CFSG.KD.F9.accF 1 CFSG.KD.F9.okW_all

theorem F9cover : Nat.beq (LceS.runCover CFSG.KD.F9.blk CFSG.KD.F9.LVs (nat_lit 12) (nat_lit 6)
    (seg CFSG.KD.F9.JV (Nat.sub (CFSG.KD.F9.loC 1) (CFSG.KD.F9.loC 0)) (CFSG.KD.F9.loC 0))
    (CFSG.KD.F9.accC 0)) (CFSG.KD.F9.accC 1) = true :=
  cover_chain _ _ (nat_lit 12) (nat_lit 6) CFSG.KD.F9.JV CFSG.KD.F9.loC CFSG.KD.F9.accC 1
    CFSG.KD.F9.okC_all

theorem F10facts : Nat.beq (LceS.runFacts CFSG.KD.F10.blk CFSG.KD.F10.selWT CFSG.KD.F10.INV
    CFSG.KD.F10.nC (nat_lit 4)
    (seg CFSG.KD.F10.JF (Nat.sub (CFSG.KD.F10.loF 1) (CFSG.KD.F10.loF 0)) (CFSG.KD.F10.loF 0))
    (CFSG.KD.F10.accF 0)) (CFSG.KD.F10.accF 1) = true :=
  facts_chain _ _ _ _ (nat_lit 4) CFSG.KD.F10.JF CFSG.KD.F10.loF CFSG.KD.F10.accF 1
    CFSG.KD.F10.okW_all

theorem F10cover : Nat.beq (LceS.runCover CFSG.KD.F10.blk CFSG.KD.F10.LVs (nat_lit 6) (nat_lit 4)
    (seg CFSG.KD.F10.JV (Nat.sub (CFSG.KD.F10.loC 1) (CFSG.KD.F10.loC 0)) (CFSG.KD.F10.loC 0))
    (CFSG.KD.F10.accC 0)) (CFSG.KD.F10.accC 1) = true :=
  cover_chain _ _ (nat_lit 6) (nat_lit 4) CFSG.KD.F10.JV CFSG.KD.F10.loC CFSG.KD.F10.accC 1
    CFSG.KD.F10.okC_all

theorem F11facts : Nat.beq (LceS.runFacts CFSG.KD.F11.blk CFSG.KD.F11.selWT CFSG.KD.F11.INV
    CFSG.KD.F11.nC (nat_lit 2)
    (seg CFSG.KD.F11.JF (Nat.sub (CFSG.KD.F11.loF 1) (CFSG.KD.F11.loF 0)) (CFSG.KD.F11.loF 0))
    (CFSG.KD.F11.accF 0)) (CFSG.KD.F11.accF 1) = true :=
  facts_chain _ _ _ _ (nat_lit 2) CFSG.KD.F11.JF CFSG.KD.F11.loF CFSG.KD.F11.accF 1
    CFSG.KD.F11.okW_all

theorem F11cover : Nat.beq (LceS.runCover CFSG.KD.F11.blk CFSG.KD.F11.LVs (nat_lit 2) (nat_lit 2)
    (seg CFSG.KD.F11.JV (Nat.sub (CFSG.KD.F11.loC 1) (CFSG.KD.F11.loC 0)) (CFSG.KD.F11.loC 0))
    (CFSG.KD.F11.accC 0)) (CFSG.KD.F11.accC 1) = true :=
  cover_chain _ _ (nat_lit 2) (nat_lit 2) CFSG.KD.F11.JV CFSG.KD.F11.loC CFSG.KD.F11.accC 1
    CFSG.KD.F11.okC_all

end CertificateChecks.KernelFi24

end
