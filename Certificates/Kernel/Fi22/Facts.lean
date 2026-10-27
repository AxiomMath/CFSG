module

public import Certificates.Kernel.Co2.Join
public import CFSG.Certificates.Kernel.Fi22.Bound2.Lab
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.X1_Sel
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.X2_Sel
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.X3_Sel
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.C_Sel
public import CFSG.Certificates.Kernel.Fi22.Bound.Data.P_Sel
public import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.X
public import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.C_W_0
public import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.C_L
public import CFSG.Certificates.Kernel.Fi22.Bound.Checks.P
import Certificates.Kernel.LceSTab.Chain

public section

namespace CertificateChecks.KernelFi22

open CFSG.KC CFSG.KC.Loop CertificateChecks.KernelCo2

theorem runLab_append (WT LB LETs : Nat → Nat) (Hs : Nat) :
    ∀ l1 l2 x, CFSG.KC.Fi22K.runLab WT LB LETs Hs (List.append l1 l2) x =
      CFSG.KC.Fi22K.runLab WT LB LETs Hs l2 (CFSG.KC.Fi22K.runLab WT LB LETs Hs l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (CFSG.KC.Fi22K.labChunk WT LB LETs Hs C x) (CFSG.KC.Fi22K.runLab WT LB LETs Hs (List.append l1 l2)) =
      CFSG.KC.Fi22K.runLab WT LB LETs Hs l2
        (strictN (CFSG.KC.Fi22K.labChunk WT LB LETs Hs C x) (CFSG.KC.Fi22K.runLab WT LB LETs Hs l1))
    rw [strictN_eq, strictN_eq, runLab_append WT LB LETs Hs l1 l2]

open CFSG.KC.LceS CFSG.KC.LceSeg in
theorem X1facts : Nat.beq (runFacts CFSG.KD.Fi22KX1.blk CFSG.KD.Fi22KX1.selWT CFSG.KD.Fi22KX1.INV
    CFSG.KD.Fi22KX1.nC (nat_lit 8) (seg CFSG.KD.Fi22KX1.JF
      (Nat.sub (CFSG.KD.Fi22KX1.loF 15) (CFSG.KD.Fi22KX1.loF 0)) (CFSG.KD.Fi22KX1.loF 0))
    (CFSG.KD.Fi22KX1.accF 0)) (CFSG.KD.Fi22KX1.accF 15) = true :=
  facts_chain _ _ _ _ _ _ _ _ 15 CFSG.KD.Fi22KX1.okW_all

open CFSG.KC.LceS CFSG.KC.LceSeg in
theorem X1cover : Nat.beq (runCover CFSG.KD.Fi22KX1.blk CFSG.KD.Fi22KX1.LVs (nat_lit 27648)
    (nat_lit 8) (seg CFSG.KD.Fi22KX1.JV
      (Nat.sub (CFSG.KD.Fi22KX1.loC 7) (CFSG.KD.Fi22KX1.loC 0)) (CFSG.KD.Fi22KX1.loC 0))
    (CFSG.KD.Fi22KX1.accC 0)) (CFSG.KD.Fi22KX1.accC 7) = true :=
  cover_chain _ _ _ _ _ _ _ 7 CFSG.KD.Fi22KX1.okC_all

open CFSG.KC.LceS CFSG.KC.LceSeg in
theorem X2facts : Nat.beq (runFacts CFSG.KD.Fi22KX2.blk CFSG.KD.Fi22KX2.selWT CFSG.KD.Fi22KX2.INV
    CFSG.KD.Fi22KX2.nC (nat_lit 10) (seg CFSG.KD.Fi22KX2.JF
      (Nat.sub (CFSG.KD.Fi22KX2.loF 13) (CFSG.KD.Fi22KX2.loF 0)) (CFSG.KD.Fi22KX2.loF 0))
    (CFSG.KD.Fi22KX2.accF 0)) (CFSG.KD.Fi22KX2.accF 13) = true :=
  facts_chain _ _ _ _ _ _ _ _ 13 CFSG.KD.Fi22KX2.okW_all

open CFSG.KC.LceS CFSG.KC.LceSeg in
theorem X2cover : Nat.beq (runCover CFSG.KD.Fi22KX2.blk CFSG.KD.Fi22KX2.LVs (nat_lit 20013)
    (nat_lit 10) (seg CFSG.KD.Fi22KX2.JV
      (Nat.sub (CFSG.KD.Fi22KX2.loC 5) (CFSG.KD.Fi22KX2.loC 0)) (CFSG.KD.Fi22KX2.loC 0))
    (CFSG.KD.Fi22KX2.accC 0)) (CFSG.KD.Fi22KX2.accC 5) = true :=
  cover_chain _ _ _ _ _ _ _ 5 CFSG.KD.Fi22KX2.okC_all

open CFSG.KC.LceS CFSG.KC.LceSeg in
theorem X3facts : Nat.beq (runFacts CFSG.KD.Fi22KX3.blk CFSG.KD.Fi22KX3.selWT CFSG.KD.Fi22KX3.INV
    CFSG.KD.Fi22KX3.nC (nat_lit 12) (seg CFSG.KD.Fi22KX3.JF
      (Nat.sub (CFSG.KD.Fi22KX3.loF 36) (CFSG.KD.Fi22KX3.loF 0)) (CFSG.KD.Fi22KX3.loF 0))
    (CFSG.KD.Fi22KX3.accF 0)) (CFSG.KD.Fi22KX3.accF 36) = true :=
  facts_chain _ _ _ _ _ _ _ _ 36 CFSG.KD.Fi22KX3.okW_all

open CFSG.KC.LceS CFSG.KC.LceSeg in
theorem X3cover : Nat.beq (runCover CFSG.KD.Fi22KX3.blk CFSG.KD.Fi22KX3.LVs (nat_lit 56235)
    (nat_lit 12) (seg CFSG.KD.Fi22KX3.JV
      (Nat.sub (CFSG.KD.Fi22KX3.loC 13) (CFSG.KD.Fi22KX3.loC 0)) (CFSG.KD.Fi22KX3.loC 0))
    (CFSG.KD.Fi22KX3.accC 0)) (CFSG.KD.Fi22KX3.accC 13) = true :=
  cover_chain _ _ _ _ _ _ _ 13 CFSG.KD.Fi22KX3.okC_all

#kc_join_range Cfacts runFacts_append CFSG.KD.Fi22KC "sW" 0 5
#kc_join_range Clab runLab_append CFSG.KD.Fi22KC "sL" 0 5

open CFSG.KC.LceS CFSG.KC.LceSeg in
theorem BPfacts : Nat.beq (runFacts CFSG.KD.Fi22BP.blk CFSG.KD.Fi22BP.selWT CFSG.KD.Fi22BP.INV
    CFSG.KD.Fi22BP.nC (nat_lit 4) (seg CFSG.KD.Fi22BP.JF
      (Nat.sub (CFSG.KD.Fi22BP.loF 41) (CFSG.KD.Fi22BP.loF 0)) (CFSG.KD.Fi22BP.loF 0))
    (CFSG.KD.Fi22BP.accF 0)) (CFSG.KD.Fi22BP.accF 41) = true :=
  facts_chain _ _ _ _ _ _ _ _ 41 CFSG.KD.Fi22BP.okW_all

open CFSG.KC.LceS CFSG.KC.LceSeg in
theorem BPcover : Nat.beq (runCover CFSG.KD.Fi22BP.blk CFSG.KD.Fi22BP.LVs (nat_lit 82571)
    (nat_lit 4) (seg CFSG.KD.Fi22BP.JV
      (Nat.sub (CFSG.KD.Fi22BP.loC 6) (CFSG.KD.Fi22BP.loC 0)) (CFSG.KD.Fi22BP.loC 0))
    (CFSG.KD.Fi22BP.accC 0)) (CFSG.KD.Fi22BP.accC 6) = true :=
  cover_chain _ _ _ _ _ _ _ 6 CFSG.KD.Fi22BP.okC_all

end CertificateChecks.KernelFi22

end
