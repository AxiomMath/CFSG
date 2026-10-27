module

public import Certificates.Kernel.Fi24PG10.Rels
import Certificates.Kernel.Co2.Intro
import Certificates.Kernel.Fi24PG10.Facts2
import Certificates.Kernel.Fi24PG10.Facts3
import Certificates.Kernel.Fi24PG10.Facts4
import Certificates.Kernel.Fi24PG10.Facts5
import Certificates.Kernel.Fi24PG10.Facts6
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Fi24.PG10.Slices.Head
public import CFSG.Sporadic.Presentation.Common
public import Mathlib

public section

namespace CertificateChecks.KernelPG10

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

abbrev Tab {G : Type*} [Group G] (g : ℕ → G) (ST : ℕ → ℕ) (nS L a : ℕ) : Prop :=
  (Subgroup.closure ((fun j => bval g (wWord (ST j)) (wLen (ST j))) '' {j | j < nS})).relIndex
      (Subgroup.closure (g '' {g' | 2 * g' < L})) ≠ 0 ∧
    (Subgroup.closure ((fun j => bval g (wWord (ST j)) (wLen (ST j))) '' {j | j < nS})).relIndex
      (Subgroup.closure (g '' {g' | 2 * g' < L})) ≤ a

theorem t2 : Tab (gen A2) CFSG.KD.PG10P2.selST (nat_lit 8) (nat_lit 18) (nat_lit 28431) :=
  lceOk_sound (lceOk_intro CFSG.KD.PG10P2.sH1 CFSG.KD.PG10P2.sH0 (by quickRfl) CFSG.KD.PG10P2.sH2
    CFSG.KD.PG10P2.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    P2facts (by quickRfl) (by quickRfl) P2cover (by quickRfl)) (gen A2) r2

theorem t3 : Tab (gen A3) CFSG.KD.PG10P3.selST (nat_lit 7) (nat_lit 16) (nat_lit 120) :=
  lceOk_sound (lceOk_intro CFSG.KD.PG10P3.sH1 CFSG.KD.PG10P3.sH0 (by quickRfl) CFSG.KD.PG10P3.sH2
    CFSG.KD.PG10P3.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    P3facts (by quickRfl) (by quickRfl) P3cover (by quickRfl)) (gen A3) r3

theorem t4 : Tab (gen A4) CFSG.KD.PG10P4.selST (nat_lit 6) (nat_lit 14) (nat_lit 1) :=
  lceOk_sound (lceOk_intro CFSG.KD.PG10P4.sH1 CFSG.KD.PG10P4.sH0 (by quickRfl) CFSG.KD.PG10P4.sH2
    CFSG.KD.PG10P4.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    P4facts (by quickRfl) (by quickRfl) P4cover (by quickRfl)) (gen A4) r4

theorem t5 : Tab (gen A5) CFSG.KD.PG10P5.selST (nat_lit 5) (nat_lit 12) (nat_lit 576) :=
  lceOk_sound (lceOk_intro CFSG.KD.PG10P5.sH1 CFSG.KD.PG10P5.sH0 (by quickRfl) CFSG.KD.PG10P5.sH2
    CFSG.KD.PG10P5.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    P5facts (by quickRfl) (by quickRfl) P5cover (by quickRfl)) (gen A5) r5

theorem t6 : Tab (gen A6) CFSG.KD.PG10P6.selST (nat_lit 0) (nat_lit 10) (nat_lit 2520) :=
  lceOk_sound (lceOk_intro CFSG.KD.PG10P6.sH1 CFSG.KD.PG10P6.sH0 (by quickRfl) CFSG.KD.PG10P6.sH2
    CFSG.KD.PG10P6.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    P6facts (by quickRfl) (by quickRfl) P6cover (by quickRfl)) (gen A6) r6

end CertificateChecks.KernelPG10

end
