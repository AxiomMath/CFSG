module

public import Certificates.Kernel.KDenseP.Tp3L
public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.MonoAll
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17489
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17494
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17495
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17540
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17541
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17542
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17543
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17544
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17598
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17613
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17614
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17615
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17616
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17617
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17618
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17619
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17625
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.R17626
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.LookChk
public import CFSG.Certificates.Kernel.KDenseP.LookSound
public import CFSG.Certificates.Kernel.KDenseP.ReplaySound
import Certificates.Kernel.KDenseP.MonoTabL
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.MonoEChk0
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.MonoEChk1
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.MonoEChk2
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.MonoEChk3

public section

namespace CertificateChecks.KernelKDenseP.MonFiveB

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CertificateChecks.KernelKDenseP.Axis
  CertificateChecks.KernelKDenseP.TwoPoint CFSG.Monster.AxisCount
  CFSG.HardMathSupport.Dickson.I271.MonsterFiveB

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.M5BM.MT = true := by
  kd_monoTabL CFSG.KD.M5BME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.M5BM.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

theorem look_eq : CFSG.KD.M5BL.look = fun k => findIdx k CFSG.KD.M5BM.MT.keys :=
  funext fun l => lookT_eq CFSG.KD.M5BL.tab_ok CFSG.KD.M5BL.len_ok l

theorem m5b_loc (b : List ℕ) :
    ∀ (S S' : ℕ → St) (c : ℕ), S (f20 c (nat_lit 3)) = S' (f20 c (nat_lit 3)) →
      S (f20 c (nat_lit 4)) = S' (f20 c (nat_lit 4)) →
      CFSG.KD.M5BL.chkBL b S c = CFSG.KD.M5BL.chkBL b S' c := by
  intro S S' c h3 h4
  unfold CFSG.KD.M5BL.chkBL chunkOKNL
  rw [h3, h4]

theorem m5b_prod (b : List ℕ) :
    ∀ (S : ℕ → St) (c : ℕ), Nat.beq (f20 c (nat_lit 5)) (nat_lit 1) = false →
      CFSG.KD.M5BL.chkBL b S c =
        stEqN 4 (CFSG.KD.M5BL.runCB b c (S (f20 c (nat_lit 3)))) (S (f20 c (nat_lit 4))) := by
  intro S c h
  unfold CFSG.KD.M5BL.chkBL chunkOKNL
  rw [h] <;> rfl

open Lean in
macro "kd_m5b% " pre:ident b:term:max : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  `((tp3L_sound CertificateChecks.KernelKDenseP.MonFiveB.data_ok (bEqsOf $b) [] (by quickRfl)
      (S := CFSG.KC.KDenseP.rlS (CFSG.KD.M5BL.runCB $b) $(n "CH") $(n "PRf") CFSG.KD.KDF.I 3)
      (fun x hx => CFSG.KC.KDenseP.rlS_lt hx) (CH := $(n "CH"))
      (nch := kd_count% $pre $(mkIdent `CH)) (IT := $(n "IT"))
      (fun k hk => CFSG.KC.KDenseP.chunkOKN_of_look CertificateChecks.KernelKDenseP.MonFiveB.look_eq
        (CFSG.KC.KDenseP.replay_sound (m5b_loc $b) (m5b_prod $b) (CH := $(n "CH"))
          (PR := $(n "PRf")) (GK := $(n "GKf")) (G := $(n "Gf")) (S0 := CFSG.KD.KDF.I) (w := 3)
          (ng := kd_count% $pre $(mkIdent `u)) (by kd_allE $pre $(mkIdent `u)) (by quickRfl) k hk))
      (by quickRfl) (by quickRfl)).1)

theorem c17489 : ∀ e ∈ bEqsOf [0, 14], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17489 [0, 14]
theorem c17494 : ∀ e ∈ bEqsOf [1, 10], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17494 [1, 10]
theorem c17495 : ∀ e ∈ bEqsOf [2, 9], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17495 [2, 9]
theorem c17540 : ∀ e ∈ bEqsOf [3, 25], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17540 [3, 25]
theorem c17541 : ∀ e ∈ bEqsOf [4, 19], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17541 [4, 19]
theorem c17542 : ∀ e ∈ bEqsOf [5, 29], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17542 [5, 29]
theorem c17543 : ∀ e ∈ bEqsOf [6, 20], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17543 [6, 20]
theorem c17544 : ∀ e ∈ bEqsOf [7, 23], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17544 [7, 23]
theorem c17598 : ∀ e ∈ bEqsOf [8, 11], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17598 [8, 11]
theorem c17613 : ∀ e ∈ bEqsOf [12, 15], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17613 [12, 15]
theorem c17614 : ∀ e ∈ bEqsOf [13], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17614 [13]
theorem c17615 : ∀ e ∈ bEqsOf [16, 26], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17615 [16, 26]
theorem c17616 : ∀ e ∈ bEqsOf [17, 22], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17616 [17, 22]
theorem c17617 : ∀ e ∈ bEqsOf [18], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17617 [18]
theorem c17618 : ∀ e ∈ bEqsOf [21], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17618 [21]
theorem c17619 : ∀ e ∈ bEqsOf [24], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17619 [24]
theorem c17625 : ∀ e ∈ bEqsOf [27, 28], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17625 [27, 28]
theorem c17626 : ∀ e ∈ bEqsOf [30], wordLin e.1 = wordLin e.2 := kd_m5b% CFSG.KD.M5B.c17626 [30]

end CertificateChecks.KernelKDenseP.MonFiveB

end
