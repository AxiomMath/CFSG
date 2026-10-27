
module

public import Certificates.Kernel.SporSch.Co1.OrbX1
public import Certificates.Kernel.SporSch.Co1.OrbX3
public import Certificates.Kernel.SporSch.Co1.OrbX61
public import Certificates.Kernel.SporSch.Co1.OrbF2
public import CFSG.Certificates.Kernel.SporSch.Co1StabSound
public import CFSG.Certificates.Kernel.SporSch.Co1VOrbSound
public meta import Certificates.Kernel.SporSch.GenPerms
public meta import CFSG.Sporadic.Schreier.Co1StabCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.SporSch.GenPerms

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Stab2148

meta def HA : Array (Array Nat) :=
  #[CFSG.Sporadic.Co1Schreier.Native.inv CFSG.Sporadic.Co1Schreier.Native.hRows0,
    CFSG.Sporadic.Co1Schreier.Native.inv CFSG.Sporadic.Co1Schreier.Native.hRows1]

end CertificateChecks.KernelSporSch.Co1Stab2148

#kss_perms CertificateChecks.KernelSporSch.Co1Stab2148.HI 24
  CertificateChecks.KernelSporSch.Co1Stab2148.HA

namespace CertificateChecks.KernelSporSch.Co1Stab2148

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelSporSch.Co1Stab CertificateChecks.KernelSporSch.Co1Packed
open CertificateChecks.KernelSporSch.Co1Orbs

@[expose] noncomputable def HM (i : Nat) : Nat := nIf(Nat.beq i 0, PH0, PH1)

@[expose] noncomputable def BF (A B v n : Nat) : VOrbit :=
  vOrbitBFS 24 (transposeRows 24 (unpack 24 24 A)) (transposeRows 24 (unpack 24 24 B)) v n

theorem k0 : invOKK PH0 (HI 0) = true := by quickRfl
theorem k1 : invOKK PH1 (HI 1) = true := by quickRfl
theorem kW : witK HM HI Data.fixWords Data.stabVecs = true := by quickRfl
theorem kF : fixK HM HI Data.fixWords Data.fixFree Data.fixSteps Data.stabVecs = true := by quickRfl

theorem x0 : memK F2.T F2.S 98280 16663704 = true := by quickRfl
theorem x1 : memK F2.T F2.S 98280 6009710 = true := by quickRfl
theorem x2 : memK F2.T F2.S 98280 769771 = true := by quickRfl
theorem x3 : memK F2.T F2.S 98280 6244414 = true := by quickRfl

theorem false_of {b : Bool} (h : Bool.not b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem m10 : memK O1.T O1.S 46575 0 = false := false_of (by quickRfl)
theorem m11 : memK O1.T O1.S 46575 16663704 = false := false_of (by quickRfl)
theorem m12 : memK O1.T O1.S 46575 (16663704 ^^^ 6009710) = false := false_of (by quickRfl)
theorem m20 : memK O2.T O2.S 47104 0 = false := false_of (by quickRfl)
theorem m21 : memK O2.T O2.S 47104 16663704 = false := false_of (by quickRfl)
theorem m22 : memK O2.T O2.S 47104 (16663704 ^^^ 769771) = false := false_of (by quickRfl)
theorem m30 : memK O3.T O3.S 4600 0 = false := false_of (by quickRfl)
theorem m31 : memK O3.T O3.S 4600 16663704 = false := false_of (by quickRfl)
theorem m32 : memK O3.T O3.S 4600 (16663704 ^^^ 6244414) = true := by quickRfl

theorem wf_unpack (X : Nat) : wf (unpack 24 24 X) = true := by
  unfold wf
  rw [Bool.and_eq_true]
  refine ⟨by simp [unpack], ?_⟩
  rw [Array.all_iff_forall]
  intro i hi _
  simp only [unpack, Array.getElem_ofFn, CFSG.KC.Enum.pg, decide_eq_true_eq]
  unfold CFSG.KS.mask
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem hm0 : HM 0 = PH0 := rfl
theorem hm1 : HM 1 = PH1 := rfl

theorem h0u : hRows0 = unpack 24 24 PH0 := h0_eq.trans (rows_of b0)
theorem h1u : hRows1 = unpack 24 24 PH1 := h1_eq.trans (rows_of b1)

theorem i0 : inv hRows0 = unpack 24 24 (HI 0) := by
  rw [h0u]
  exact (invOKK_sound k0).2

theorem i1 : inv hRows1 = unpack 24 24 (HI 1) := by
  rw [h1u]
  exact (invOKK_sound k1).2

theorem e0 : enumOK (transposeRows 24 (unpack 24 24 PH0)) (transposeRows 24 (unpack 24 24 PH1))
    16663704 1 (BF PH0 PH1 16663704 1) = true :=
  (vorbK_sound O0.hr (by decide) (by decide) (by decide) O0.hc0 O0.hcN O0.hb O0.hp).1

theorem e1 : enumOK (transposeRows 24 (unpack 24 24 PH0)) (transposeRows 24 (unpack 24 24 PH1))
    6009710 46575 (BF PH0 PH1 6009710 46575) = true :=
  (vorbK_sound O1.hr (by decide) (by decide) (by decide) O1.hc0 O1.hcN O1.hb O1.hp).1

theorem e2 : enumOK (transposeRows 24 (unpack 24 24 PH0)) (transposeRows 24 (unpack 24 24 PH1))
    769771 47104 (BF PH0 PH1 769771 47104) = true :=
  (vorbK_sound O2.hr (by decide) (by decide) (by decide) O2.hc0 O2.hcN O2.hb O2.hp).1

theorem e3 : enumOK (transposeRows 24 (unpack 24 24 PH0)) (transposeRows 24 (unpack 24 24 PH1))
    6244414 4600 (BF PH0 PH1 6244414 4600) = true :=
  (vorbK_sound O3.hr (by decide) (by decide) (by decide) O3.hc0 O3.hcN O3.hb O3.hp).1

theorem q1 (n' : Nat) (hn : n' = 46575) (v : Nat) :
    ((List.range n').any fun i => (BF PH0 PH1 6009710 46575).pts[i]! == v) =
      memK O1.T O1.S 46575 v := by
  subst hn
  exact (vorbK_sound O1.hr (by decide) (by decide) (by decide) O1.hc0 O1.hcN O1.hb O1.hp).2.2.2 v

theorem q2 (n' : Nat) (hn : n' = 47104) (v : Nat) :
    ((List.range n').any fun i => (BF PH0 PH1 769771 47104).pts[i]! == v) =
      memK O2.T O2.S 47104 v := by
  subst hn
  exact (vorbK_sound O2.hr (by decide) (by decide) (by decide) O2.hc0 O2.hcN O2.hb O2.hp).2.2.2 v

theorem q3 (n' : Nat) (hn : n' = 4600) (v : Nat) :
    ((List.range n').any fun i => (BF PH0 PH1 6244414 4600).pts[i]! == v) =
      memK O3.T O3.S 4600 v := by
  subst hn
  exact (vorbK_sound O3.hr (by decide) (by decide) (by decide) O3.hc0 O3.hcN O3.hb O3.hp).2.2.2 v

theorem qF (v : Nat) :
    ((List.range 98280).any fun i => (BF PA PB 2 98280).pts[i]! == v) = memK F2.T F2.S 98280 v :=
  (vorbK_sound F2.hr (by decide) (by decide) (by decide) F2.hc0 F2.hcN F2.hb F2.hp).2.2.2 v

theorem so (k : Nat) : stabOrb k = BF PH0 PH1 (stabVec k) (stabSize k) := by
  unfold stabOrb BF
  rw [h0u, h1u]

theorem so1 : stabOrb (0 + 1) = BF PH0 PH1 6009710 46575 := so 1
theorem so2 : stabOrb (1 + 1) = BF PH0 PH1 769771 47104 := so 2
theorem so3 : stabOrb (2 + 1) = BF PH0 PH1 6244414 4600 := so 3

theorem full2 : fullOrb 2 = BF PA PB 2 98280 := by
  have hA : CFSG.Sporadic.Co1.Native.co1Data.colsA =
      transposeRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsA := rfl
  have hB : CFSG.Sporadic.Co1.Native.co1Data.colsB =
      transposeRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsB := rfl
  unfold fullOrb BF
  rw [hA, hB, Co1Rows.rowsA_eq, Co1Rows.rowsB_eq, uA, uB]
  rfl

theorem orb : stabOrbCheck = true := by
  unfold stabOrbCheck
  rw [i0, i1, h0u, h1u, (invOKK_sound k0).1, (invOKK_sound k1).1, wf_unpack, wf_unpack]
  simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true, List.mem_range]
  intro k hk
  rw [so]
  interval_cases k
  exacts [e0, e1, e2, e3]

theorem x : stabXCheck = true := by
  unfold stabXCheck stabXCheckOf
  rw [full2]
  simp only [qF, List.all_eq_true, List.mem_range]
  intro k hk
  interval_cases k
  exacts [x0, x1, x2, x3]

theorem wit : witCheck = true := by
  have h : witCheck = witCheckP Data.fixWords [hRows0, hRows1] [inv hRows0, inv hRows1]
      Data.stabVecs := by
    unfold witCheck witRows stabVec witCheckP witRowsP
    rfl
  rw [h, i0, i1, h0u, h1u, ← hm0, ← hm1]
  exact witK_sound kW

theorem fix : fixCheck = true := by
  have h : fixCheck = fixCheckP Data.fixWords [hRows0, hRows1] [inv hRows0, inv hRows1]
      Data.fixFree Data.fixSteps Data.stabVecs := by
    unfold fixCheck fixCheckOf witRows nonFree fixFreeOf fixStepsOf fixComb fixCoef stabVec
      fixCheckP fixCheckOfP witRowsP fixCombP fixCoefP
    rfl
  rw [h, i0, i1, h0u, h1u, ← hm0, ← hm1]
  exact fixK_sound kW kF

theorem mc0 : memCheckOf 0 (stabOrb (0 + 1)) = true := by
  unfold memCheckOf inEnum
  rw [so1]
  simp only [q1 (stabSize (0 + 1)) rfl]
  rw [m10]
  change (!false && !memK O1.T O1.S 46575 16663704 &&
    memK O1.T O1.S 46575 (16663704 ^^^ 6009710) == (0 == 2)) = true
  rw [m11, m12]
  rfl

theorem mc1 : memCheckOf 1 (stabOrb (1 + 1)) = true := by
  unfold memCheckOf inEnum
  rw [so2]
  simp only [q2 (stabSize (1 + 1)) rfl]
  rw [m20]
  change (!false && !memK O2.T O2.S 47104 16663704 &&
    memK O2.T O2.S 47104 (16663704 ^^^ 769771) == (1 == 2)) = true
  rw [m21, m22]
  rfl

theorem mc2 : memCheckOf 2 (stabOrb (2 + 1)) = true := by
  unfold memCheckOf inEnum
  rw [so3]
  simp only [q3 (stabSize (2 + 1)) rfl]
  rw [m30]
  change (!false && !memK O3.T O3.S 4600 16663704 &&
    memK O3.T O3.S 4600 (16663704 ^^^ 6244414) == (2 == 2)) = true
  rw [m31, m32]
  rfl

theorem mem : memCheck = true := by
  unfold memCheck
  simp only [List.all_eq_true, List.mem_range]
  intro m hm
  interval_cases m
  exacts [mc0, mc1, mc2]

end CertificateChecks.KernelSporSch.Co1Stab2148

end
