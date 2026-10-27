module

public import Certificates.Kernel.J4Hub.Seeds
public import CFSG.Certificates.Kernel.J4Hub.RegSound
public import CFSG.Certificates.Kernel.J4Hub.DceSound
public import CFSG.Certificates.Kernel.Fam.J4.Checks.S0
public import CFSG.Certificates.Kernel.Fam.J4.Checks.S1
public import CFSG.Certificates.Kernel.Fam.J4.Checks.S2
public import CFSG.Certificates.Kernel.Fam.J4.Checks.O
public import CFSG.Certificates.Kernel.Fam.J4.Checks.R
public import CFSG.Certificates.Kernel.Fam.J4.Checks.C
public import CFSG.Certificates.Kernel.Fam.J4.Checks.F
public import CFSG.Certificates.Kernel.Fam.J4.Rels
public import CFSG.Sporadic.J4.Group
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.LceSP.Base
public import CFSG.Sporadic.J4.ParSpec
public import Certificates.Data.Kernel.LceSTab

public section

namespace CertificateChecks.KernelJ4Hub

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub CFSG.Sporadic.J4

noncomputable abbrev FMUL : Nat → Nat → Nat :=
  mulR 2 8 896 112 5 CFSG.KD.FamJ4.L CFSG.KD.FamJ4.H CFSG.KD.FamJ4.CM CFSG.KD.FamJ4.RM

noncomputable abbrev FV : Nat → Bool := validM 2 100352 CFSG.KD.FamJ4.L CFSG.KD.FamJ4.H

noncomputable abbrev FM (n : Nat) : Matrix (Fin 112) (Fin 112) (ZMod 2) := ordMat 2 112 8 896 n

@[expose] def GRxyt : Nat := nat_lit 150325559318

@[expose] def IRxyt : Nat := nat_lit 163211182116

@[expose] def zList : List (Nat × Bool) :=
  [(1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false),
    (1, false), (0, false), (1, false), (2, true), (1, true), (0, true), (1, true), (0, true),
    (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false),
    (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false),
    (1, false), (2, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
    (1, true), (0, true), (1, false), (0, true), (1, true), (0, false), (1, true), (0, false),
    (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (2, true),
    (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
    (1, false), (0, true)]

@[expose] def apList : List (Nat × Bool) :=
  [(1, true), (1, false), (1, true), (2, true), (1, true), (0, true), (2, true), (1, false),
    (0, true), (2, true), (2, true), (1, false), (1, true), (1, false), (1, true), (2, true),
    (1, true), (0, true), (2, true), (1, false), (0, true), (2, true), (2, true), (1, false),
    (1, true), (1, false), (1, true), (2, true), (1, true), (0, true), (2, true), (1, false),
    (0, true), (2, true), (2, true), (1, false), (1, true), (1, false), (1, true), (2, true),
    (1, true), (0, true), (2, true), (1, false), (0, true), (2, true), (2, true), (1, false)]

@[expose] def bpList : List (Nat × Bool) :=
  [(0, false), (2, false), (0, false), (0, false), (1, true), (0, false), (2, false), (1, true),
    (0, false), (2, false), (1, true), (1, false), (1, false), (1, true), (2, true), (0, true),
    (1, false), (0, true), (1, true), (0, true), (1, false), (2, true), (1, true), (1, false),
    (1, false), (1, true), (2, true), (0, true), (1, false), (0, true), (1, true), (0, true),
    (1, false), (2, true), (1, true), (1, false), (1, false), (1, true), (2, true), (0, true),
    (1, false), (0, true), (1, true), (0, true), (1, false), (2, true), (2, true), (0, true),
    (1, false), (2, true), (0, true), (1, false), (0, true), (0, true), (2, true), (0, true)]

theorem z_word : Nat.beq (CFSG.KC.Fam.wordProd CFSG.KD.FamJ4.RW FMUL CFSG.KD.FamJ4.ONE GRxyt IRxyt
    zList CFSG.KD.FamJ4.ONE) (CFSG.KD.FamJ4.RW 47) = true := by
  quickRfl

theorem ap_word : Nat.beq (CFSG.KC.Fam.wordProd CFSG.KD.FamJ4.RW FMUL CFSG.KD.FamJ4.ONE GRxyt IRxyt
    apList CFSG.KD.FamJ4.ONE) (CFSG.KD.FamJ4.RW 206) = true := by
  quickRfl

theorem bp_word : Nat.beq (CFSG.KC.Fam.wordProd CFSG.KD.FamJ4.RW FMUL CFSG.KD.FamJ4.ONE GRxyt IRxyt
    bpList CFSG.KD.FamJ4.ONE) (CFSG.KD.FamJ4.RW 238) = true := by
  quickRfl

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem fam_v1 : FV (CFSG.KD.FamJ4.RW 1) = true :=
  (andB_true (andB_true CFSG.KD.FamJ4.d1_end).2).2

theorem fam_v2 : FV (CFSG.KD.FamJ4.RW 2) = true :=
  (andB_true (andB_true CFSG.KD.FamJ4.d2_end).2).2

theorem matA_sq' : matA ^ 2 = 1 := by
  rw [matA, fam_A]
  exact (ordExact_sound' (hnb := rfl) CFSG.KD.FamJ4.consts (by norm_num) fam_v1
    CFSG.KD.FamJ4.o_A).2.2.1

theorem matB_pow4' : matB ^ 4 = 1 := by
  rw [matB, fam_B]
  exact (ordExact_sound' (hnb := rfl) CFSG.KD.FamJ4.consts (by norm_num) fam_v2
    CFSG.KD.FamJ4.o_B).2.2.1

theorem detA' : matA.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det matA_sq'
  rw [Matrix.det_pow, h, zero_pow two_ne_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem detB' : matB.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det matB_pow4'
  rw [Matrix.det_pow, h, zero_pow four_ne_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem gA_val' : ((gA : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) = matA := by
  unfold gA
  exact coe_dite_mk _ detA'

theorem gB_val' : ((gB : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) = matB := by
  unfold gB
  exact coe_dite_mk _ detB'

theorem regs3 : RegsIn 2 112 8 896 100352 CFSG.KD.FamJ4.L CFSG.KD.FamJ4.H J CFSG.KD.FamJ4.RW 3 := by
  intro r h0 h3
  obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
  · exact ⟨fam_v1, gA, Subgroup.subset_closure (Set.mem_insert _ _), by rw [gA_val', matA, fam_A]⟩
  · exact ⟨fam_v2, gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl),
      by rw [gB_val', matB, fam_B]⟩

local macro "regs_step" h:term:max t:term:max s:term:max : term =>
  `(slp_sound' (nb := nat_lit 100352) (hnb := rfl) CFSG.KD.FamJ4.consts $h $t $s)

open CFSG.KD.FamJ4 in
theorem fam_regs : RegsIn 2 112 8 896 100352 L H J RW 239 := by
  have h := regs_step regs3 ws0 (by norm_num)
  have h := regs_step h ws1 (by norm_num)
  exact regs_step h ws2 (by norm_num)

@[expose] noncomputable def fe (r : Nat) : GL (Fin 112) (ZMod 2) :=
  if h : 0 < r ∧ r < 239 then Classical.choose (fam_regs r h.1 h.2).2 else 1

theorem fe_spec {r : Nat} (h0 : 0 < r) (h1 : r < 239) :
    fe r ∈ J ∧ ((fe r : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) =
      FM (CFSG.KD.FamJ4.RW r) ∧ FV (CFSG.KD.FamJ4.RW r) = true := by
  have hs := Classical.choose_spec (fam_regs r h0 h1).2
  unfold fe
  rw [dite_eq_left (show 0 < r ∧ r < 239 from ⟨h0, h1⟩)]
  exact ⟨hs.1, hs.2, (fam_regs r h0 h1).1⟩

@[expose] noncomputable def feJ (r : Nat) : J :=
  if h : 0 < r ∧ r < 239 then ⟨fe r, (fe_spec h.1 h.2).1⟩ else 1

theorem feJ_val {r : Nat} (h0 : 0 < r) (h1 : r < 239) :
    (((feJ r : J) : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) =
      FM (CFSG.KD.FamJ4.RW r) := by
  unfold feJ
  rw [dite_eq_left (show 0 < r ∧ r < 239 from ⟨h0, h1⟩)]
  exact (fe_spec h0 h1).2.1

end CertificateChecks.KernelJ4Hub

end
