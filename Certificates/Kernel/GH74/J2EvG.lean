module

public import Certificates.Kernel.GH74.J2EvF
public import Certificates.Kernel.GH74.Derived
public import Certificates.Kernel.GH74.EvSound
public import Certificates.Kernel.GH74.J2Cent5

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.J2Ev

open Subgroup
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.GH74
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native
open CFSG.GH74.Generic.S45.EvSpor CertificateChecks.KernelGH74
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn
open scoped commutatorElement

theorem cb_gen {s : Equiv.Perm (Fin 315)} (hs : s ∈ tp 315 '' {x | x ∈ j2Row2B.centGens.toArray}) :
    ∃ j < 5, s = tp 315 (tabT (unpack 315 9 (J2CB.GI j))) ∧
      Rep 315 (tabT (unpack 315 9 (J2CB.GI j))) s := by
  obtain ⟨x, hx, rfl⟩ := hs
  have hx' : x ∈ j2Row2B.centGens := List.mem_toArray.1 hx
  have hr := (enumOK_spec (by norm_num) cb_enum).2.2 x hx'
  obtain ⟨j, hj, rfl, -⟩ := TabsOK_list cb_tabs hx'
  exact ⟨j, hj, rfl, hr⟩

theorem cb_inv {j : Nat} (hj : j < 5) {s : Equiv.Perm (Fin 315)}
    (hr : Rep 315 (tabT (unpack 315 9 (J2CB.GI j))) s) :
    Rep 315 (tabT (unpack 315 9 (J2CentI (Nat.add 18 j)))) s⁻¹ := by
  have := rep_invT_of_rep (by norm_num) hr
  rwa [invT_unpack (by norm_num) (cb_invs j hj).1] at this

theorem kb_gen {k : Equiv.Perm (Fin 315)} (hk : k ∈ tp 315 '' {x | x ∈ j2KbGens.toArray}) :
    ∃ l < 2, Rep 315 (tabT (unpack 315 9 (J2XT l))) k := by
  obtain ⟨x, hx, rfl⟩ := hk
  have hx' : x ∈ j2KbGens := List.mem_toArray.1 hx
  have hr := (enumOK_spec (by norm_num) kb_enum).2.2 x hx'
  simp only [j2KbGens, List.mem_cons, List.not_mem_nil, or_false] at hx'
  rcases hx' with rfl | rfl
  · exact ⟨0, by norm_num, by rw [← x_tabs.1]; exact hr⟩
  · exact ⟨1, by norm_num, by rw [← x_tabs.2.1]; exact hr⟩

theorem cbc {j : Nat} (hj : j < 5) : canonK 315 9 (mask 9) (315 * 9) (J2CB.GI j) = true :=
  (cb_tabs.2 j hj).2

theorem derived_ok : j2DerivedOK = true := by
  have hn : (315 : Nat) < 2 ^ 32 := by norm_num
  obtain ⟨hEB, -, -⟩ := enumOK_spec hn cb_enum
  obtain ⟨hEK, -, -⟩ := enumOK_spec hn kb_enum
  have hnorm : ∀ s ∈ tp 315 '' {x | x ∈ j2Row2B.centGens.toArray},
      ∀ m ∈ closure (tp 315 '' {x | x ∈ j2KbGens.toArray}),
      s * m * s⁻¹ ∈ closure (tp 315 '' {x | x ∈ j2KbGens.toArray}) := by
    intro s hs
    obtain ⟨j, hj, -, hrs⟩ := cb_gen hs
    refine conj_mem_closure fun k hk => ?_
    obtain ⟨l, hl, hrk⟩ := kb_gen hk
    have hX := (xp (j := l) (by omega)).1
    have e : kbQ (2 * j + l) = pc (pc (J2CB.GI j) (J2XT l)) (J2CentI (Nat.add 18 j)) := by
      interval_cases j <;> interval_cases l <;> rfl
    have hrep : Rep 315 (tabT (unpack 315 9 (kbQ (2 * j + l)))) (s * k * s⁻¹) := by
      rw [e]
      unfold pc
      rw [← compT_unpack (CFSG.KC.BfsPin.canonK_pcomp (cbc hj) hX) (cb_invs j hj).2,
        ← compT_unpack (cbc hj) hX]
      exact Rep.compT (Rep.compT hrs hrk) (cb_inv hj hrs)
    exact (hEK.mem_iff hrep).1 (kbQ_mem (by omega))
  have hcomm : ∀ s ∈ tp 315 '' {x | x ∈ j2Row2B.centGens.toArray},
      ∀ t ∈ tp 315 '' {x | x ∈ j2Row2B.centGens.toArray},
      ⁅s, t⁆ ∈ closure (tp 315 '' {x | x ∈ j2KbGens.toArray}) := by
    intro s hs t ht
    obtain ⟨i, hi, -, hrs⟩ := cb_gen hs
    obtain ⟨j, hj, -, hrt⟩ := cb_gen ht
    have e : kbQ (10 + 5 * i + j) = pc (pc (J2CB.GI i) (J2CB.GI j))
        (pc (J2CentI (Nat.add 18 i)) (J2CentI (Nat.add 18 j))) := by
      interval_cases i <;> interval_cases j <;> rfl
    have hrep : Rep 315 (tabT (unpack 315 9 (kbQ (10 + 5 * i + j)))) ⁅s, t⁆ := by
      rw [e, commutatorElement_def, mul_assoc (s * t)]
      unfold pc
      rw [← compT_unpack (CFSG.KC.BfsPin.canonK_pcomp (cbc hi) (cbc hj))
        (CFSG.KC.BfsPin.canonK_pcomp (cb_invs i hi).2 (cb_invs j hj).2),
        ← compT_unpack (cbc hi) (cbc hj), ← compT_unpack (cb_invs i hi).2 (cb_invs j hj).2]
      exact Rep.compT (Rep.compT hrs hrt) (Rep.compT (cb_inv hi hrs) (cb_inv hj hrt))
    exact (hEK.mem_iff hrep).1 (kbQ_mem (by omega))
  have hBK := comm_mem_of_gens hnorm hcomm
  unfold j2DerivedOK derivedInOK
  rw [Array.all_eq_true]
  intro a ha
  obtain ⟨gx, hgx, hrx⟩ := hEB.1 a ha
  rw [← getElem!_pos j2C2B a ha, Array.all_eq_true]
  intro b hb
  obtain ⟨gy, hgy, hry⟩ := hEB.1 b hb
  rw [← getElem!_pos j2C2B b hb]
  have hrep : Rep 315 (compT 315 (compT 315 j2C2B[a]! j2C2B[b]!)
      (compT 315 (invT 315 j2C2B[a]!) (invT 315 j2C2B[b]!))) ⁅gx, gy⁆ := by
    rw [commutatorElement_def, mul_assoc (gx * gy)]
    exact Rep.compT (Rep.compT hrx hry)
      (Rep.compT (rep_invT_of_rep hn hrx) (rep_invT_of_rep hn hry))
  exact (hEK.mem_iff hrep).2 (hBK gx hgx gy hgy)

theorem bIf_true_right (c t : Bool) : bIf(c, t, true) = (!c || t) := by cases c <;> rfl

theorem bIf_true_mid (c e : Bool) : bIf(c, true, e) = (c || e) := by cases c <;> rfl

theorem c2c {k : Nat} (hk : k < J2C2.cnt) : canonK 315 9 (mask 9) (315 * 9) (J2C2.T k) = true :=
  penumPt_canon (J2Loc.c2_pe k hk)

theorem cent5_at {k : Nat} (hk : k < J2C2.cnt) :
    cent5At 315 9 J2C2.cnt J2C2.T (F 31) (J2XT 2) (J2C2.T k) = true := by
  have hc : J2C2.cnt = 64 * 30 := rfl
  have hk' : k / 64 < 30 := by omega
  have hs := J2Cent5.all (k / 64) hk'
  have h := allBlk_spec hs (k % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 64 (k / 64)) (k % 64) = k := Nat.div_add_mod k 64
  rw [e] at h
  exact h

theorem cent5_ok : j2Cent5OK = true := by
  have c31 := Fc (by norm_num : 31 < 42)
  have cV := (xp (j := 2) (by norm_num)).1
  unfold j2Cent5OK cent5OK
  rw [show j2Row2A.rep = j2CentTbl 31 from rfl, tabF (by norm_num : 31 < 42), x_tabs.2.2.1, c2_arr,
    all_hRec_iff]
  intro k hk
  have hz := c2c hk
  have hs := cent5_at hk
  rw [ord5K_eq hz]
  cases h5 : ord5K 315 9 (J2C2.T k)
  · rfl
  have hb := cent5Body_of h5 hs
  unfold cent5Body at hb
  obtain ⟨hA, hB⟩ := (bAnd_iff _ _).1 hb
  have hpw : ∀ e, pw (e + 1) (J2C2.T k) = pc (J2C2.T k) (pw e (J2C2.T k)) := (pows _).2
  have hpw0 : pw 0 (J2C2.T k) = pidn 315 9 := (pows _).1
  have hpT := powT_unpack (pows (J2C2.T k)) hid hidc hz
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [all_hRec_iff]
    intro i hi
    have hT := c2c hi
    have h1 := allN_spec hA i hi
    have ht : ∀ j, tblEq 315 (tabT (unpack 315 9 (J2C2.T i)))
        (tabT (unpack 315 9 (pw j (J2C2.T k)))) = Nat.beq (J2C2.T i) (pw j (J2C2.T k)) :=
      fun j => tblEq_unpack hT (canonP hz j)
    have hct : ∀ j, compT 315 (tabT (unpack 315 9 (F 31))) (tabT (unpack 315 9 (pw j (J2C2.T k)))) =
        tabT (unpack 315 9 (pc (F 31) (pw j (J2C2.T k)))) :=
      fun j => compT_unpack c31 (canonP hz j)
    have ht2 : ∀ j, tblEq 315 (tabT (unpack 315 9 (J2C2.T i)))
        (tabT (unpack 315 9 (pc (F 31) (pw j (J2C2.T k))))) =
          Nat.beq (J2C2.T i) (pc (F 31) (pw j (J2C2.T k))) :=
      fun j => tblEq_unpack hT (CFSG.KC.BfsPin.canonK_pcomp c31 (canonP hz j))
    rw [commF hT hz, show List.range 5 = [0, 1, 2, 3, 4] from rfl]
    simp only [hpT, hct, ht, ht2, List.any_cons, List.any_nil, Bool.or_false, hpw, hpw0]
    rw [pcommK_eq hT hz] at h1
    simp only [bIf_true_right, bIf_true_mid] at h1
    simp only [Bool.or_assoc]
    exact h1
  · rw [all_hRec_iff]
    intro i hi
    have hT := c2c hi
    have h1 := allN_spec hB i hi
    rw [pcomm2K_eq cV hT hz, bIf_not] at h1
    rw [compT_unpack cV hT, commF (CFSG.KC.BfsPin.canonK_pcomp cV hT) hz]
    exact h1

end CertificateChecks.KernelGH74.J2Ev

end
