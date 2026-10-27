module

public import Certificates.Kernel.J3Ref.Bind
public import Certificates.Kernel.K426.J3TFacts
public import CFSG.Certificates.Kernel.Spor.PEnumBSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Misc.RuInvHash
public import CFSG.Certificates.Kernel.Spor.ClassOneH

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ3Ref

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnumB CertificateChecks.KernelSporSch
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KS.Raw.Orb

@[expose] def MJ (X : Nat) : Prop :=
  canonK 6156 13 (mask 13) (6156 * 13) X = true ∧
    ∃ A ∈ KernelK426J3.GJ, ∀ x : Fin 6156, pg 13 (mask 13) X x = (A x : Nat)

theorem szOK_j3 : szOK 6156 13 = true := by decide

theorem mj_faith : BaseFaith 6156 13 bsJ MJ where
  n_lt := by norm_num
  bs_lt := by decide
  canon := fun _ h => h.1
  eq := fun X Y hX hY h => by
    obtain ⟨hXc, A, hA, hXA⟩ := hX
    obtain ⟨hYc, B, hB, hYB⟩ := hY
    have hAB : A = B := KernelK426J3.eq_of_base hA hB fun b hb => by
      rw [← hXA, ← hYB]
      exact h b (by simpa [bsJ, KernelK426J3.bs] using hb)
    subst hAB
    obtain ⟨-, hw, hX0, -⟩ := PF.canon_facts hXc
    obtain ⟨-, -, hY0, -⟩ := PF.canon_facts hYc
    exact PF.eq_of_fields (PF.w_pos hw) hX0 hY0 fun i hi => by
      rw [hXA ⟨i, hi⟩, hYB ⟨i, hi⟩]
  comp := fun X Y hX hY => by
    obtain ⟨hXc, A, hA, hXA⟩ := hX
    obtain ⟨hYc, B, hB, hYB⟩ := hY
    refine ⟨CFSG.KC.BfsPin.canonK_pcomp hXc hYc, A * B, KernelK426J3.GJ.mul_mem hA hB,
      fun x => ?_⟩
    rw [PF.pg_pcomp (by norm_num) x.2, hYB x, hXA (B x), Equiv.Perm.mul_apply]
  id := by
    refine ⟨(CFSG.KC.BfsPin.PP.id szOK_j3).1, 1, KernelK426J3.GJ.one_mem, fun x => ?_⟩
    rw [PF.pg_pidn (by norm_num) (by norm_num) x.2]
    rfl

theorem mj_of_rep {X : Nat} {A : Equiv.Perm (Fin 6156)} (hc : canonK 6156 13 (mask 13) (6156 * 13) X = true)
    (hA : A ∈ KernelK426J3.GJ) (hr : Rep 6156 (unpack 6156 13 X) A) : MJ X :=
  ⟨hc, A, hA, fun x => by rw [← KernelK426J3.unpackGet x.2]; exact hr x⟩

theorem mj_of_word {wd : List Int} {P : Nat} (hc : canonK 6156 13 (mask 13) (6156 * 13) P = true)
    (h : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 wd P = true) : MJ P := by
  have hS : CFSG.Sporadic.Schreier.j3StrongArrs.size = 5 := PJ3Check.binds.2.2.2.1
  obtain ⟨hw, hl⟩ := wordEqK_sound ⟨hS, PJ3Check.binds.2.2.2.2.1⟩ PJ3Check.perm h
  have hrep := rep_wordA (n := 6156) (j := 5)
    (gs := fun h => permOfArr 6156 CFSG.Sporadic.Schreier.j3StrongArrs[h]!)
    (fun h hh => rep_S J3KT.hd (by omega)) (fun h hh => rep_Si J3KT.hd (by omega)) wd hl
  rw [hw] at hrep
  exact mj_of_rep hc (KernelK426J3.gen_le (Quiver.SchreierGraph.evalWord_mem_closure _ _)) hrep

theorem mj_inv {P R : Nat} (hP : MJ P) (hR : canonK 6156 13 (mask 13) (6156 * 13) R = true)
    (h : invEqK 6156 13 (mask 13) (6156 * 13) P R = true) : MJ R := by
  obtain ⟨hPc, A, hA, hPA⟩ := hP
  have hrep : Rep 6156 (unpack 6156 13 P) A := fun x => by
    rw [KernelK426J3.unpackGet x.2]
    exact hPA x
  exact mj_of_rep hR (KernelK426J3.GJ.inv_mem hA)
    (rep_inv_of_isInvA hrep (invEqK_sound h).2)

end CertificateChecks.KernelJ3Ref

end
