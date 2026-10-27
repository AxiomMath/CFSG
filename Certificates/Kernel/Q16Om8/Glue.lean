module

public import Certificates.Kernel.Q16Om8.Checks
public import Certificates.Kernel.LocalComp.Weyl3185
public import CFSG.Certificates.Kernel.Q16BKSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinNoQ16E4Sound

public section

namespace CertificateChecks.KernelQ16Om8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Q16BK
open CFSG.KC.Misc.ArrEnum CFSG.RankThree.Native CFSG.EvenSmallLie.OmegaEight
open CFSG.Monster.B.Co2 (permOfArr)
open CFSG.CGT.PushingUpLit.SolKNA.R4 (NoQ16 NoQ16.of_injective noQ16_of_sylow_card)

@[expose] noncomputable def gs : Array (Array ℕ) :=
  Array.ofFn (n := 4) fun k => unpack 120 7 (CS.G k)

theorem nums' : CS.ng = 4 ∧ CS.N = 4096 := by
  have h := nums
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem gs_size : gs.size = CS.ng := by rw [nums'.1, gs, Array.size_ofFn]

theorem gs_get : ∀ k < CS.ng, gs[k]! = unpack 120 7 (CS.G k) := fun k hk => by
  rw [nums'.1] at hk
  rw [gs, getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem gs_perm : ∀ k < CS.ng, permB 120 7 (CS.G k) = true := fun k hk => by
  rw [nums'.1] at hk
  exact allN_spec perm k hk

theorem unpack_eq {P Q : ℕ}
    (h : allN 120 (fun i => Nat.beq (pg 7 127 P i) (pg 9 511 Q i)) = true) :
    unpack 120 7 P = unpack 120 9 Q := by
  have m7 : mask 7 = 127 := rfl
  have m9 : mask 9 = 511 := rfl
  unfold unpack
  rw [m7, m9]
  congr 1
  funext i
  exact Nat.eq_of_beq_eq_true (allN_spec h i.val i.isLt)

theorem gen_eq {k : ℕ} (hk : k < 4) : permOfArr 120 (unpack 120 7 (CS.G k)) = gen1 (2 * k) := by
  rw [unpack_eq (allN_spec gens k hk), gen1,
    CertificateChecks.KernelLC.W3185.copy0_gen (j := 2 * k) (by omega)]

theorem q_le : Subgroup.closure (permsA 120 gs) ≤ omega1T := by
  rw [omega1T_eq]
  apply Subgroup.closure_mono
  rintro _ ⟨k, hk, rfl⟩
  have hk4 : k < 4 := by
    have : k < gs.size := hk
    rwa [gs_size, nums'.1] at this
  exact ⟨2 * k, by omega, by
    change gen1 (2 * k) = permOfArr 120 gs[k]!
    rw [gs_get k (by rw [nums'.1]; exact hk4), gen_eq hk4]⟩

theorem psLt : ∀ p ∈ [0, 8, 24], p < 120 := by decide

theorem q16Om1_noQ16 : NoQ16 ↥omega1T := by
  obtain ⟨hcard, hno⟩ := q16BK_sound gs_size gs_get gs_perm CS.ok psLt keys q16
  exact noQ16_of_sylow_card q_le (k := 12) (by rw [hcard, nums'.2]; norm_num) (m := 42525)
    (by decide) (by rw [card_omega1T]; norm_num) hno

theorem q16Om8_noQ16 : NoQ16 ↥omegaT :=
  NoQ16.of_injective omegaRestrictEquiv.toMonoidHom omegaRestrictEquiv.injective q16Om1_noQ16

end CertificateChecks.KernelQ16Om8

end
