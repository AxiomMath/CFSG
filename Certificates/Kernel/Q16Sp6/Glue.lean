module

public import Certificates.Kernel.Q16Sp6.Checks
public import CFSG.Certificates.Kernel.Q16BKSound
public import CFSG.Sporadic.Schreier.Co3Sp6
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinNoQ16E4Sound

public section

namespace CertificateChecks.KernelQ16Sp6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Q16BK
open CFSG.KC.Misc.ArrEnum CFSG.RankThree.Native CFSG.Sporadic.Schreier.Co3
open CFSG.Monster.B.Co2 (permOfArr)
open CFSG.CGT.PushingUpLit.SolKNA.R4 (NoQ16 noQ16_of_sylow_card)
open CertificateChecks.KernelSpor

theorem hsz : szOK 36 6 = true := by decide

@[expose] noncomputable def gs : Array (Array ℕ) := Array.ofFn (n := 9) fun k => unpack 36 6 (CS.G k)

theorem nums' : CS.ng = 9 ∧ CS.N = 512 := by
  have h := nums
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem gs_size : gs.size = CS.ng := by rw [nums'.1, gs, Array.size_ofFn]

theorem gs_get : ∀ k < CS.ng, gs[k]! = unpack 36 6 (CS.G k) := fun k hk => by
  rw [nums'.1] at hk
  rw [gs, getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem gs_perm : ∀ k < CS.ng, permB 36 6 (CS.G k) = true := fun k hk => by
  rw [nums'.1] at hk
  exact allN_spec perm k hk

theorem S_permB {a : ℕ} (ha : a < 66) : permB 36 6 (Co3Sp36.S a) = true :=
  permB_of_pp (pp_of_permOK hsz (allN_spec Co3Sp36.perm a ha))

theorem S_mem {a : ℕ} (ha : a < 63) : permOfArr 36 (unpack 36 6 (Co3Sp36.S a)) ∈ co3X36 := by
  rw [← Co3Sp36.arr_eq a (by omega)]
  exact co3Sp36Gen_mem a ha

@[expose] noncomputable def wk (wd : List ℕ) (A : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
    (fun l _ ih acc => strictN (pcomp 36 6 (mask 6) acc (Co3Sp36.S l)) ih) wd A

theorem wk_mem : ∀ wd : List ℕ, (∀ a ∈ wd, a < 63) → ∀ A : ℕ, permB 36 6 A = true →
    permOfArr 36 (unpack 36 6 A) ∈ co3X36 →
      permB 36 6 (wk wd A) = true ∧ permOfArr 36 (unpack 36 6 (wk wd A)) ∈ co3X36
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | l :: wd, hl, A, h1, h2 => by
    have hl0 := hl l List.mem_cons_self
    have e : wk (l :: wd) A = wk wd (pcomp 36 6 (mask 6) A (Co3Sp36.S l)) :=
      PF.strictN_eqP _ (wk wd)
    rw [e]
    refine wk_mem wd (fun a ha => hl a (List.mem_cons_of_mem l ha)) _
      (permB_pcomp hsz h1 (S_permB (by omega))) ?_
    rw [permOfArr_pcomp hsz h1 (S_permB (by omega))]
    exact co3X36.mul_mem h2 (S_mem hl0)

theorem words_lt : ∀ k < 9, ∀ a ∈ words.getD k [], a < 63 := by decide

theorem q_le : Subgroup.closure (permsA 36 gs) ≤ co3X36 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk9 : k < 9 := by
    have : k < gs.size := hk
    rwa [gs_size, nums'.1] at this
  have hG : CS.G k = wk (words.getD k []) (pidn 36 6) := Nat.eq_of_beq_eq_true (allN_spec gens k hk9)
  change permOfArr 36 gs[k]! ∈ co3X36
  rw [gs_get k (by rw [nums'.1]; exact hk9), hG]
  have hid : permOfArr 36 (unpack 36 6 (pidn 36 6)) ∈ co3X36 := by
    rw [← idA_eq hsz, permOfArr_eq_of_rep CFSG.Monster.B.Co2.rep_idA]
    exact co3X36.one_mem
  exact (wk_mem _ (words_lt k hk9) _ (permB_of_pp (PP.id hsz)) hid).2

theorem psLt : ∀ p ∈ [4, 0, 2], p < 36 := by decide

theorem q16Sp6_noQ16 :
    NoQ16 ↥co3X36 := by
  obtain ⟨hcard, hno⟩ := q16BK_sound gs_size gs_get gs_perm CS.ok psLt keys q16
  exact noQ16_of_sylow_card q_le (k := 9) (by rw [hcard, nums'.2]; norm_num) (m := 2835)
    (by decide) (by rw [card_co3X36]; norm_num) hno

end CertificateChecks.KernelQ16Sp6

end
