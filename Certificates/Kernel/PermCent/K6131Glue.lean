module

public import Certificates.Kernel.PermCent.K6131F
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import Certificates.Data.Seitz77Sec27L34Ord3
public meta import Certificates.Data.Seitz77Sec27L34Ord3

public section

namespace CFSG.Certificates.Kernel.PkCV.L34O3

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.GH74.KGroups.NativeChecks CFSG.KGroups.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier Certificates.Seitz77Sec27

theorem enumA_ev : enumA QP = (elemsC QP).map (fun c => toA (ev c)) := by
  rw [enumA_eq, elemsT_eq_elemsC, List.map_map]
  rfl

theorem ord3_ev (q : CV 42) : orderIsA 42 (toA (ev q)) 3 = orderIsP q 3 [3] := by
  rw [orderIsA_rep (rep_toA (ev q)) 3, orderIs_ev]
  exact orderIs_eq_orderIsP q (by norm_num) [3]
    (fun p hp hd => by simp [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hd]) (by decide)

theorem com_ev (a b : CV 42) :
    eqA 42 (compA 42 (toA (ev b)) (toA (ev a))) (compA 42 (toA (ev a)) (toA (ev b))) =
      decide (b * a = a * b) := by
  rw [eqA_eq_decide (rep_compA (rep_toA _) (rep_toA _)) (rep_compA (rep_toA _) (rep_toA _)),
    ev_mul', ev_mul', decide_ev_eq]

theorem wC42 : wC 42 = 6 := by decide +kernel

theorem sB (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem o3_eq : o3 = fun q => orderIsP q 3 [3] := by
  funext q
  have h : orderIsP q 3 [3] = (powOneC q 3 && !powOneC q 1) := by
    simp [orderIsP, powOneC_eq]
  rw [h, o3, sB, o3N]
  simp only [powOneC]
  delta img
  simp only [wC42]

theorem hcF_cons (c : Nat) (a : CV 42) (L : List (CV 42)) :
    hcF c (a :: L) = (((elemsC QP).filter fun g => decide (g * a = a * g)).length == c) := by
  rw [hcF, sB]
  congr 3
  funext g
  rw [sB, ← eq22C_eq, eq22C, wC42]

theorem check6131 : l34Ord3Check = true := by
  have hK := k6131
  unfold ord3F at hK
  rw [o3_eq, Bool.and_eq_true] at hK
  obtain ⟨h1, h2⟩ := hK
  have hf : ((fun a => orderIsA 42 a 3) ∘ fun c : CV 42 => toA (ev c)) =
      fun q => orderIsP q 3 [3] := funext ord3_ev
  unfold l34Ord3Check l34Ord3CheckL
  rw [enumA_ev, List.filter_map, hf]
  generalize (elemsC QP).filter (fun q => orderIsP q 3 [3]) = F at h1 h2 ⊢
  cases F with
  | nil => exact absurd h2 (by simp [hcF])
  | cons a rest =>
    rw [hcF_cons] at h2
    simp only [List.length_map, List.map_cons, Bool.and_eq_true, decide_eq_true_eq]
    have hl := beq_iff_eq.mp h1
    refine ⟨by simpa using hl, ?_⟩
    have hc : ((fun g => eqA 42 (compA 42 g (toA (ev a))) (compA 42 (toA (ev a)) g)) ∘
        fun b : CV 42 => toA (ev b)) = fun g => decide (g * a = a * g) :=
      funext fun b => com_ev a b
    unfold centLenA
    rw [List.filter_map, List.length_map, hc]
    exact beq_iff_eq.mp h2

end CFSG.Certificates.Kernel.PkCV.L34O3

end
