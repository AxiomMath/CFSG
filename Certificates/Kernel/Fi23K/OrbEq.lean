module

public import Certificates.Kernel.Fi23K.Letters
public import CFSG.F3.ConjBFSW
import Certificates.Kernel.Fi23K.Misc
import Certificates.Kernel.Fi23K.Ord
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KD.Fi23K

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KS.Raw.Orb CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native.BfsSpec

theorem ord_pt {k : Nat} (hk : k < 31671) :
    tb G 39 (tb G 39 k) = k ∧ tb G 40 (tb G 40 (tb G 40 k)) = k := by
  have h := allN_iff.1 ord_ok k hk
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem dep_pt {k : Nat} (hk : k < 31671) :
    tb G 93 k < 200 ∧ (k ≠ 0 → tb G 93 k = tb G 93 (tb G 91 k) + 1) := by
  have h := dep_ok
  unfold depK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  have h2 := allN_iff.1 h.2 k hk
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true, bIf_eq] at h2
  refine ⟨by simpa [Nat.blt_eq] using h2.1, fun hk0 => ?_⟩
  have h3 := h2.2
  have hb : k.beq 0 = false := by
    cases e : k.beq 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hk0
  rw [hb, if_neg Bool.false_ne_true] at h3
  exact Nat.eq_of_beq_eq_true h3

theorem orbLit_size : orbLit.keys.size = 31671 := by
  unfold orbLit
  rw [Array.size_ofFn]

theorem orbLit_root : orbLit.keys[0]! = matD := by
  rw [getElem!_pos _ _ (by rw [orbLit_size]; decide)]
  simp only [orbLit, Array.getElem_ofFn]
  rfl

theorem orbitData_eq
    (hA : ∀ k < 31671, conjW 253 matA matA orbLit.keys[k]! = orbLit.keys[ap orbLit.alpha k]!)
    (hB : ∀ k < 31671, conjW 253 matB matBi orbLit.keys[k]! = orbLit.keys[ap orbLit.beta k]!)
    (hinj : ∀ i < 31671, ∀ j < 31671, orbLit.keys[i]! = orbLit.keys[j]! → i = j) :
    orbitData () = orbLit := by
  have hs := orbLit_size
  have hal : ∀ k < orbLit.keys.size, ap orbLit.alpha k = tb G 39 k :=
    fun k hk => ap_tabOf 39 (by omega)
  have hbe : ∀ k < orbLit.keys.size, ap orbLit.beta k = tb G 40 k :=
    fun k hk => ap_tabOf 40 (by omega)
  unfold orbitData
  refine conjBFSW_eq_of (fp := tb G 91) (fl := tb G 92) (dep := tb G 93) (by rw [hs]; decide)
    orbLit_root (by rw [hs]; exact tabOf_size 39) (by rw [hs]; exact tabOf_size 40)
    (by rw [hs]; exact tabOf_size 91) (by rw [hs]; exact tabOf_size 92) hal hbe
    (fun k hk => ap_tabOf 91 (by omega)) (fun k hk => ap_tabOf 92 (by omega))
    (by rw [hs]; exact bfs_ok) (fun k hk => hA k (by omega)) (fun k hk => hB k (by omega))
    (fun k hk => ?_) (fun k hk => ?_) (fun i hi j hj => hinj i (by omega) j (by omega))
    (fun k hk => (dep_pt (by omega)).1)
    (fun k hk0 hk => (dep_pt (by omega)).2 (by omega))
  · have h1 := rng 39 (by decide) k (by omega)
    rw [hal k hk, hal _ (by omega)]
    exact (ord_pt (by omega)).1
  · have h1 := rng 40 (by decide) k (by omega)
    have h2 := rng 40 (by decide) _ h1
    rw [hbe k hk, hbe (tb G 40 k) (by omega), hbe (tb G 40 (tb G 40 k)) (by omega)]
    exact (ord_pt (by omega)).2

end CFSG.KD.Fi23K

end
