module

public import Certificates.Data.Kernel.Fi23Five.Defs
public import Certificates.Kernel.Fi23R.Sound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelFi23Five

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23Five CFSG.KS.Raw.Orb
  CertificateChecks.KernelFi23R

theorem regSl_spec {H G : Nat → Nat} {r : Nat} {w : List Nat} {lo c : Nat}
    (h : regSl H G r w lo c = true) : ∀ x, lo ≤ x → x < lo + c → tb H r x = wa G w x := by
  intro x hx1 hx2
  unfold regSl at h
  have h1 := allN_iff.1 h (x - lo) (by omega)
  rw [strictB_eq] at h1
  have e : Nat.add lo (x - lo) = x := by
    change lo + (x - lo) = x
    omega
  rw [e] at h1
  exact Nat.eq_of_beq_eq_true h1

theorem decB_spec : ∀ (l : List Nat) (b : Nat), decB l b = true →
    l.Pairwise (fun x y => y < x) ∧ ∀ x ∈ l, x < b
  | [], _, _ => ⟨List.Pairwise.nil, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, b, h => by
    have e : decB (x :: l) b = (Nat.blt x b && decB l x) := rfl
    rw [e, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hx : x < b := by simpa [Nat.blt_eq] using h1
    obtain ⟨ih1, ih2⟩ := decB_spec l x h2
    refine ⟨List.Pairwise.cons ih2 ih1, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · exact lt_trans (ih2 y hy) hx

theorem fixK_spec {H : Nat → Nat} {w L : List Nat} (h : fixK H w L = true) :
    (List.range 31671).filter (fun x => Nat.beq (wv H w x) x) = L := by
  unfold fixK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hd, hf, hc⟩ := h
  obtain ⟨hs, hlt⟩ := decB_spec _ _ hd
  have hs1 : L.Pairwise (· < ·) := List.pairwise_reverse.1 hs
  have hs2 : ((List.range 31671).filter (fun x => Nat.beq (wv H w x) x)).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  have hsub : L ⊆ (List.range 31671).filter (fun x => Nat.beq (wv H w x) x) := by
    intro x hx
    rw [List.all_eq_true] at hf
    exact List.mem_filter.2 ⟨List.mem_range.2 (hlt x (List.mem_reverse.2 hx)), hf x hx⟩
  have hlen : ((List.range 31671).filter (fun x => Nat.beq (wv H w x) x)).length = L.length := by
    rw [← List.countP_eq_length_filter, ← cntS_zero]
    exact Nat.eq_of_beq_eq_true hc
  have hp : L.Perm ((List.range 31671).filter (fun x => Nat.beq (wv H w x) x)) :=
    List.Subperm.perm_of_length_le (List.Nodup.subperm (hs1.imp Nat.ne_of_lt) hsub) (by rw [hlen])
  exact hp.symm.eq_of_pairwise' (r := (· ≤ ·)) (hs2.imp le_of_lt) (hs1.imp le_of_lt)

end CertificateChecks.KernelFi23Five

end
