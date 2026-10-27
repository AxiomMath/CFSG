
module

public import Certificates.Kernel.Fi23Tw.Fix
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23ThreeCBase
import Certificates.Kernel.Fi23Tw.Twin
import Certificates.Kernel.Fi23Tw.Tg
public import Certificates.Kernel.Fi23Tw.ChkDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Tw

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KD.Fi23K
  CFSG.KC.Fi23R CFSG.KC.Fi23Five CFSG.KC.Fi23Tw CFSG.KD.Fi23Tw CFSG.KD.Fi23Cls
  CertificateChecks.KernelFi23Q CertificateChecks.KernelFi23Cls
  CFSG.HardMathSupport.Dickson.I271.TabFi23 CFSG.KS.Raw.Orb
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (t3)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem pe_low : ∀ e ∈ PE, e % 32768 < 18225 := by decide

theorem first_list (i : ℕ) : ∀ L : List ℕ, List.rec (motive := fun _ => Bool) false
    (fun e _ ih => bIf(Nat.beq (Nat.div (Nat.land e (nat_lit 32767)) (nat_lit 135)) i, true, ih))
      L = true → ∃ e ∈ L, e % 32768 / 135 = i
  | [], h => absurd h (by intro h'; cases h')
  | e :: P, h => by
    dsimp only at h
    rw [bOr_eq, Bool.or_eq_true] at h
    rcases h with h | h
    · refine ⟨e, List.mem_cons_self, ?_⟩
      rw [Nat.beq_eq, low_eq] at h
      exact h
    · obtain ⟨e', he', h'⟩ := first_list i P h
      exact ⟨e', List.mem_cons_of_mem e he', h'⟩

theorem first_spec : ∀ i < 135, ∃ e ∈ PE, e % 32768 / 135 = i := fun i hi =>
  first_list i PE (allN_iff.1 (ch17340first_ok : first = true) i hi)

theorem fixed_pt {a : Fin 31671} (ha : t3 2 • a = a) : ∃ i, ∃ hi : i < 135, a = pt i hi := by
  obtain ⟨i, hi, e⟩ := L2_pos ((fix_iff a).1 ha)
  exact ⟨i, hi, Fin.ext e.symm⟩

theorem twin_pe {a b : Fin 31671} (h : Twin ePt (t3 2) a b) :
    ∃ e ∈ PE, e % 32768 / 135 < 135 ∧ e % 32768 % 135 < 135 ∧
      a.val = L2.getD (e % 32768 / 135) 0 ∧ b.val = L2.getD (e % 32768 % 135) 0 := by
  obtain ⟨i, hi, rfl⟩ := fixed_pt h.1
  obtain ⟨j, hj, rfl⟩ := fixed_pt h.2.1
  obtain ⟨e, he, hm⟩ := (twin_iff_pe hi hj).1 h
  refine ⟨e, he, by omega, by omega, ?_, ?_⟩
  · change L2.getD i 0 = _
    rw [hm]
    congr 1
    omega
  · change L2.getD j 0 = _
    rw [hm]
    congr 1
    omega

theorem pe_twin {e : ℕ} (he : e ∈ PE) :
    Twin ePt (t3 2) (pt (e % 32768 / 135) (by have := pe_low e he; omega))
      (pt (e % 32768 % 135) (by omega)) := by
  have hl := pe_low e he
  have h := (twin_iff_pe (i := e % 32768 / 135) (j := e % 32768 % 135) (by omega) (by omega)).2
    ⟨e, he, by omega⟩
  exact h

theorem pe_spec {e : ℕ} (he : e ∈ PE) :
    e / 32768 % 256 < 135 ∧
      tA G (L2.getD (e % 32768 / 135) 0) (L2.getD (e % 32768 % 135) 0) =
        L2.getD (e / 32768 % 256) 0 ∧
      L2.getD (e / 32768 % 256) 0 ≠ L2.getD (e % 32768 / 135) 0 ∧
      L2.getD (e / 32768 % 256) 0 ≠ L2.getD (e % 32768 % 135) 0 ∧
      e / 2 ^ 23 =
        tA G (L2.getD (e % 32768 / 135) 0) (tA G (L2.getD (e % 32768 % 135) 0) 0) := by
  have h := allL_spec (ch17340pe_ok : pe = true) e he
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact peK_spec h.1

theorem hK1 : ∀ a : Fin 31671, t3 2 • a = a → ∃ b, Twin ePt (t3 2) a b := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := fixed_pt ha
  obtain ⟨e, he, hei⟩ := first_spec i hi
  have h := pe_twin he
  refine ⟨pt (e % 32768 % 135) (by omega), ?_⟩
  have e1 : pt (e % 32768 / 135) (by have := pe_low e he; omega) = pt i hi := by
    unfold pt
    congr 2
  rw [e1] at h
  exact h

theorem third_val (a b : Fin 31671) : (thirdPt a b).val = tA G a.val b.val := by
  unfold thirdPt
  rw [← conjPt_acts a.2 b.val b.2, idx_of_lt _ b.2]

theorem hK2b : ∀ a b, Twin ePt (t3 2) a b → thirdPt a b ≠ a ∧ thirdPt a b ≠ b := by
  intro a b h
  obtain ⟨e, he, -, -, ha, hb⟩ := twin_pe h
  obtain ⟨-, h2, h3, h4, -⟩ := pe_spec he
  refine ⟨fun h' => h3 ?_, fun h' => h4 ?_⟩
  · rw [← h2, ← ha, ← hb, ← third_val, h', ha]
  · rw [← h2, ← ha, ← hb, ← third_val, h', hb]

theorem key_val (a b : Fin 31671) :
    idx 31671 (ePt a * ePt b) 0 = tA G a.val (tA G b.val 0) := by
  unfold ePt
  rw [idx_mul, conjPt_acts b.2 0 (by norm_num),
    conjPt_acts a.2 _ (CertificateChecks.KernelFi23R.tA_lt _ (by norm_num))]

theorem hK2 : ∀ a b a' b', Twin ePt (t3 2) a b → Twin ePt (t3 2) a' b' →
    ePt a' * ePt b' = ePt a * ePt b →
      (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = thirdPt a b) ∨ (a' = thirdPt a b ∧ b' = a) := by
  intro a b a' b' h h' hE
  obtain ⟨e, he, hi, hj, ha, hb⟩ := twin_pe h
  obtain ⟨e', he', hi', hj', ha', hb'⟩ := twin_pe h'
  obtain ⟨hk, h2, -, -, h5⟩ := pe_spec he
  obtain ⟨-, -, -, -, h5'⟩ := pe_spec he'
  have hkey : e / 2 ^ 23 = e' / 2 ^ 23 := by
    rw [h5, h5', ← ha, ← hb, ← ha', ← hb', ← key_val, ← key_val, hE]
  have hrot := rotB_spec (keyK_spec (ch17340key_ok : key = true) e he e' he' hkey)
  have hl := pe_low e he
  have hl' := pe_low e' he'
  have hc : (thirdPt a b).val = L2.getD (e / 32768 % 256) 0 := by
    rw [third_val, ha, hb, h2]
  rcases hrot with h1 | h1 | h1
  · left
    refine ⟨Fin.ext ?_, Fin.ext ?_⟩
    · rw [ha', ha, h1]
    · rw [hb', hb, h1]
  · right
    left
    refine ⟨Fin.ext ?_, Fin.ext ?_⟩
    · rw [ha', hb]
      congr 1
      omega
    · rw [hb', hc]
      congr 1
      omega
  · right
    right
    refine ⟨Fin.ext ?_, Fin.ext ?_⟩
    · rw [ha', hc]
      congr 1
      omega
    · rw [hb', ha]
      congr 1
      omega

end CertificateChecks.KernelFi23Tw

end
