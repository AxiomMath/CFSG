module

public import Certificates.Kernel.Sporadic.Fi24Net.G
public import Certificates.Kernel.Sporadic.Fi24Net.W0
public import Certificates.Kernel.Sporadic.Fi24Net.W1
public import Certificates.Kernel.Sporadic.Fi24Net.W2
public import Certificates.Kernel.Sporadic.Fi24Net.W3
public import CFSG.Certificates.Kernel.Spor.Fi24NetSound
public import Certificates.Data.CFSGNative.Fi24.Certificate
import CFSG.Certificates.Kernel.Common.ForallTree
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import Certificates.Data.Kernel.KDense.KeysDistinct
public import Certificates.Data.Kernel.KDense.LetterOK
public import Certificates.Data.Kernel.KDense.Plan
public import Mathlib

public section

namespace CFSG.KD.Fi24Net

open CFSG.KC CFSG.KC.Fi24Net CFSG.KS.Fi24Net CFSG.KS.TW CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Fi24.Native

#kc_forall_tree nAll (fun j => CFSG.KD.Fi24Net.nck j = true) 13 CFSG.KD.Fi24Net.Ck.n
#kc_forall_tree gAll (fun g => CFSG.KD.Fi24Net.gck g = true) 38 CFSG.KD.Fi24Net.Ck.g
#kc_forall_tree wAll (fun g => CFSG.KD.Fi24Net.wck g = true) 209 CFSG.KD.Fi24Net.Ck.w

theorem nck_spec : ∀ j < 13, netOK (NW j) = true := nAll

theorem gck_spec : ∀ g < 38, genOK CFSG.KD.Fi24Orb.OT (NW (g / 19)) (19 * (g / 19)) (g % 19) = true :=
  gAll

theorem WD_eq : ∀ j < 13, WD j = (chainWords ())[j]! := by
  intro j hj
  interval_cases j <;> rfl

theorem wck_spec : ∀ g < 209,
    wordOK NW ((chainWords ())[2 + g / 19]!) (2 + g / 19) (g % 19) = true := by
  intro g hg
  have h := wAll g hg
  have e : WD (2 + g / 19) = (chainWords ())[2 + g / 19]! := WD_eq _ (by omega)
  change wordOK NW (WD (2 + g / 19)) (2 + g / 19) (g % 19) = true at h
  rw [e] at h
  exact h

theorem words_ok : ∀ j < 13, ∀ z ∈ (chainWords ())[j]!, z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3) := by
  decide +kernel

theorem nets {j : Nat} (hj : j < 13) {x : Nat} (hx : x < 306936) :
    pF (NW j) x < 306936 ∧ pR (NW j) x < 306936 ∧ pR (NW j) (pF (NW j) x) = x ∧
      pF (NW j) (pR (NW j) x) = x :=
  nets_facts nck_spec hj hx

theorem letters (O : Enum)
    (hA : ∀ x < 306936, ap O.alpha x = CFSG.KC.Fi24Orb.oA (CFSG.KD.Fi24Orb.OL x))
    (hB : O.beta.size = 306936 ∧ ∀ x < 306936, ap O.beta x = CFSG.KC.Fi24Orb.oB (CFSG.KD.Fi24Orb.OL x)) :
    (chainLetters O).size = 26 ∧ ∀ l < 26, ∀ x < 306936, ap (chainLetters O)[l]! x = LN NW l x := by
  have hab : ∀ x < 306936, pF (NW 0) x = CFSG.KC.Fi24Orb.oA (CFSG.KD.Fi24Orb.OL x) ∧
      pF (NW 1) x = CFSG.KC.Fi24Orb.oB (CFSG.KD.Fi24Orb.OL x) :=
    fun x hx => gens_spec nck_spec gck_spec hx
  have hgen : ∀ z, ∀ x < 306936, ap (genTables O z) x = GN NW z x ∧ GN NW z x < 306936 := by
    intro z x hx
    unfold genTables GN
    by_cases h1 : z = 1 ∨ z = -1
    · rw [if_pos h1, if_pos h1, hA x hx, ← (hab x hx).1]
      exact ⟨rfl, (nets (by decide) hx).1⟩
    by_cases h2 : z = 2
    · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, hB.2 x hx, ← (hab x hx).2]
      exact ⟨rfl, (nets (by decide) hx).1⟩
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
      have hT : TR 306936 O.beta (pF (NW 1)) :=
        ⟨hB.1, fun i hi => ⟨by rw [hB.2 i hi, (hab i hi).2], (nets (by decide) hi).1⟩⟩
      have hI := invT_TR (by decide) hT fun i hi =>
        ⟨(nets (by decide) hi).2.1, (nets (by decide) hi).2.2.2, (nets (by decide) hi).2.2.1⟩
      exact hI.2 x hx
  exact letters_spec (words := chainWords ()) (gens := genTables O) nck_spec wck_spec rfl rfl rfl
    words_ok hgen

end CFSG.KD.Fi24Net

end
