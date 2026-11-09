module

public import Certificates.Data.Kernel.M24G.FixOct
public import Certificates.Kernel.M24G.ReplayChunk

public section

namespace CFSG.KC.M24G.FixOctQ

open CFSG.KC.M24G CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

@[expose] def keyQ : List Nat → Nat → Nat
  | [], acc => acc
  | m :: l, acc => keyQ l (Nat.lor (Nat.shiftLeft acc 8) m)

@[expose] def tabKeyQ (t : Array Nat) : Nat := keyQ t.toList 0

theorem foldl_eq_keyQ : ∀ (l : List Nat) (acc : Nat),
    l.foldl (fun acc m => (acc <<< 8) ||| m) acc = keyQ l acc
  | [], _ => rfl
  | _ :: l, _ => foldl_eq_keyQ l _

theorem tabKeyF_eq_Q : tabKeyF = tabKeyQ := by
  funext t
  exact foldl_eq_keyQ t.toList 0

@[expose] def lookP (C v : Nat) : Nat := Nat.land (Nat.shiftRight C (Nat.mul 8 v)) 255

theorem lookP_spec {C : Nat} {c : Array Nat} (hlen : c.toList.length = 24) (hC : C < 2 ^ 192)
    (hsm : ∀ v < 24, lookP C v = c.toList.getD v 0) (v : Nat) : lookP C v = c.toList.getD v 0 := by
  by_cases hv : v < 24
  · exact hsm v hv
  · have h1 : c.toList.getD v 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    have h2 : C >>> (8 * v) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hC (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h1]
    unfold lookP
    change Nat.land (C >>> (8 * v)) 255 = 0
    rw [h2]
    rfl

@[expose] def mulPF (C : Nat) (c x : Array Nat) : Array Nat :=
  bif Nat.beq x.toList.length 24 then (x.toList.map (lookP C)).toArray else mulTabF c x

theorem mulTabF_eq_P {C : Nat} {c : Array Nat} (hC : ∀ v, lookP C v = c.toList.getD v 0) :
    mulTabF c = mulPF C c := by
  funext x
  unfold mulPF
  cases hb : Nat.beq x.toList.length 24
  · rfl
  · have hx : x.toList.length = 24 := Nat.eq_of_beq_eq_true hb
    simp only [Bool.cond_true, mulTabF]
    congr 1
    apply List.ext_getElem
    · simp [hx]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, hC]
      rw [List.getD_eq_getElem?_getD (l := x.toList), List.getElem?_eq_getElem (by simpa using h2)]
      rfl

@[expose] def fixOctC1P : Nat := 418667261709520212593887661288065807247625881070959132931

@[expose] def fixOctC2P : Nat := 418952733889897110025644859524524417797869654985721054466

theorem fixOctStepsF_eq_P :
    fixOctStepsF = [mulPF fixOctC1P Native.fixOctComm1, mulPF fixOctC2P Native.fixOctComm2] := by
  unfold fixOctStepsF
  rw [mulTabF_eq_P (C := fixOctC1P) (lookP_spec (by decide) (by decide) (by decide)),
    mulTabF_eq_P (C := fixOctC2P) (lookP_spec (by decide) (by decide) (by decide))]

end CFSG.KC.M24G.FixOctQ
